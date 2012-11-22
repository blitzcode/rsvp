
// rsvp | (C) 2012 Tim C. Schroeder | www.blitzcode.net

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <cmath>

#include <vector>
#include <list>
#include <string>
#include <memory>
#include <map>
#include <set>
#include <stack>

#include <sys/sysctl.h>
#include <sys/time.h>
#include <libproc.h> 
#include <mach/mach.h>
#include <mach/mach_vm.h> // for mach_vm_ instead of vm_
#include <pthread.h>
#include <errno.h>
#include <signal.h>
#include <fcntl.h>

#include <OpenGL/gl.h>
#include <OpenGL/glu.h>
#include <GLUT/glut.h>

// Static assert
template <bool> struct StaticAssert;
template<> struct StaticAssert<true> { };
#define STATIC_ASSERT(x) (StaticAssert<(x) != 0>())

// Integer types
typedef char               int8;
typedef short              int16;
typedef int                int32;
typedef long long          int64;
typedef unsigned int       uint;
typedef unsigned char      uchar;
typedef unsigned char      uint8;
typedef unsigned short     uint16;
typedef unsigned int       uint32;
typedef unsigned long long uint64;
void TestTypes()
{
    // Static size checks
    STATIC_ASSERT(sizeof(int8)   == 1);
    STATIC_ASSERT(sizeof(int16)  == 2);
    STATIC_ASSERT(sizeof(int32)  == 4);
    STATIC_ASSERT(sizeof(int64)  == 8);
    STATIC_ASSERT(sizeof(uint8)  == 1);
    STATIC_ASSERT(sizeof(uint16) == 2);
    STATIC_ASSERT(sizeof(uint32) == 4);
    STATIC_ASSERT(sizeof(uint64) == 8);
}

// Global state and constants
pthread_t     g_sampling_thread;
volatile bool g_stop_sampling_thread = false;
volatile bool g_freeze_sampling_thread = false;
uint          g_num_smp_target = 2500; // Per >= 1/2 second
uint          g_num_smp_profile = 8000;
const uint    g_max_fps = 30; // Frame limiter
const uint    g_col_wdh = 485; // For the two column GUI layout
const uint    g_wnd_wdh = g_col_wdh * 2 - 3;
uint          g_wnd_hgt = 678; // Window height is adjustable
float         g_ui_scale = 1.0f;
uint          g_real_wnd_wdh = g_wnd_hgt; // Actual window size, needed for UI scaling
uint          g_real_wnd_hgt = g_wnd_wdh;
uint          g_cur_func_sel = 0; // Current function index selected in the function profile
bool          g_call_tree_incoming = true; // Show incoming or outgoing call tree?
volatile bool g_reset_profile = false; // Trigger a reset of the profile in the HF sampling thread
const char    g_project_url[] = "https://github.com/blitzcode/rsvp";
bool          g_show_call_tree = true; // Show call tree or source view?
// g_font, g_symbol, g_fs_usage, g_source and g_prof_data further down

void FatalExit(const char *error)
{
    // Error exit function

    std::printf("ERROR: %s\n", error);
    std::exit(1);
}

double TimerGetTick()
{
    // High precision timer, return in seconds

    // Make returned tick smaller
    static bool first_call = true;
    static timeval start;
    if (first_call)
    {
        first_call = false;
        gettimeofday(&start, NULL);
    }

    timeval time;
    gettimeofday(&time, NULL);
    return
        double(time.tv_sec - start.tv_sec) +
        double(time.tv_usec - start.tv_usec) / 1000000.0;
}

class Lockable
{
public:
    Lockable()    { if (pthread_mutex_init   (&m_mutex, NULL) != 0) assert(!"Mutex init failed");    }
    ~Lockable()   { if (pthread_mutex_destroy(&m_mutex)       != 0) assert(!"Mutex destroy failed"); }
    void Lock()   { if (pthread_mutex_lock   (&m_mutex)       != 0) assert(!"Mutex lock failed");    }
    void Unlock() { if (pthread_mutex_unlock (&m_mutex)       != 0) assert(!"Mutex unlock failed");  }

protected:
    pthread_mutex_t m_mutex;

};

// Wrapper around atos tool
//
// http://developer.apple.com/library/mac/#documentation/Darwin/Reference/ManPages/man1/atos.1.html
//
// Duplicating the full functionality of this tool would be rather difficult. Its source is not
// available, some of the underlying APIs are poorly documented, plus it does exactly what we need
// and seems reasonably fast and reliable
class ATOS_Pipe
{
public:
    ATOS_Pipe(pid_t pid)
    {
        // Check for atos
        if (std::system("atos 2> /dev/null") != 0)
            FatalExit("Can't find 'atos' command line utility - dev. tools not installed?");

        // TODO: The bi-directional popen() only works with this environment
        //       variable set to avoid a deadlock due to buffering, nasty
        if (setenv("NSUnbufferedIO", "YES", 1) != 0)
            assert(!"setenv failed");

        char buf[64];
        std::snprintf(buf, sizeof(buf), "atos -p %i", pid);
        m_pipe = popen(buf, "r+");
        assert(m_pipe != NULL);
    }

    ~ATOS_Pipe()
    {
        if (m_pipe != NULL)
            if (pclose(m_pipe ) != 0)
                assert(!"pclose() failed");
    }

    void AddressToSymbol(uint64 addr, char *buf, size_t buf_len) const
    {
        // Communicate with atos program for address resolution, needs to have
        // buffering disabled to not deadlock

        // The addresses need to be in hexadecimal, since 10.7 atos only resolves those
        if (std::fprintf(m_pipe, "0x%llx\n", addr) <= 0)
            assert(!"Writing to atos pipe failed");

        if (std::fgets(buf, buf_len, m_pipe) == NULL)
            assert(!"Reading from atos pipe failed");
    }

protected:
    std::FILE *m_pipe;

};

class SymbolManager : private Lockable
{
public:
    SymbolManager(pid_t pid) :
        m_atos(pid),
        m_cache_hit(0),
        m_cache_miss(0),
        m_unresolved_sym_name("(Unresolved)")
    { }

    uint32 AddressToSymbolID(
        uint64 addr,
        uint16 *file_name_id_out = NULL, // Optional source & line information starts here
        uint16 *line_number_out  = NULL)
    {
        // Resolve an address into a symbol ID common to all addresses resolving into that symbol.
        // We return source and line information on the spot. We can't cache them here as they are
        // tied to the address and not the symbol

        Lock();

        // Check address cache
        CacheEntry &cache = m_cache[addr % (sizeof(m_cache) / sizeof(CacheEntry))];
        if (cache.m_pc == addr &&
            cache.m_sym_id != uint32(-1)) // Sometimes we get a null address and a false hit
        {
            m_cache_hit++;
        }
        else
        {
            m_cache_miss++;

            // Obtain symbol string from atos
            char symbol[8192];
            m_atos.AddressToSymbol(addr, symbol, sizeof(symbol));

            // Module and file name / line
            char module[1024];
            char file_name[1024];
            uint line_number;
            ExtractModuleAndFileName(
                symbol,
                module,
                sizeof(module),
                file_name,
                sizeof(file_name),
                &line_number);

            // De-mangle atos output into clean and display friendly symbol name
            PrettyPrintSymbol(symbol);

            // Just convert all hex addresses to a single unresolved token
            if (std::strncmp(symbol, "0x", 2) == 0)
                std::strncpy(symbol, GetUnresolvedSymbolName(), sizeof(symbol));

            // Check if we already have that symbol name in the table
            const uint32 sym_hash = BernsteinHash(symbol) ^ BernsteinHash(module);
            std::map<uint32, uint32>::iterator it_sym = m_hash_to_sym_id.find(sym_hash);
            if (it_sym == m_hash_to_sym_id.end())
            {
                // Add to symbol and module name string table
                uint32 new_id = uint32(m_sym_table.size());
                m_sym_table.push_back(SymbolName());
                m_sym_table.back().m_symbol = std::string(symbol);
                m_sym_table.back().m_module = std::string(module);

                // Hash-to-ID translation entry
                it_sym = m_hash_to_sym_id.insert
                    (std::map<uint32, uint32>::value_type(sym_hash, new_id)).first;
            }

            // Check if we already have that file name in the table
            const uint32 file_hash = BernsteinHash(file_name);
            std::map<uint32, uint16>::iterator it_file = m_hash_to_file_name_id.find(file_hash);
            if (it_file == m_hash_to_file_name_id.end())
            {
                // Add to file name string table
                uint16 new_id = uint16(m_file_name_table.size());
                m_file_name_table.push_back(std::string(file_name));

                // Hash-to-ID translation entry
                it_file = m_hash_to_file_name_id.insert
                    (std::map<uint32, uint16>::value_type(file_hash, new_id)).first;
            }

            // Update cache
            cache.m_pc = addr;
            cache.m_sym_id = (* it_sym).second;
            cache.m_file_name_id = (* it_file).second;
            cache.m_line_number = line_number;
            assert(std::strcmp(symbol,    SymbolIDToName  ((* it_sym ).second)) == 0);
            assert(std::strcmp(module,    SymbolIDToModule((* it_sym ).second)) == 0);
            assert(std::strcmp(file_name, FileIDToName    ((* it_file).second)) == 0);
        }

        // Return results from cache
        if (file_name_id_out != NULL)
            (* file_name_id_out) = cache.m_file_name_id;
        if (line_number_out != NULL)
            (* line_number_out) = cache.m_line_number;
        const uint32 sym_id = cache.m_sym_id;

        Unlock();

        return sym_id;
    }

    const char * SymbolIDToName(uint32 id) const
    {
        assert(id < m_sym_table.size());
        return m_sym_table[id].m_symbol.c_str();
    }

    const char * SymbolIDToModule(uint32 id) const
    {
        assert(id < m_sym_table.size());
        return m_sym_table[id].m_module.c_str();
    }

    const char * FileIDToName(uint16 id) const
    {
        assert(id < m_file_name_table.size());
        return m_file_name_table[id].c_str();
    }

    float GetCacheHitPercentage() const
    {
        return float(m_cache_hit) / float(m_cache_hit + m_cache_miss) * 100.0f;
    }

    const char * GetUnresolvedSymbolName() const { return m_unresolved_sym_name.c_str(); }

protected:
    ATOS_Pipe m_atos;

    // Address -> Symbol ID cache
    uint m_cache_hit;
    uint m_cache_miss;
    struct CacheEntry
    {
        CacheEntry() : m_pc(0), m_sym_id(-1), m_file_name_id(-1), m_line_number(-1) { }
        uint64 m_pc;
        uint32 m_sym_id;
        // Have to store this here instead of the symbol table as they vary by address, not symbol
        uint16 m_file_name_id;
        uint16 m_line_number;
    } m_cache[65536 * 32]; // 32MB

    // Table of unique symbol names and map to translate string hash -> table location
    std::map<uint32, uint32> m_hash_to_sym_id;
    struct SymbolName
    {
        std::string m_symbol;
        std::string m_module;
    };
    std::vector<SymbolName> m_sym_table;

    // Table of unique file names and map to translate string hash -> table location
    std::map<uint32, uint16> m_hash_to_file_name_id;
    std::vector<std::string> m_file_name_table;

    std::string m_unresolved_sym_name;

    uint32 BernsteinHash(const char *str_) const
    {
        // We could use a better hash function, but this seems to be collision
        // free so far

        const uchar *str = reinterpret_cast<const uchar *> (str_);
        uint32 hash = 5381;
        int c;

        while ((c = *str++))
            hash = hash * 33 ^ c;

        return hash;
    }

    void ExtractModuleAndFileName(
        const char *sym,
        char *module,
        size_t module_len,
        char *file,
        size_t file_len,
        uint *line_number) const
    {
        // Extract the module and file / line from a symbol string. Can pass NULL for all out
        // parameters to skip them

        // Initialize with failure defaults in case we abort
        if (module != NULL)
            std::strncpy(module, GetUnresolvedSymbolName(), module_len);
        if (file != NULL)
            std::strncpy(file, GetUnresolvedSymbolName(), file_len);
        if (line_number != NULL)
            (* line_number) = 0;

        // Find module name part
        const char module_token[] = " (in ";
        const char *module_begin = std::strstr(sym, module_token);
        if (module_begin == NULL)
            return; // Not present
        module_begin += std::strlen(module_token);

        // Find end of module name part
        const char *module_end = std::strchr(module_begin, ')');
        if (module_end == NULL)
            return; // Must be terminated by closing brace
        const size_t module_idx = module_end - module_begin;

        // Extract module name
        if (module != NULL)
        {
            std::strncpy(module, module_begin, module_len);
            module[std::min(module_idx, module_len)] = '\0';
        }

        // Find file name part
        const char file_token[] = " (";
        const char *file_begin = std::strstr(module_end, file_token);
        if (file_begin == NULL)
            return; // Not present
        file_begin += std::strlen(file_token);

        // Find end of file name part
        const char *file_end = std::strchr(file_begin, ':');
        if (file_end == NULL)
            return; // Need colon
        const size_t file_idx = file_end - file_begin;

        // Extract file name
        if (file != NULL)
        {
            std::strncpy(file, file_begin, file_len);
            file[std::min(file_idx, file_len)] = '\0';
        }

        // Extract line number
        if (line_number != NULL)
            std::sscanf(file_end + 1, "%i", line_number);
    }

    void PrettyPrintSymbol(char *sym) const
    {
        // Convert the output of atos into a name that is readable and compact. We inevitably throw
        // away some information like template arguments, function overloads and module information
        // etc., it's a trade-off. This function also makes certain assumptions on how atos formats
        // its symbols, will likely need to be tweaked if anything changes

        if (sym[0] == '+' || sym[0] == '-')
        {
            // Objective C. We just cut off the parameter list and everything after the brackets
            while (*sym++ != '\0')
            {
                if (*sym == ']' || *sym == ':')
                {
                    *sym++ = ']';
                    *sym = '\0';
                }
            }
        }
        else
        {
            // Assume C / C++

            // Remove module, source file and offset information
            {
                char *cut = std::strstr(sym, " (in ");
                if (cut != NULL)
                    *cut = '\0';
            }

            // Remove newline
            if (sym[std::strlen(sym) - 1] == '\n')
                sym[std::strlen(sym) - 1] = '\0';

            // Shorten '(anonymous namespace)' to 'anon'
            {
                char *anon = NULL;
                const char search[] = "(anonymous namespace)";
                const size_t len_s = sizeof(search) - 1;
                while ((anon = std::strstr(sym, search)))
                {
                    const char replace[] = "anon";
                    const size_t len_r = sizeof(replace) - 1;
                    std::memcpy(anon, replace, len_r);
                    std::memmove(anon + len_r, anon + len_s, std::strlen(sym + len_s) + 1);
                }
            }

            char *orig_ptr = sym;

            // Compact braces and angle brackets
            int angle_level = 0, brace_level = 0;
            char *angle_start = NULL, *brace_start = NULL;
            while (*sym != '\0')
            {
                // Angle brackets confuse our parser, skip operators which have them
                const char ops[][16] =
                {
                    "operator<<=", "operator <<=", "operator>>=", "operator >>=", // Shift Assign
                    "operator<<",  "operator <<",  "operator>>",  "operator >>",  // Shift
                    "operator<",   "operator <",   "operator>",   "operator >",   // Compare
                    "operator->",  "operator ->"                                  // Dereference
                };
                for (uint i=0; i<sizeof(ops) / sizeof(ops[0]); i++)
                    if (std::strncmp(sym, ops[i], std::strlen(ops[i])) == 0)
                    {
                        sym += std::strlen(ops[i]);
                        break;
                    }

                // Don't bother inside braces, we just remove it all anyway
                if (brace_level == 0)
                {
                    // Increment nesting level and store position of first open angle
                    // bracket so we know where to start deleting
                    if (*sym == '<')
                        if (angle_level++ == 0)
                            angle_start = sym;

                    // Decrement nesting level and replace on encountering final angle bracket
                    if (*sym == '>')
                        if (--angle_level == 0)
                        {
                            std::memmove(angle_start + 1, sym, strlen(sym) + 1); 
                            sym = angle_start + 1;
                        }
                    assert(angle_level >= 0);
                }

                // Don't bother inside angle brackets, we just remove it all anyway
                if (angle_level == 0)
                {
                    // Increment nesting level and store position of first open
                    // brace so we know where to start deleting
                    if (*sym == '(')
                        if (brace_level++ == 0)
                            brace_start = sym;
                    
                    // Decrement nesting level and delete on encountering final brace
                    if (*sym == ')')
                        if (--brace_level == 0)
                        {
                            if (sym - brace_start > 1)
                            {
                                std::memmove(brace_start + 1, sym, strlen(sym) + 1); 
                                sym = brace_start + 1;
                            }
                        }
                    assert(brace_level >= 0);
                }

                sym++;
            }
            assert(angle_level == 0);
            assert(brace_level == 0);

            // Remove leading types and trailing qualifiers
            {
                sym = orig_ptr;

                // Trailing const
                char *const_trail = std::strstr(sym, " const");
                if (const_trail != NULL)
                    *const_trail = '\0';

                // Leading types (return values) are sometimes included in the symbol, remove them
                while (*sym != '\0')
                {
                    // Operator function names have spaces in them, don't throw them
                    // away as leading segments
                    const char ops[][16] = { " operator", ":operator", "$operator" };
                    bool break_outer = false;
                    for (uint i=0; i<sizeof(ops) / sizeof(ops[0]); i++)
                        if (std::strncmp(sym, ops[i], std::strlen(ops[i])) == 0)
                            break_outer = true;
                    if (break_outer)
                        break;

                    // Remove all space separated segments before the last one
                    if (*sym == ' ')
                    {
                        std::memmove(orig_ptr, sym + 1, std::strlen(sym) + 1);
                        sym = orig_ptr;
                        continue;
                    }
                        
                    sym++;
                }
            }
        }
    }
};

std::auto_ptr<SymbolManager> g_symbol;

// Fixed size and stack allocated version of std::stack
template <typename T, size_t N> class FixedStackStack
{
public:
    FixedStackStack() : m_top(0) { }

    const T&  Pop()              { return m_stack[--m_top]; }
    void      Push(const T& top) { assert(m_top != N - 1); m_stack[m_top++] = top; }
    void      Clear()            { m_top = 0; }
    size_t    Size() const       { return m_top; }
    bool      Empty() const      { return m_top == 0; }
    const T * GetStack() const   { return Empty() ? NULL : &m_stack[0]; }

protected:
    T m_stack[N];
    size_t m_top;
};

class CallTree
{
public:
    void MergeCallStack(const uint32 *stack, size_t size, uint hits = 1)
    {
        // Merge the given call stack into our tree

        uint32 cur_node = m_tree.empty() ? uint32(-1) : 0;
        uint32 parent = uint32(-1);

        // Merge all the levels of the call stack
        for (uint level=0; level<size; level++)
        {
            // See if we already got the symbol at the current level
            uint32 last_sibling = uint32(-1);
            while (cur_node != uint32(-1))
            {
                if (m_tree[cur_node].m_sym_id == stack[level])
                    break; // Found it
                last_sibling = cur_node;
                cur_node = m_tree[cur_node].m_sibling; // Next
            }

            // We either found a match or we're at the end of the sibling list
            if (cur_node != uint32(-1))
            {
                // Found it, just increment the hit count
                m_tree[cur_node].m_hits += hits;
                parent = cur_node;
                cur_node = m_tree[cur_node].m_child;
            }
            else
            {
                // At the end, add new node
                {
                    Node new_node;
                    new_node.m_sym_id = stack[level];
                    new_node.m_hits = hits;
                    m_tree.push_back(new_node);
                }
                const uint32 new_node = uint32(m_tree.size() - 1);

                if (last_sibling == uint32(-1)) 
                {
                    // No siblings, link with parent
                    if (parent != uint32(-1))
                       m_tree[parent].m_child = new_node;
                }
                else
                {
                    // Link up with the last sibling
                    m_tree[last_sibling].m_sibling = new_node;
                }

                parent = new_node;
                cur_node = uint32(-1);
            }
        }
    }

    void MergeCallTree(const CallTree& merge)
    {
        // Merge the given tree into this one
        //
        // TODO: This function is basically a combination of MergeCallStack() and the traversal
        //       from DebugPrint(). Can we maybe refactor all three functions to share code?

        if (merge.m_tree.empty())
            return;
        if (m_tree.empty())
        {
            (* this) = merge;
            return;
        }

        // Merging trees is tricky, some sanity checks before and after
#ifdef DEBUG_MERGE_CALL_TREE
        const uint dbg_count_1 = merge.DebugPrint(true);
        const uint dbg_count_2 = DebugPrint(true);
        assert(merge.DebugHasDuplicates() == false);
        assert(DebugHasDuplicates() == false);
#endif // DEBUG_MERGE_CALL_TREE

        // Merging tree_1 into tree_2
        const std::vector<Node>& tree_1 = merge.m_tree;
        std::vector<Node>& tree_2 = m_tree;

        FixedStackStack<uint32, 512> stack_1, stack_2;
        stack_1.Push(0);
        stack_2.Push(0);
        uint32 cur_node_1, cur_node_2;

        // Traverse the merge tree
        while (stack_1.Empty() == false)
        {
            cur_node_1 = stack_1.Pop();
            cur_node_2 = stack_2.Pop();

            // We basically go down tree_1, then right, and then work our way
            // back up through the outer loop
            uint32 parent = uint32(-1);
            while (cur_node_1 != uint32(-1))
            {
                // See if we already got the symbol from tree_1 one the same level in tree_2
                // TODO: This is O(n^2) in the worst case (seems fine in practice, though)
                uint32 first_sibling = cur_node_2;
                uint32 last_sibling = uint32(-1);
                while (cur_node_2 != uint32(-1))
                {
                    if (tree_2[cur_node_2].m_sym_id == tree_1[cur_node_1].m_sym_id)
                        break; // Found it
                    last_sibling = cur_node_2;
                    cur_node_2 = tree_2[cur_node_2].m_sibling; // Next
                }

                // We either found a match or we're at the end of the sibling list
                if (cur_node_2 != uint32(-1))
                {
                    // Found it, just add up the counts from both trees
                    tree_2[cur_node_2].m_hits += tree_1[cur_node_1].m_hits;
                    parent = cur_node_2; // In case we have children in tree_1 and descent
                }
                else
                {
                    // At the end, add new node to tree_2
                    {
                        // Just copy from tree_1
                        Node new_node;
                        new_node.m_sym_id = tree_1[cur_node_1].m_sym_id;
                        new_node.m_hits   = tree_1[cur_node_1].m_hits;
                        tree_2.push_back(new_node);
                    }
                    const uint32 new_node = uint32(tree_2.size() - 1);

                    if (last_sibling == uint32(-1)) 
                    {
                        // No siblings, link with parent. We know there always is a
                        // parent since we don't merge empty trees
                        tree_2[parent].m_child = new_node;
                        first_sibling = new_node; // What we push on the stack if we descent
                    }
                    else
                        tree_2[last_sibling].m_sibling = new_node; // Link with last sibling

                    cur_node_2 = new_node;
                    parent = new_node;
                }

                // Traverse tree_1 depth first
                if (tree_1[cur_node_1].m_child != uint32(-1))
                {
                    // Continue with the next sibling once we go back up
                    stack_1.Push(tree_1[cur_node_1].m_sibling);

                    // We need to search for a match from tree_1 at the first sibling
                    stack_2.Push(first_sibling);

                    // Go down both trees
                    cur_node_1 = tree_1[cur_node_1].m_child;
                    cur_node_2 = tree_2[cur_node_2].m_child;
                }
                else
                {
                    cur_node_1 = tree_1[cur_node_1].m_sibling; // Can't go deeper, go right
                    cur_node_2 = first_sibling;                // Start again at first sibling
                }
            }
        }

#ifdef DEBUG_MERGE_CALL_TREE
        assert(DebugPrint(true) == dbg_count_1 + dbg_count_2);
        assert(DebugHasDuplicates() == false);
#endif // DEBUG_MERGE_CALL_TREE
    }

    void SortSiblingLists()
    {
        // Sort all sibling lists by their m_hits member in descending order

        // Enumerate all sibling lists
        std::vector<uint32> first_siblings;
        GetAllNonZeroSiblingLists(first_siblings);

        // Sort
        for (std::vector<uint32>::const_iterator it=first_siblings.begin();
             it!=first_siblings.end();
             it++)
        {
            uint32 cur_node;

            // Create vector of nodes
            std::vector<Node> nodes;
            cur_node = (* it);
            do
            {
                nodes.push_back(m_tree[cur_node]);
                cur_node = m_tree[cur_node].m_sibling;
            } while (cur_node != uint32(-1));

            // Sort copy
            std::sort(nodes.begin(), nodes.end());

            // Write the sorted vector back into the node slots
            cur_node = (* it);
            for (std::vector<Node>::const_iterator it=nodes.begin();
                 it!=nodes.end();
                 it++)
            {
                assert(cur_node != uint32(-1));
                const uint32 next_node = m_tree[cur_node].m_sibling;
                m_tree[cur_node] = (* it);
                m_tree[cur_node].m_sibling = next_node;
                cur_node = next_node;
            }
        }
    }

    void ExtractOutgoingCallArcs(
        uint32 symbol_id,
        uint32 root_symbol_id,
        CallTree *outgoing) const
    {
        // Search this incoming tree tree for call arcs from symbol_id and merge them into outgoing.
        // We need the root symbol of the incoming tree as it is not stored in the tree itself.
        // Pretty straightforward, except for the bit ensuring that we only take the longest part of
        // an arc in the case of cycles
        //
        // TODO: Maybe write some tests to make sure this really works completely as intended...

        if (m_tree.empty())
            return;

        FixedStackStack<uint32, 512> st;
        st.Push(0);
        uint32 cur_node;
        bool arc_already_merged = true;
        bool seen_root = false;
        while (st.Empty() == false)
        {
            cur_node = st.Pop();

            // Found the symbol we're looking for?
            if (m_tree[cur_node].m_sym_id == symbol_id && arc_already_merged == false)
            {
                // Flip our arc and add the root symbol at the end
                uint32 arc[512];
                for (uint i=0; i<st.Size(); i++)
                    arc[i] = m_tree[st.GetStack()[st.Size() - (i + 1)]].m_sym_id;
                arc[st.Size()] = root_symbol_id;

                // Merge into the outgoing graph for symbol_id
                // TODO: We merge the arc with only one hit count for all levels. This should allow
                //       us to reconstruct the first-level times for the outgoing call tree, but we
                //       could do better
                outgoing->MergeCallStack(arc, st.Size() + 1, m_tree[cur_node].m_hits);

                // Only add the longest sequence on the arc, meaning for recursion / cycles
                // we only use the bottom one
                arc_already_merged = true;
            }

            // Little hack so we keep the actual path on the stack instead of the next siblings
            if (cur_node == 0 && seen_root == false)
                seen_root = true;
            else
                cur_node = m_tree[cur_node].m_sibling;

            // Depth-first
            while (cur_node != uint32(-1))
            {
                if (m_tree[cur_node].m_sym_id == symbol_id)
                {
                    // We're about to push a new instance of the arc start symbol onto the stack,
                    // meaning we're on a new arc again and should stop ignoring its occurrence
                    arc_already_merged = false;
                }

                // Go deeper, go right in the outer loop if there's no child
                st.Push(cur_node);
                cur_node = m_tree[cur_node].m_child;
            }
        }
    }

    uint DebugPrint(bool silent) const
    {
        // Traverse the tree depth-first and print it to stdout. Also check for
        // orphaned nodes and return the sum of the hit count of all nodes

        if (m_tree.empty())
            return 0;

        std::stack<uint32> st;
        st.push(0);
        uint32 cur_node;
        uint num_nodes_printed = 0;
        uint total_count = 0;
        while (st.empty() == false)
        {
            cur_node = st.top();
            st.pop();
            while (cur_node != uint32(-1))
            {
                num_nodes_printed++;
                total_count += m_tree[cur_node].m_hits;
                if (silent == false)
                {
                    for (uint i=0; i<st.size() + 1; i++)
                        std::printf(" ");
                    std::printf("%s : %i\n", g_symbol->SymbolIDToName(
                        m_tree[cur_node].m_sym_id), m_tree[cur_node].m_hits);
                }
                if (m_tree[cur_node].m_child != uint32(-1))
                {
                    st.push(m_tree[cur_node].m_sibling);
                    cur_node = m_tree[cur_node].m_child;
                }
                else
                    cur_node = m_tree[cur_node].m_sibling;
            }
        }
        if (silent == false)
            std::printf("\n");

        assert(num_nodes_printed == m_tree.size()); // Did we get everything, no orphaned nodes?

        return total_count;
    }

    bool DebugHasDuplicates() const
    {
        // Return true if we have duplicate siblings at any level

        std::vector<uint32> first_siblings;
        GetAllNonZeroSiblingLists(first_siblings);

        for (std::vector<uint32>::const_iterator it=first_siblings.begin();
             it!=first_siblings.end();
             it++)
        {
            uint32 cur_node_1 = (* it);
            while (cur_node_1 != uint32(-1))
            {
                uint duplicates = 0;

                uint32 cur_node_2 = (* it);
                while (cur_node_2 != uint32(-1))
                {
                    if (m_tree[cur_node_1].m_sym_id == m_tree[cur_node_2].m_sym_id)
                        duplicates++;
                    cur_node_2 = m_tree[cur_node_2].m_sibling;
                }

                assert(duplicates > 0);
                if (duplicates > 1)
                    return true;

                cur_node_1 = m_tree[cur_node_1].m_sibling;
            }
        }

        return false;
    }

    void DebugSerializeToDisk(const char *file_name) const
    {
        std::FILE *file = std::fopen(file_name, "wb");
        size_t size = m_tree.size();
        std::fwrite(&size, sizeof(size_t), 1, file); 
        std::fwrite(&m_tree[0], sizeof(Node), size,file); 
        std::fclose(file);
    }

    void DebugSerializeFromDisk(const char *file_name)
    {
        std::FILE *file = std::fopen(file_name, "rb");
        size_t size;
        std::fread(&size, sizeof(size_t), 1, file); 
        m_tree.resize(size);
        std::fread(&m_tree[0], sizeof(Node), size,file); 
        std::fclose(file);
    }

    struct Node
    {
        Node() : m_sibling(-1), m_child(-1), m_sym_id(-1), m_hits(1) { }

        uint32 m_sibling;
        uint32 m_child;
        uint32 m_sym_id;
        uint32 m_hits;

        // Sort by hit count
        bool operator < (const Node& rhs) const
        {
            return rhs.m_hits < m_hits;
        }
    };

    const Node * GetRoot() const { return m_tree.empty() ? NULL : &m_tree[0]; }

protected:
    std::vector<Node> m_tree;

    void GetAllNonZeroSiblingLists(std::vector<uint32>& first_siblings) const
    {
        if (m_tree.empty())
            return;

        // Enumerate all sibling lists
        first_siblings.push_back(0);
        for (std::vector<Node>::const_iterator it=m_tree.begin(); it!=m_tree.end(); it++)
            if ((* it).m_child != uint32(-1))
                if (m_tree[(* it).m_child].m_sibling != uint32(-1)) // Skip size one lists
                    first_siblings.push_back((* it).m_child);
    }
};

// Helper for handling symbol ID -> symbol sampling statistics maps and their merging
struct SymSampleStats
{
    SymSampleStats() : m_hits(0), m_stack_capture_failures(0) { }

    SymSampleStats& operator += (const SymSampleStats& rhs) 
    {
        // Add hits & call stack capture failures, merge call tree
        m_hits += rhs.m_hits;
        m_stack_capture_failures += rhs.m_stack_capture_failures;
        assert(m_stack_capture_failures <= m_hits);
        m_incoming.MergeCallTree(rhs.m_incoming);

        // Merge source & line hits
        for (std::map<SourceLocation, uint>:: const_iterator it=rhs.m_source_hits.begin();
             it!=rhs.m_source_hits.end();
             it++)
        {
            std::map<SourceLocation, uint>::iterator it_source_hit =
                m_source_hits.find((* it).first);
            if (it_source_hit == m_source_hits.end())
                m_source_hits.insert((* it));
            else
                (* it_source_hit).second += (* it).second;
        }

        return (* this);
    }

    // Hits, stack / tree statistics
    uint m_hits;
    uint m_stack_capture_failures;
    CallTree m_incoming;

    // Source file & line -> hit count statistics
    struct SourceLocation
    {
        SourceLocation() :
            m_file_name_id(-1),
            m_line_number(-1)
        { }
        SourceLocation(uint16 file_name_id, uint16 line_number) :
            m_file_name_id(file_name_id),
            m_line_number(line_number)
        { }

        bool operator < (const SourceLocation& rhs) const
        {
            // Sort first by file and then by source line top to bottom
            if (m_file_name_id == rhs.m_file_name_id)
                return m_line_number < rhs.m_line_number;
            else
                return m_file_name_id < rhs.m_file_name_id;
        }

        uint16 m_file_name_id;
        uint16 m_line_number;
    };
    std::map<SourceLocation, uint> m_source_hits;
};

typedef std::map<uint32, SymSampleStats> SymbolMap;

void MergeSymbolIntoMap(const SymbolMap::value_type& symbol, SymbolMap& symbol_map)
{
    SymbolMap::iterator it = symbol_map.find(symbol.first);
    if (it == symbol_map.end())
        symbol_map.insert(symbol); // New symbol?
    else
        (* it).second += symbol.second; // Merge
}

void MergeSymbolIntoMap(
    uint sym_id,
    uint hits,
    const uint32 *stack,
    size_t stack_size,
    uint16 file_name_id,
    uint16 line_number,
    SymbolMap& symbol_map)
{
    SymbolMap::iterator it = symbol_map.find(sym_id);

    // New symbol?
    if (it == symbol_map.end())
        it = symbol_map.insert(SymbolMap::value_type(sym_id, SymSampleStats())).first;

    // Add hits & call stack capture failures, merge call stack into tree
    (* it).second.m_hits += hits;
    // TODO: This will give capture failure false positives for true entry-point functions
    (* it).second.m_stack_capture_failures += (stack_size == 0); // No stack?
    (* it).second.m_incoming.MergeCallStack(stack, stack_size);

    // Merge source and line information
    SymSampleStats::SourceLocation source_hit(file_name_id, line_number);
    std::map<SymSampleStats::SourceLocation, uint>::iterator it_source_hit =
        (* it).second.m_source_hits.find(source_hit);
    if (it_source_hit == (* it).second.m_source_hits.end())
    {
        (* it).second.m_source_hits.insert(
            std::map<SymSampleStats::SourceLocation, uint>::value_type(source_hit, 1));
    }
    else
        (* it_source_hit).second++;
}

// Profiler results created by the profiler threads and picked up by the rendering code
struct ProfileData : public Lockable
{
    ProfileData() :
        m_pid(0),
        m_x64(false),
        m_phys_ram(0),
        m_num_cpus(0),
        m_resident_memory(0),
        m_live_threads_user_time(0.0),
        m_live_threads_system_time(0.0),
        m_prof_cpu(0.0f),
        m_iops(0),
        m_bytes_read_sec(0),
        m_bytes_written_sec(0),
        m_fs_usage_running(true),
        m_num_smp_collected(0),
        m_num_smp_collected_total(0),
        m_samples_unresolved(0),
        m_smp_collection_interval(0.0)
    {
        std::memset(&m_tei, 0, sizeof(task_events_info));
    }

    // Those will be initialized by the main thread before the profiling begins
    //
    // TODO: Maybe move this somewhere else? Not really profile results, just some constant
    //       target and system information
    pid_t       m_pid;
    std::string m_executable_path;
    std::string m_prof_exe_name;
    bool        m_x64;
    uint64      m_phys_ram;
    uint        m_num_cpus;

    // Memory profiling
    uint64 m_resident_memory;
    std::vector<uint64> m_res_mem_hist;

    // Data for the thread display
    struct Thread
    {
        std::string m_run_state;
        float       m_cpu_usage_percentage;
        float       m_cpu_usage_percentage_slow_update; // Slowly updated for GUI reasons
        std::string m_cur_symbol;
        bool        m_swapped_out;

        // Sort threads in descending order of their CPU usage
        bool operator < (const Thread& rhs) const
        {
            // Use the slow version to avoid constant reshuffling of the thread display
            return rhs.m_cpu_usage_percentage_slow_update < m_cpu_usage_percentage_slow_update;
        }
    };
    std::vector<Thread> m_threads;
    double m_live_threads_user_time;
    double m_live_threads_system_time;

    // Event info structure from the target task, but only containing events
    // from the last second (roughly)
    //
    // TODO: Maybe keep this free from Mach kernel data types?
    task_events_info m_tei;

    // Unnormalized CPU usage percentage for the profiler itself
    float m_prof_cpu;

    // I/O profiling data
    uint m_iops;
    uint m_bytes_read_sec;
    uint m_bytes_written_sec;
    bool m_fs_usage_running;
    std::vector<uint64> m_combined_bytes_sec_hist;

    // Function level profile
    uint   m_num_smp_collected;       // Samples collected in the last interval
    uint   m_num_smp_collected_total; // Total amount of samples in m_functions
    uint   m_samples_unresolved;      // Amount of unresolved samples in m_functions
    double m_oldest_sample_used;      // Age of oldest sample used in function list
    double m_smp_collection_interval; // Duration of last collection interval
    struct Function : public SymSampleStats
    {
        uint32 m_sym_id;

        // Sort in descending order hit count
        bool operator < (const Function& rhs) const
        {
            return rhs.m_hits < SymSampleStats::m_hits;
        }
    };
    std::vector<Function> m_functions;

    // Symbols supposed to be merged into their parents
    //
    // TODO: The only reason this is here is because it is shared between GUI /  data collection
    //       and we need the ability to lock it
    std::set<uint32> m_merge_sym;

} g_prof_data;

bool GetPCFP(thread_act_t thread, uint64 *pc_out, uint64 *fp_out)
{
    // Get the program counter (PC) and frame pointer (FP) for the given thread

    if (g_prof_data.m_x64)
    {
        x86_thread_state64_t x86ts64;
        mach_msg_type_number_t thread_state_count64 = x86_THREAD_STATE64_COUNT;
        if (thread_get_state(thread,
                             x86_THREAD_STATE64,
                             (thread_state_t) &x86ts64,
                             &thread_state_count64) != KERN_SUCCESS)
        {
            return false;
        }

        if (pc_out != NULL) (* pc_out) = x86ts64.__rip;
        if (fp_out != NULL) (* fp_out) = x86ts64.__rbp;
    }
    else
    {
        x86_thread_state32_t x86ts32;
        mach_msg_type_number_t thread_state_count32 = x86_THREAD_STATE32_COUNT;
        if (thread_get_state(thread,
                             x86_THREAD_STATE32,
                             (thread_state_t) &x86ts32,
                             &thread_state_count32) != KERN_SUCCESS)
        {
            return false;
        }

        if (pc_out != NULL) (* pc_out) = x86ts32.__eip;
        if (fp_out != NULL) (* fp_out) = x86ts32.__ebp;
    }

    return true;
}

uint GetHostPageSize()
{
    vm_size_t page_size;
    if (host_page_size(mach_host_self(), &page_size) != KERN_SUCCESS)
        assert(!"Can't obtain host page size");
    return page_size;
}

void DeallocateThreadList(
    thread_act_port_array_t thread_list,
    mach_msg_type_number_t thread_count)
{
    for (uint i=0; i<thread_count; i++)
        if (mach_port_deallocate(mach_task_self(), thread_list[i]) != KERN_SUCCESS)
            assert(!"Error while deallocating thread port");

    if (vm_deallocate(mach_task_self(),
                      (vm_offset_t) thread_list,
                      sizeof(* thread_list) * thread_count) != KERN_SUCCESS)
    {
        assert(!"Error while deallocating thread list");
    }
}

// A cache of memory pages mapped from the target's address space into ours. Allows fast
// reads without the overhead of vm_read_overwrite()
//
// TODO: Sometimes the data we read from the mapped pages differs from what we get from
//       mach_vm_read_overwrite(). In those cases it seems the directly read data is corrupted. This
//       should work, as it is the exact same memory and the thread is suspended. Even suspending
//       the task doesn't help. The code inside #if DBG_PAGE_CACHE compares the two methods and tries
//       to print as much useful information as possible. Sometimes retrying the
//       mach_vm_read_overwrite() brings things in sync. With certain 32 bit processes this code
//       even crashes. Checking the memory region with mach_vm_region() for validity seems to
//       prevent that, but that call basically takes as much time as the entire read, defeating the
//       purpose of this system. It's not clear why a mapped memory region with read permissions
//       would ever cause a segfault, or why any of the read discrepancies occur
class TargetPageCache
{
public:
    TargetPageCache() : m_cache_hit(0), m_cache_miss(0)
    {
        m_page_size = GetHostPageSize();
    }

    bool Read(mach_port_name_t task_port, uint64 addr, size_t size, void *out)
    {
        // Find the starting address of the page containing the requested memory region
        const uint64 addr_page_start = addr & (~(uint64(m_page_size) - 1));
        if (addr + size > addr_page_start + m_page_size)
        {
            // TODO: Stack frame crossing page boundary
            return false;
        }

        // Find cache entry (TODO: Clearly optimized for 4K pages, use log2(page_size) instead)
        PageEntry& entry =
            m_cache[(addr_page_start >> 12) % uint64(sizeof(m_cache) / sizeof(PageEntry))];

        if (entry.m_src != addr_page_start)
        {
            // Cache miss
            m_cache_miss++;

            // Deallocate previous mapping
            if (entry.m_dst != NULL)
            {
                if (mach_vm_deallocate(mach_task_self(),
                                       (mach_vm_address_t) entry.m_dst,
                                       1) != KERN_SUCCESS)
                {
                    assert(!"vm_deallocate() failed");
                }
            }
            entry.m_dst = NULL;

            // Map the page
            vm_prot_t cur_protection, max_protection;
            mach_vm_address_t target_addr = 0;
            if (mach_vm_remap(mach_task_self(), // Target_task
                              &target_addr,     // Target_address
                              m_page_size,      // Size
                              0,                // Mask
                              TRUE,             // Anywhere
                              task_port,        // Source_task
                              addr_page_start,  // Source_address
                              FALSE,            // Copy
                              &cur_protection,  // Cur_protection
                              &max_protection,  // Max_protection
                              VM_INHERIT_NONE)  // Inheritance
                              != KERN_SUCCESS)
            {
                entry.m_src = uint64(-1);
                return false;
            }
            assert(target_addr % uint64(m_page_size) == 0);
            assert(cur_protection & VM_PROT_READ);

            // Update cache
            entry.m_src = addr_page_start;
            entry.m_dst = reinterpret_cast<char *> (target_addr);
        }
        else
            m_cache_hit++;

#if DBG_PAGE_CACHE
        mach_vm_size_t inout_size = size;
        if (mach_vm_read_overwrite(task_port,
                                   addr,
                                   size,
                                   (mach_vm_address_t) out,
                                   &inout_size) != KERN_SUCCESS)
        {
            std::printf("vm_read_overwrite() Failed\n");
        }
        assert(inout_size == size);
        if (std::memcmp(out, entry.m_dst + (addr - addr_page_start), size) != 0)
        {
            static uint cnt = 0;
            cnt++;
            vm_region_basic_info_64 region_info;
            mach_msg_type_number_t info_count = VM_REGION_BASIC_INFO_COUNT_64;
            mach_vm_size_t region_size = 0;
            mach_vm_address_t region_addr = (mach_vm_address_t) entry.m_dst;
            memory_object_name_t object_name;
            if (mach_vm_region(mach_task_self(),
                               &region_addr,
                               &region_size,
                               VM_REGION_BASIC_INFO_64,
                               (vm_region_info_t) &region_info,
                               &info_count,
                               &object_name) != KERN_SUCCESS)
            {
                std::printf("mach_vm_region() failed\n");
            }
            std::printf("\nvm_read_overwrite() / vm_remap() mismatch\n");
            std::printf(
                "addr: %llu addr_page_start: %llu size: %i, addr %% m_page_size: %llu, cnt: %i\n",
                addr, addr_page_start, int(size), addr % uint64(m_page_size), cnt);
            std::printf(
                "region_basic_info - protection: %i max_protection: %i inheritance: %i shared: %i "
                "reserved: %i offset: %llu behavior:%i wired: %i\n",
                region_info.protection,
                region_info.max_protection,
                region_info.inheritance,
                region_info.shared,
                region_info.reserved,
                region_info.offset,
                region_info.behavior,
                region_info.user_wired_count);
            std::printf("vm_read_overwrite(): next: %llu ret: %llu\n",
                ((uint64 *) out)[0],
                ((uint64 *) out)[1]);
            std::printf("vm_remap():          next: %llu ret: %llu\n",
                ((uint64 *) (entry.m_dst + (addr - addr_page_start)))[0],
                ((uint64 *) (entry.m_dst + (addr - addr_page_start)))[1]);
            std::printf("vm_read_overwrite(): ret: %s\n",
                g_symbol->SymbolIDToName(g_symbol->AddressToSymbolID(((uint64 *) out)[1])));
            std::printf("vm_remap():          ret: %s\n",
                g_symbol->SymbolIDToName(g_symbol->AddressToSymbolID
                    (((uint64 *)(entry.m_dst + (addr - addr_page_start)))[1])));
            if (mach_vm_read_overwrite(task_port,
                                       addr,
                                       size,
                                       (mach_vm_address_t) out,
                                       &inout_size) != KERN_SUCCESS)
            {
                std::printf("vm_read_overwrite() Failed\n");
            }
            if (std::memcmp(out, entry.m_dst + (addr - addr_page_start), size) != 0)
                std::printf("Retry did not help\n\n");
            else
                std::printf("Retry did help\n\n");
        }
#endif // DBG_PAGE_CACHE

        // Copy the memory region out of the mapped page into the provided/ buffer
        std::memcpy(out, entry.m_dst + (addr - addr_page_start), size);

        return true;
    }

    float GetCacheHitPercentage() const
    {
        return float(m_cache_hit) / float(m_cache_hit + m_cache_miss) * 100.0f;
    }

protected:
    uint m_page_size;
    uint m_cache_hit;
    uint m_cache_miss;

    struct PageEntry
    {
        PageEntry() : m_src(-1ull), m_dst(NULL) { }
        ~PageEntry()
        {
            if (m_dst != NULL)
                if (vm_deallocate(mach_task_self(), (vm_address_t) m_dst, 1) != KERN_SUCCESS)
                    assert(!"vm_deallocate() failed");
        }

        uint64 m_src;
        char *m_dst;
    };
    PageEntry m_cache[1024]; // Seems to be enough for >= 98% hit rate in all test cases

} g_target_page_cache;

template<typename PTR> void CaptureCallStack(
    mach_port_name_t task_port,
    PTR fp,
    uint32 *stack_symbols_out,
    size_t *stack_size_in_out)
{
    // Traverse the target's call stack. We use a pretty basic method here
    // utilizing frame pointers. It's fast and conceptually simple, but comes
    // with inherent limitations and doesn't work with the default code
    // generation parameters of many modern compilers (e.g. -fomit-frame-pointer).
    //
    // Some overview material and other implementations:
    //
    // http://www.acsu.buffalo.edu/~charngda/backtrace.html
    // http://www.yosefk.com/blog/getting-the-call-stack-without-a-frame-pointer.html
    // https://bitbucket.org/edd/dbg/src/1abb9939664c/src/osx/frames.cpp?at=default
    // http://opensource.apple.com/source/gdb/gdb-956/src/gdb/macosx/macosx-self-backtrace.c
    //
    // Debuggers generally use special debug information or fall back on
    // function prologue analysis. It's slower and vastly more complicated, but
    // more reliable and doesn't require programs to be compiled with frame
    // pointers explicitly enabled. Consider this as a possible future
    // extension.
    //
    // Some information and source code regarding CFI:
    //
    // http://gnu.wildebeest.org/blog/mjw/2007/08/23/stack-unwinding/
    // http://code.google.com/p/google-breakpad/source/browse/trunk/src/common/dwarf/cfi_assembler.h
    // http://www.nongnu.org/libunwind/

    // Templatized so we can read 32 and 64 bit stack frames
    struct StackFrame
    {
        PTR next;
        PTR ret;
    };

#ifndef USE_PAGE_CACHE
    // No TargetPageCache, use a simple buffer with some read-ahead to avoid a few Mach calls
    char stack_buf[256];
    uint64 stack_buf_addr = uint64(-1);
#endif // USE_PAGE_CACHE

    PTR frame = fp;
    uint i;
    for (i=0; i<(* stack_size_in_out); i++)
    {
        // Sanity checks on FP
        if (frame < 16)                 // Near zero
            break;
        if ((frame % sizeof(PTR)) != 0) // Not properly aligned
            break;

        StackFrame frame_struct;
#ifdef USE_PAGE_CACHE
        if (g_target_page_cache.Read(task_port, frame, sizeof(StackFrame), &frame_struct) == false)
            break; // Can't read from FP address
#else
        if (frame < stack_buf_addr ||
            frame > stack_buf_addr + sizeof(stack_buf) - sizeof(StackFrame))
        {
            // Outside our buffer
            mach_vm_size_t inout_size = sizeof(StackFrame);
            if (mach_vm_read_overwrite(
                task_port,
                frame,
                sizeof(stack_buf),
                (mach_vm_address_t) stack_buf,
                &inout_size) != KERN_SUCCESS)
            {
                break;
            }
            assert(inout_size == sizeof(stack_buf));
            stack_buf_addr = frame;
        }
        std::memcpy(&frame_struct, &stack_buf[frame - stack_buf_addr], sizeof(StackFrame));
#endif // USE_PAGE_CACHE

        // Sanity checks on new frame
        if (frame_struct.next <= frame) // Next frame equal or before previous
            break;
        if (frame_struct.next - frame > 1024 * 1024 * 256) // Next frame >256MB away from previous
            break;

        // Advance to next frame
        frame = frame_struct.next;

        // Output symbol
        stack_symbols_out[i] = g_symbol->AddressToSymbolID(frame_struct.ret);
    }

    (* stack_size_in_out) = i;
}

void HFSampleRun(
    uint num_smp_target,               // How many samples
    double target_time,                // Over how many seconds
    mach_port_name_t task_port,        // For which task
    uint *sample_cnt_out,              // How many we actually got
    const std::set<uint32>& merge_sym, // Symbols we're supposed to merge into their parents
    SymbolMap *sym_map_out)            // Symbol ID -> Symbol sample statistics map
{
    // Collect a single 'run' of samples for the HF sampling thread

    // List of threads
    thread_act_port_array_t thread_list;
    mach_msg_type_number_t thread_count;
    if (task_threads(task_port, &thread_list, &thread_count) != KERN_SUCCESS)
        assert(!"Can't obtain thread list");

    // Sample till we reach our target
    uint sample_attempts = 0;
    const double sampling_begin = TimerGetTick();
    while (g_stop_sampling_thread == false)
    {
        // Just slowly spin if we're supposed to freeze
        while (g_freeze_sampling_thread)
            usleep(1000 * 25);

        const uint sample_quantum = 100;
        for (uint sample=0;
             sample<sample_quantum && g_stop_sampling_thread == false;
             sample++)
        {
            // Shuffle threads so we don't oversample the ones earlier in the array
            std::random_shuffle(thread_list, thread_list + thread_count);

            // Find a thread for sampling
            // TODO: Sample previously running threads more frequently?
            for (uint thread_idx=0; thread_idx<thread_count; thread_idx++)
            {
                // Query thread scheduling etc. information
                thread_basic_info tbi;
                mach_msg_type_number_t thread_info_count = THREAD_BASIC_INFO_COUNT;
                if (thread_info(thread_list[thread_idx],
                                THREAD_BASIC_INFO,
                                (thread_info_t) &tbi,
                                &thread_info_count) != KERN_SUCCESS)
                {
                    continue; // Thread was likely terminated since we obtained the port
                }

                // Only sample running threads that actually take up execution
                // resources
                if (tbi.run_state != TH_STATE_RUNNING)
                    continue;

                // We need to suspend the thread so we can safely analyze the call stack
                if (thread_suspend(thread_list[thread_idx]) != KERN_SUCCESS)
                    continue;

                // TODO: Thread could've suspended between querying its status and sampling
                uint64 pc_sample, fp_sample;
                if ((GetPCFP(thread_list[thread_idx], &pc_sample, &fp_sample)))
                {
                    // TODO: Disabling the shuffle and adding this move-to-front code should
                    //       give a significant speed boost in scenarios where we spend a lot
                    //       of time looking for running threads. Figure out why it doesn't
                    //
                    // for (uint i=thread_idx; i>0; i--)
                    //     std::swap(thread_list[i], thread_list[i - 1]);

                    // Obtain the call stack
                    uint32 call_stack[256];
                    size_t depth = sizeof(call_stack) / sizeof(uint32);
                    if (g_prof_data.m_x64)
                        CaptureCallStack<uint64>(task_port, fp_sample, call_stack, &depth);
                    else
                        CaptureCallStack<uint32>(task_port, fp_sample, call_stack, &depth);

                    // Resume, we don't care about failure here
                    thread_resume(thread_list[thread_idx]);

                    // Lookup sample
                    uint16 file_name_id;
                    uint16 line_number;
                    uint32 symbol_id = g_symbol->AddressToSymbolID(
                        pc_sample, &file_name_id, &line_number);

                    // Any symbols that need to be merged on the call stack?
                    for (uint i=0; i<depth; i++)
                    {
                        if (merge_sym.find(call_stack[i]) != merge_sym.end())
                        {
                            // Found a function on the stack that's on our list, merge it into
                            // its parent by moving up the rest of the stack
                            depth--;
                            std::memmove(
                                &call_stack[i],
                                &call_stack[i + 1],
                                (depth - i) * sizeof(uint32));

                            i--; // Don't skip the entry we just moved up
                        }
                    }

                    // Do we need to do merging for the symbol at the sampled address?
                    if (merge_sym.find(symbol_id) != merge_sym.end())
                    {
                        if (depth > 0)
                        {
                            symbol_id = call_stack[0];

                            // Move up the call stack
                            depth--;
                            std::memmove(
                                call_stack,
                                &call_stack[1],
                                depth * sizeof(uint32));
                        }
                    }

                    // Add to map of symbols
                    MergeSymbolIntoMap(
                        symbol_id,
                        1,
                        call_stack,
                        depth,
                        file_name_id,
                        line_number,
                        (* sym_map_out));

                    // Got a sample
                    (* sample_cnt_out)++;
                    break;
                }

                // Resume, we don't care about failure here
                thread_resume(thread_list[thread_idx]);
            }
        }

        sample_attempts += sample_quantum;

        // Compute how much we need to sleep in-between sampling. The idea is that we're trying to
        // take num_smp_target samples in target_time seconds. We'd like to finish on time and use
        // as little CPU as possible while distributing the sampling evenly over the interval
        const double tick              = TimerGetTick();
        const uint   remaining_quanta  = (num_smp_target - sample_attempts) / sample_quantum;
        if (remaining_quanta == 0)
            break; // We're done
        const uint   taken_quanta      = sample_attempts / sample_quantum;
        const double elapsed_time      = tick - sampling_begin;
        const double remaining_time    = target_time - elapsed_time;
        const double time_per_quantum  = remaining_time / remaining_quanta;
        const double sleep_per_quantum = time_per_quantum - (elapsed_time / taken_quanta);

        if (sleep_per_quantum > 0.0)
            usleep(uint64(sleep_per_quantum * 1000.0 * 1000.0));
    }

    DeallocateThreadList(thread_list, thread_count);
}

void * HFSamplingThread(void *arg)
{
    // High-frequency sampling thread, collects the PCs and call stack data required for the
    // function level profile

    // We need a port for the task to be profiled
    mach_port_name_t task_port;
    if (task_for_pid(mach_task_self(), g_prof_data.m_pid, &task_port) != KERN_SUCCESS)
        assert(!"Can't get port for task");

    std::list<SymbolMap> sym_map_history;
    std::list<double> sym_collection_time_history;

    while (g_stop_sampling_thread == false)
    {
        // We keep a local copy of these as the user might change them at any time,
        // and the sampling code expects them to be constant during a single run
        const uint num_smp_target  = g_num_smp_target;
        const uint num_smp_profile = g_num_smp_profile;
        g_prof_data.Lock();
        const std::set<uint32> merge_sym = g_prof_data.m_merge_sym;
        g_prof_data.Unlock();

        // Collect samples for >= half a second
        const double tick = TimerGetTick();
        uint sample_cnt = 0;
        SymbolMap sym_map;
        HFSampleRun(num_smp_target, 0.5, task_port, &sample_cnt, merge_sym, &sym_map);

        // Add samples from this run into the history
        sym_map_history.push_back(sym_map);
        sym_collection_time_history.push_back(tick);

        // Are we being asked to reset the history?
        if (g_reset_profile)
        {
            g_reset_profile = false;
            sym_map_history.clear();
            sym_collection_time_history.clear();
        }

        // Collect samples from the history till we reach the sample target
        sym_map.clear();
        uint merged_sample_count     = 0;
        uint unresolved_sample_count = 0;
        uint num_hist_entries_used   = 0;
        double oldest_sample_used    = 0.0;
        std::list<double>::const_reverse_iterator it_time = sym_collection_time_history.rbegin();
        for (std::list<SymbolMap>::const_reverse_iterator it=sym_map_history.rbegin();
             it!=sym_map_history.rend();
             it++, it_time++)
        {
            num_hist_entries_used++;
            oldest_sample_used = (* it_time);

            const SymbolMap &merge_sym = (* it);     
            for (SymbolMap::const_iterator it_merge=merge_sym.begin();
                 it_merge!=merge_sym.end();
                 it_merge++)
            {
                MergeSymbolIntoMap((* it_merge), sym_map);
                merged_sample_count += (* it_merge).second.m_hits;

                // Unresolvable address?
                if (std::strcmp(
                    g_symbol->SymbolIDToName((* it_merge).first),
                    g_symbol->GetUnresolvedSymbolName()) == 0)
                {
                    unresolved_sample_count += (* it_merge).second.m_hits;
                }
            }

            if (merged_sample_count >= num_smp_profile)
                break;
        }

        assert(((merged_sample_count < num_smp_profile) &&
               (sym_map_history.size() > num_hist_entries_used)) == false);

        // Trim history to hold just the sample amount we're targeting to output
        while (sym_map_history.size() > num_hist_entries_used)
        {
            sym_map_history.pop_front();
            sym_collection_time_history.pop_front();
        }
        assert(sym_map_history.size() == sym_collection_time_history.size());

        g_prof_data.Lock();

        // Collection statistics
        g_prof_data.m_num_smp_collected       = sample_cnt;
        g_prof_data.m_num_smp_collected_total = merged_sample_count;
        g_prof_data.m_samples_unresolved      = unresolved_sample_count;
        g_prof_data.m_smp_collection_interval = TimerGetTick() - tick;
        g_prof_data.m_oldest_sample_used      = TimerGetTick() - oldest_sample_used;

        // Update function profile
        g_prof_data.m_functions.clear();
        for (SymbolMap::const_iterator it=sym_map.begin(); it!=sym_map.end(); it++)
        {
            g_prof_data.m_functions.push_back(ProfileData::Function());
            ProfileData::Function& func = g_prof_data.m_functions.back();
            func.m_sym_id = (* it).first;
            (* static_cast<SymSampleStats *>(&func)) = (* it).second;
            func.m_incoming.SortSiblingLists(); // Sort for display
        }
        std::sort(g_prof_data.m_functions.begin(), g_prof_data.m_functions.end());

        g_prof_data.Unlock();
    }

    // Cleanup
    if (mach_port_deallocate(mach_task_self(), task_port) != KERN_SUCCESS)
        assert(!"Can't deallocate port");

    return 0;
}

void UpdateProfDataThreadList(
    mach_port_name_t task_port,
    thread_act_port_array_t thread_list,
    mach_msg_type_number_t thread_count)
{
    // Update the thread list in the profiler output data

    g_prof_data.Lock();

    // Query task thread time information
    mach_msg_type_number_t task_info_count;
    task_thread_times_info tti;
    task_info_count = TASK_THREAD_TIMES_INFO_COUNT;
    if (task_info(task_port,
                  TASK_THREAD_TIMES_INFO,
                  (task_info_t) &tti,
                  &task_info_count) != KERN_SUCCESS)
    {
        assert(!"Can't get task info (TASK_THREAD_TIMES_INFO)");
    }
    g_prof_data.m_live_threads_user_time =
        double(tti.user_time.seconds) + double(tti.user_time.microseconds) / 1000000.0;
    g_prof_data.m_live_threads_system_time =
        double(tti.system_time.seconds) + double(tti.system_time.microseconds) / 1000000.0;

    g_prof_data.m_threads.clear();
    for (uint i=0; i<thread_count; i++)
    {
        // Query thread scheduling etc. information
        thread_basic_info tbi;
        mach_msg_type_number_t thread_info_count = THREAD_BASIC_INFO_COUNT;
        if (thread_info(thread_list[i],
                        THREAD_BASIC_INFO,
                        (thread_info_t) &tbi,
                        &thread_info_count) != KERN_SUCCESS)
        {
            continue; // Thread was likely terminated since we obtained the port
        }

        // Get program counter
        uint64 pc_sample, fp_sample;
        if ((GetPCFP(thread_list[i], &pc_sample, &fp_sample)) == false)
            continue;

        // Add thread to profiler output
        ProfileData::Thread thread;
        switch (tbi.run_state)
        {
            case TH_STATE_RUNNING: thread.m_run_state         = "Running";   break;
            case TH_STATE_STOPPED: thread.m_run_state         = "Stopped";   break;
            case TH_STATE_WAITING: thread.m_run_state         = "Waiting";   break;
            case TH_STATE_UNINTERRUPTIBLE: thread.m_run_state = "NoIntWait"; break;
            case TH_STATE_HALTED: thread.m_run_state          = "Halted";    break;
            default: thread.m_run_state                       = "Unknown";   break;
        }
        thread.m_cpu_usage_percentage_slow_update = thread.m_cpu_usage_percentage =
            float(tbi.cpu_usage) / float(TH_USAGE_SCALE) * 100.0f;
        thread.m_cur_symbol =
            std::string(g_symbol->SymbolIDToName(g_symbol->AddressToSymbolID(pc_sample)));
        thread.m_swapped_out = tbi.flags & TH_FLAGS_SWAPPED;
        g_prof_data.m_threads.push_back(thread);
    }

    g_prof_data.Unlock();
}

float GetProfilerCPUUsage()
{
    // Determine profiler CPU usage (TODO: Might want to include atos and fs_usage)

    thread_act_port_array_t prof_thread_list;
    mach_msg_type_number_t prof_thread_count;
    if (task_threads(mach_task_self(), &prof_thread_list, &prof_thread_count) != KERN_SUCCESS)
        assert(!"Can't obtain thread list");

    float prof_cpu = 0.0f;
    for (uint i=0; i<prof_thread_count; i++)
    {
        thread_basic_info tbi;
        mach_msg_type_number_t thread_info_count = THREAD_BASIC_INFO_COUNT;
        if (thread_info(prof_thread_list[i],
                        THREAD_BASIC_INFO,
                        (thread_info_t) &tbi,
                        &thread_info_count) != KERN_SUCCESS)
        {
            continue;
        }
        prof_cpu += float(tbi.cpu_usage) / float(TH_USAGE_SCALE) * 100.0f;
    }

    DeallocateThreadList(prof_thread_list, prof_thread_count);

    return prof_cpu;
}

struct POpen2Process
{
    POpen2Process() : m_pid(-1), m_stdin(NULL), m_stdout(NULL), m_stderr(NULL) { }

    pid_t m_pid;
    std::FILE *m_stdin;
    std::FILE *m_stdout;
    std::FILE *m_stderr;
};

POpen2Process POpen2(const char *executable, const char * const *argv)
{
    // Our own version of the popen() call, giving us a bit more control

    // Create pipes for communication with the process
    int stdin_pipe[2], stdout_pipe[2], stderr_pipe[2];
    if (pipe(stdin_pipe) != 0 || pipe(stdout_pipe) != 0 || pipe(stderr_pipe) != 0)
        assert(!"pipe() failed");

    // Fork
    POpen2Process ret;
    ret.m_pid = fork();
    assert(ret.m_pid >= 0);

    if (ret.m_pid == 0)
    {
        // Child

        // Not going to write to own stdin or read from stdout / sterr
        close(stdin_pipe [1]);
        close(stdout_pipe[0]);
        close(stderr_pipe[0]);

        // Overwrite stdin / stdout / stderr with pipe
        if (dup2(stdin_pipe [0], STDIN_FILENO)  == -1 ||
            dup2(stdout_pipe[1], STDOUT_FILENO) == -1 ||
            dup2(stderr_pipe[1], STDERR_FILENO) == -1)
        {
            assert(!"dup2() failed");
        }

        // Close originals
        close(stdin_pipe [0]);
        close(stdout_pipe[1]);
        close(stderr_pipe[1]);

        // Execute
        if (execvp(executable, const_cast<char * const *> (argv)) == -1)
            assert("execvp() failed");
    }

    // Not going to read from child's stdin or write to its stdout / stderr
    close(stdin_pipe [0]);
    close(stdout_pipe[1]);
    close(stderr_pipe[1]);

    // Create streams. Caller must fclose() these, which also calls close() on the original FD
    ret.m_stdin  = fdopen(stdin_pipe [1], "w");
    ret.m_stdout = fdopen(stdout_pipe[0], "r");
    ret.m_stderr = fdopen(stderr_pipe[0], "r");
    assert(ret.m_stdin != NULL && ret.m_stdout != NULL && ret.m_stderr != NULL);

    return ret;
}

// Wrapper around the fs_usage tool
//
// http://developer.apple.com/library/mac/#documentation/Darwin/Reference/ManPages/man1/fs_usage.1.html
//
// The tool uses the kdebug system call tracing facility internally. Its code size is similar to
// that of the entire profiler. Documentation for kdebug is sparse. Things change between OS
// revisions. These reasons make wrapping around the existing tool an attractive choice. Should we
// ever need to change that, the source code for fs_usage, sc_usage and some kdebug documentation
// is available here:
//
// http://opensource.apple.com/source/system_cmds/system_cmds-550.10/fs_usage.tproj/
// http://opensource.apple.com/source/system_cmds/system_cmds-550.10/sc_usage.tproj/
// http://books.google.com/books?id=K8vUkpOXhN4C&pg=PA625&lpg=PA625
class FSUsage_Pipe
{
public:
    FSUsage_Pipe(pid_t pid) :
        m_pid(pid),
        m_iop(0),
        m_bytes_read(0),
        m_bytes_written(0),
        m_last_tick(-1.0),
        m_last_iop(0),
        m_last_bytes_read(0),
        m_last_bytes_written(0)
    {
        m_page_size = GetHostPageSize();

        // Prepare system call function tables. Those are matched against the fs_usage source
        const char read_func_names[][32] =
            { "read", "readv", "pread", "getdirentries", "getdirentries64", "recvfrom", "recvmsg" };
        for (uint i=0; i<sizeof(read_func_names) / sizeof(char *); i++)
            m_read_funcs.insert(read_func_names[i]);
        const char write_func_names[][32] =
            { "write" , "writev", "pwrite", "sendto", "sendmsg" };
        for (uint i=0; i<sizeof(write_func_names) / sizeof(char *); i++)
            m_write_funcs.insert(write_func_names[i]);
        const char io_func_names[][32] =
        {
            "sendfile",
            "select", "accept", "socket", "connect", "bind",
            "listen", "mmap", "socketpair", "getxattr", "setxattr",
            "removexattr", "listxattr", "stat", "stat64", "stat_extended",
            "stat_extended64", "mount", "unmount", "exit", "execve",
            "posix_spawn", "load_sf", "open", "open_extended", "dup",
            "dup2", "close", "fgetxattr",
            "fsetxattr", "fremovexattr", "flistxattr", "fstat", "fstat64",
            "fstat_extended", "fstat64_extended", "lstat", "lstat64", "lstat_extended",
            "lstat_extended64", "lstatv", "link", "unlink", "mknod",
            "umask", "chmod", "chmod_extended", "fchmod", "fchmod_extended",
            "chown", "lchown", "fchown", "access", "access_extended",
            "chdir", "pthread_chdir", "chroot", "utimes", "delete-Carbon",
            "undelete", "revoke", "fsctl", "chflags", "fchflags",
            "fchdir", "pthread_fchdir", "futimes", "sync", "symlink",
            "readlink", "fsync", "mkdir", "mkdir_extended", "mkfifo", "mkfifo_extended",
            "rmdir", "statfs", "statfs64", "getfsstat", "getfsstat64",
            "fstatfs", "fstatfs64", "pathconf", "fpathconf",
            "lseek", "truncate", "ftruncate", "statv",
            "fstatv", "mkcomplex", "getattrlist", "setattrlist", "getdirentriesattr",
            "exchangedata", "rename", "copyfile", "checkuseraccess", "searchfs",
            "aio_fsync", "aio_return", "aio_suspend", "aio_cancel", "aio_error",
            "aio_read", "aio_write", "lio_listio", "msync", "fcntl",
            "ioctl", "IOCTL"
        };
        for (uint i=0; i<sizeof(io_func_names) / sizeof(char *); i++)
            m_io_funcs.insert(io_func_names[i]);

        InitPipe();
    }

    ~FSUsage_Pipe() { Shutdown(); }

    void ProcessSystemCalls()
    {
        if (IsRunning() == false)
           return; 

        char buf[1024];

        // Check for errors
        while (std::fgets(buf, sizeof(buf), m_pipe.m_stderr) != NULL)
        {
            // Trace facility used by another process?
            if (std::strstr(buf, "currently in use") != NULL) 
            {
                Shutdown();
                return;
            }
#ifdef FS_USAGE_DBG_PRINT
            else
                std::fprintf(stderr, "%s", buf); // Repeat other errors
#endif // FS_USAGE_DBG_PRINT
        }

        // Process system calls
        while (std::fgets(buf, sizeof(buf), m_pipe.m_stdout) != NULL)
        {
            m_iop++;

            // Determine byte count, if any
            uint bytes = 0;
            {
                char *byte_str = std::strstr(buf, " B=");
                if (byte_str != NULL)
                    std::sscanf(byte_str + 3, "%x", &bytes);
            }

            // Get call name
            char syscall_name[1024];
            (* syscall_name) = '\0';
            char *name_loc = std::strstr(buf, "  ");
            if (name_loc != NULL)
            {
                name_loc += 2;
                char *name_end = std::strchr(name_loc, ' ');
                if (name_end != NULL)
                {
                    assert(sizeof(syscall_name) > size_t(name_end - name_loc));
                    std::strncpy(syscall_name, name_loc, name_end - name_loc);
                    syscall_name[name_end - name_loc] = '\0';
                }
            }

            // Read?
            if (m_read_funcs.find(syscall_name) != m_read_funcs.end())
            {
                m_bytes_read += bytes;
                if (bytes != 0) // TODO: We seem to have quite a few of those on 10.8
                    continue;
            }

            // Page-in?
            if (std::strncmp(syscall_name, "PAGE_IN", 7) == 0)
            {
                m_bytes_read += m_page_size;
                continue;
            }

            // Write?
            if (m_write_funcs.find(syscall_name) != m_write_funcs.end())
            {
                m_bytes_written += bytes;
                if (bytes != 0)
                    continue;
            }

            // Page-out?
            if (std::strncmp(syscall_name, "PAGE_OUT", 8) == 0)
            {
                m_bytes_written += m_page_size;
                continue;
            }

            // Known IO function?
            if (m_io_funcs.find(syscall_name) != m_io_funcs.end())
            {
                if (bytes == 0 || std::strcmp(syscall_name, "mmap") == 0)
                    continue;
            }

#ifdef FS_USAGE_DBG_PRINT
            // Debug: Print unknown functions, known read / write with no byte count
            //        and known generic IO with an nonzero byte count
            std::printf("%s", buf);
            std::printf("%s() - %i Bytes\n\n", syscall_name, bytes);
#endif // FS_USAGE_DBG_PRINT
        }
    }

    bool UpdateStatistics(
        uint& iops_out,
        uint& bytes_read_sec_out,
        uint& bytes_written_sec_out,
        std::vector<uint64>& combined_bytes_sec_hist)
    {
        // Update internal per-second statistics and update passed variables if
        // enough time has passed. Also return true in that case

        const double cur_tick = TimerGetTick();
        if (m_last_tick == -1.0)
            m_last_tick = cur_tick;
        const double time_elapsed = cur_tick - m_last_tick;
        if (time_elapsed == 0.0)
            return false;

        // Always add an entry to the passed history table. Wait a second in the
        // beginning for a stable value, though.
        //
        // TODO: Since we're using increasing intervals till we reset at the
        //       full second, peaks in the graph will always have that ramp
        //       shape. Consider adding a second set of m_last_ values
        if (combined_bytes_sec_hist.empty() == false || time_elapsed >= 1.0)
        {
            combined_bytes_sec_hist.push_back(uint64(
                ((m_bytes_read    - m_last_bytes_read    ) +
                 (m_bytes_written - m_last_bytes_written)) / time_elapsed));
        }

        // Per-second update?
        if (time_elapsed >= 1.0)
        {
            iops_out = m_iop - m_last_iop;
            bytes_read_sec_out = m_bytes_read - m_last_bytes_read;
            bytes_written_sec_out = m_bytes_written - m_last_bytes_written;

            m_last_iop = m_iop;
            m_last_bytes_read = m_bytes_read;
            m_last_bytes_written = m_bytes_written;

            m_last_tick = cur_tick;

            return true;
        }

        return false;
    }

    bool IsRunning() const { return m_pipe.m_pid != -1; }

protected:
    uint m_page_size;
    pid_t m_pid;
    POpen2Process m_pipe;

    uint m_iop;
    uint64 m_bytes_read;
    uint64 m_bytes_written;

    double m_last_tick;
    uint m_last_iop;
    uint64 m_last_bytes_read;
    uint64 m_last_bytes_written;

    std::set<std::string> m_read_funcs;
    std::set<std::string> m_write_funcs;
    std::set<std::string> m_io_funcs;

    void InitPipe()
    {
        Shutdown();

        // Create pipes and launch fs_usage
        char pid_buf[32];
        std::snprintf(pid_buf, sizeof(pid_buf), "%i", m_pid);
        const char * const command_argv[] =
        {
            "fs_usage",
            "-f",
            "filesys",
            "-w",
            pid_buf,
            NULL
        };
        m_pipe = POpen2(command_argv[0], command_argv);

        // Set stdout / stderr to non-blocking. This way we don't need a dedicated thread to read
        // from it without risking to block a sampling thread indefinitely
        SetNonBlocking(m_pipe.m_stdout);
        SetNonBlocking(m_pipe.m_stderr);
    }

    void SetNonBlocking(std::FILE *file)
    {
        const int fd = fileno(file);
        int flags = fcntl(fd, F_GETFL, 0);
        flags |= O_NONBLOCK;
        fcntl(fd, F_SETFL, flags);
    }

    void Shutdown()
    {
        // TODO: Currently when we crash fs_usage is left hanging around, locking up the kdebug
        //       facility. Consider adding a signal handler that'll shut it down in any case

        // Kill fs_usage and close pipe file handles
        if (IsRunning())
        {
            if (kill(m_pipe.m_pid, SIGINT) != 0)
                assert(!"kill() failed");

            std::fclose(m_pipe.m_stdin);
            std::fclose(m_pipe.m_stdout);
            std::fclose(m_pipe.m_stderr);
            m_pipe = POpen2Process();
        }
    }
};

std::auto_ptr<FSUsage_Pipe> g_fs_usage;

void UpdateProfData10x(
    mach_port_name_t task_port,
    thread_act_port_array_t thread_list,
    mach_msg_type_number_t thread_count)
{
    // Update all the statistics in the profiler data output which need updating
    // ~10x per second

    // Process messages from fs_usage
    g_fs_usage->ProcessSystemCalls();

    g_prof_data.Lock();

    // Query basic task information
    mach_msg_type_number_t task_info_count;
    task_basic_info_64 ti64;
    task_info_count = TASK_BASIC_INFO_64_COUNT;
    if (task_info(task_port,
                  TASK_BASIC_INFO_64,
                  (task_info_t) &ti64,
                  &task_info_count) != KERN_SUCCESS)
    {
        assert(!"Can't get task info (TASK_BASIC_INFO_64)");
    }

    // Memory profiling
    g_prof_data.m_resident_memory = ti64.resident_size;
    g_prof_data.m_res_mem_hist.push_back(ti64.resident_size);

    // For converting the task events into a per-second basis
    static task_events_info last_tei;
    static double last_tei_tick = -1.0;
    if (last_tei_tick == -1.0)
        std::memset(&last_tei, 0, sizeof(task_events_info));

    // Query event information, store ~1sec delta into the profile data
    const double cur_tick = TimerGetTick();
    if (last_tei_tick == -1.0 || cur_tick - last_tei_tick >= 1.0)
    {
        task_events_info tei;
        task_info_count = TASK_EVENTS_INFO_COUNT;
        if (task_info(task_port,
                      TASK_EVENTS_INFO,
                      (task_info_t) &tei,
                      &task_info_count) != KERN_SUCCESS)
        {
            assert(!"Can't get task info (TASK_EVENTS_INFO)");
        }

        if (last_tei_tick != -1.0)
        {
            g_prof_data.m_tei = tei;
            g_prof_data.m_tei.faults             -= last_tei.faults;
            g_prof_data.m_tei.pageins            -= last_tei.pageins;
            g_prof_data.m_tei.cow_faults         -= last_tei.cow_faults;
            g_prof_data.m_tei.messages_sent      -= last_tei.messages_sent;
            g_prof_data.m_tei.messages_received  -= last_tei.messages_received;
            g_prof_data.m_tei.syscalls_mach      -= last_tei.syscalls_mach;
            g_prof_data.m_tei.syscalls_unix      -= last_tei.syscalls_unix;
            g_prof_data.m_tei.csw                -= last_tei.csw;
        }

        last_tei = tei;
        last_tei_tick = cur_tick;
    }

    // TODO: This loop is a bit dodgy. Will assert() when there's zero
    //       threads added in m_threads and will assign CPU usage to the
    //       wrong thread if one or more became unavailable since the
    //       outer loop ran
    for (uint i=0, thread_idx=0; i<thread_count; i++)
    {
        // Query thread scheduling etc. information
        thread_basic_info tbi;
        mach_msg_type_number_t thread_info_count = THREAD_BASIC_INFO_COUNT;
        if (thread_info(thread_list[i],
                        THREAD_BASIC_INFO,
                        (thread_info_t) &tbi,
                        &thread_info_count) != KERN_SUCCESS)
        {
            continue; // Thread was likely terminated since we obtained the port
        }

        // Only thing we update at 100ms intervals about threads is the
        // CPU usage. All other quantities can't be read quickly enough
        // to make it worthwhile
        assert(thread_idx < g_prof_data.m_threads.size());
        g_prof_data.m_threads[thread_idx++].m_cpu_usage_percentage =
            float(tbi.cpu_usage) / float(TH_USAGE_SCALE) * 100.0f;
    }

    g_prof_data.m_prof_cpu = GetProfilerCPUUsage();

    // IO profiling
    g_fs_usage->UpdateStatistics(
        g_prof_data.m_iops,
        g_prof_data.m_bytes_read_sec,
        g_prof_data.m_bytes_written_sec,
        g_prof_data.m_combined_bytes_sec_hist);
    g_prof_data.m_fs_usage_running = g_fs_usage->IsRunning();

    g_prof_data.Unlock();
}

void * SamplingThread(void *arg)
{
    // Main sampling thread. Do all data collection which happens and 500ms and
    // 100ms intervals, also launch the HF sampling thread for anything more frequent

    // Launch HF sampling thread
    pthread_t hf_sampling_thread;
    if (pthread_create(&hf_sampling_thread, NULL, HFSamplingThread, NULL) != 0)
        assert(!"HF sampling thread creation failed");

    // We need a port for the task to be profiled
    mach_port_name_t task_port;
    if (task_for_pid(mach_task_self(), g_prof_data.m_pid, &task_port) != KERN_SUCCESS)
        assert(!"Can't get port for task");

    while (g_stop_sampling_thread == false)
    {
        // Outer sampling loop, all this code runs every ~500ms

        // List of threads
        thread_act_port_array_t thread_list;
        mach_msg_type_number_t thread_count;
        if (task_threads(task_port, &thread_list, &thread_count) != KERN_SUCCESS)
            assert(!"Can't obtain thread list");

        UpdateProfDataThreadList(task_port, thread_list, thread_count);

        // Inner sampling loop, this code runs every ~100ms
        for (uint inner_prof=0; inner_prof<5 && g_stop_sampling_thread == false; inner_prof++)
        {
            // Just slowly spin if we're supposed to freeze
            while (g_freeze_sampling_thread)
                usleep(1000 * 25);

            UpdateProfData10x(task_port, thread_list, thread_count);

            // 5 * 100ms, loop runs for half a second
            usleep(1000 * 100);
        }

        DeallocateThreadList(thread_list, thread_count);
    }

    // Cleanup
    if (pthread_join(hf_sampling_thread, NULL) != 0)
        assert(!"pthread_join() for HF sampling thread failed");
    if (mach_port_deallocate(mach_task_self(), task_port) != KERN_SUCCESS)
        assert(!"Can't deallocate port");

    return 0;
}

// Font
const uint32 g_misc_fixed_6x12_data[16 * 16 * 6 * 12 / 8 / 4] = 
{
    0x00000000, 0x00000000, 0x20080200, 0x00000000, 0x00000000, 0x10080100, 0x711c2772, 0xc7f100c7,
    0x088f701c, 0x8aa2288a, 0x28ca8828, 0x944889a2, 0x8aa2288a, 0x28aa8028, 0xa2288aa2, 0x8aa2288b,
    0x289abe28, 0xa2288aa2, 0x711cc77a, 0x287a00c7, 0x222f8aa2, 0x00000008, 0x00000800, 0x00080000,
    0x5208c252, 0x820000c5, 0x14885014, 0x2104a421, 0x010100a0, 0x00400008, 0x00000050, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00001800, 0x00000000, 0x00000000,
    0x00000400, 0x00000000, 0x799ee779, 0xc7719ce7, 0x1cc7711c, 0x8aa2288a, 0x0882222a, 0x08822020,
    0x799ee779, 0xcff320e7, 0x0882203c, 0x08822008, 0x288aa222, 0x088220a2, 0x711cc771, 0xc7711cc7,
    0x1886611c, 0x00000000, 0x00000080, 0x00000000, 0x512c8520, 0x85200040, 0x14852014, 0x001a4240,
    0x42400080, 0x00424000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00800000, 0x00000000, 0x711c2772, 0xc77100c7,
    0x2c84701c, 0x8aa2284a, 0x28caa228, 0x228788a2, 0x8aa2684a, 0x28aa9428, 0xa48488a2, 0x8aa2a8ea,
    0x28aa8828, 0xa88488a2, 0x8aa2284b, 0x28aa9428, 0xa44489a2, 0x8aa2284a, 0x289aa228, 0x22278aa2,
    0x711c2772, 0x287200c7, 0x1c248aa2, 0x00000000, 0x00080000, 0x00000000, 0x5208c202, 0x820000c5,
    0x00805014, 0x2104a401, 0x010100a0, 0x00400008, 0x00000000, 0x00001800, 0x00000000, 0x00000000,
    0x00000400, 0x00000000, 0x8aa2288a, 0xeffb9c2b, 0x1cc771be, 0x8aa2288a, 0x0882222a, 0x08822020,
    0x8aa2288a, 0x0882202a, 0x08822020, 0xfbbeeffb, 0xcff320ef, 0x0882203c, 0x8aa2288a, 0x0882202a,
    0x08822020, 0x8aa2288a, 0x0882222a, 0x08822020, 0x711cc771, 0xeffb9cc7, 0x1cc771be, 0x00000000,
    0x00000080, 0x00000000, 0x512c8520, 0x85200040, 0x14852014, 0x001a4240, 0x42400080, 0x00424000,
    0x02000000, 0x00600000, 0x00000000, 0x02000000, 0x00100000, 0x00000000, 0x0300e003, 0x000080a2,
    0x1ce11028, 0x02000000, 0x00008062, 0x22811014, 0x02008000, 0x00008022, 0x9047780a, 0x02008000,
    0x00008c26, 0x08255014, 0x0200e003, 0x00008c2e, 0x08a33028, 0x40188730, 0xc701800e, 0x004d5100,
    0x20048248, 0x8000800e, 0x08024100, 0x10080148, 0x82008007, 0x00044100, 0x00040530, 0x85010000,
    0x0002c300, 0x00180200, 0x82000000, 0x000c4100, 0x00000000, 0x00000000, 0x00000000, 0x00000200,
    0x00000000, 0x00000000, 0xa82c8700, 0xe0011c82, 0x8007000a, 0x50928a00, 0x10020282, 0x40080814,
    0x8b108a00, 0x50020ce2, 0x400a0828, 0x50b88a00, 0x90021280, 0x40caf914, 0xab108700, 0x570212e2,
    0x400b000a, 0x01120200, 0x10020c42, 0x40080000, 0x020c8000, 0xe3011022, 0x80070000, 0x00000000,
    0x05500e00, 0x3e000000, 0x00000000, 0x03000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00002080, 0x00020000, 0x00000000, 0x00002080, 0x00010000, 0x00002104, 0x193ce8f1, 0x8f8814a2,
    0x00802088, 0x2202288a, 0x44512a65, 0x00802008, 0x221c288a, 0x2222aa28, 0x00892008, 0x22a02c8a,
    0x2152a228, 0x804a2010, 0xfa1eebf1, 0x2f8aa228, 0x80842088, 0x20000000, 0x00000000, 0x00802008,
    0x20000000, 0x00000000, 0x00802008, 0x00000000, 0x00000000, 0x00002104, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x03001c00, 0x00000000, 0x00000000,
    0x04000200, 0x00000080, 0x791cef01, 0xc0891ec4, 0x9ca872a2, 0x8aa22802, 0x80882204, 0xa2a822a4,
    0x8ba0e801, 0x808822c4, 0xa2a822b8, 0x8aa22800, 0x8088222e, 0xa2ac22a4, 0x791ccf01, 0x81f11cc4,
    0x1c4b23a2, 0x08000810, 0x00808004, 0x00002020, 0x08000820, 0x80800003, 0x000060a0, 0x00000040,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x3e000000, 0x00000000, 0x00000000, 0x00c0011c, 0x219ca881, 0x8f8814c2,
    0x00400890, 0x22224982, 0x88882a25, 0x00401010, 0x2202aa82, 0x84502a25, 0x00401010, 0x221c2ff2,
    0x8220a228, 0x00402010, 0x22a0288a, 0x4151a228, 0x00404010, 0x22a2288a, 0x208aa228, 0x80484090,
    0xfa1ccff1, 0x2f8aa228, 0x00458090, 0x00000000, 0x00000000, 0x00c2011c, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0xf31c2f72, 0xc6891ce8, 0x9c28fa22, 0x4aa22482, 0x89882208, 0xa2288224,
    0x4aa024ba, 0x81882608, 0xa2298228, 0x4b20e7ab, 0x81f820cf, 0xa22a8230, 0x4aa024ba, 0x81882008,
    0xa2ac8228, 0x4aa2248a, 0x81882208, 0xa2688324, 0xf31ccf71, 0xc3899cef, 0x9c2882a2, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000030, 0x119ccf31, 0x867108c7,
    0x08000018, 0x12228448, 0x46888828, 0x00041018, 0xf8028248, 0x20888828, 0x08e22300, 0x900c8148,
    0xe671042f, 0x08014018, 0x53848048, 0x268a04c8, 0x04e22318, 0x32828849, 0x208a0204, 0x22041000,
    0x133e8730, 0xc0713ee3, 0x1c000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x20000000,
    0x00110000, 0x0000c000, 0x72148000, 0x82208066, 0x20066000, 0xaa3e0000, 0x8a200069, 0x10066088,
    0x29148000, 0x4740800a, 0x10000008, 0x70148000, 0x42400084, 0x08e0033e, 0xa03e8000, 0x4740004a,
    0x04000008, 0xab148500, 0x8a20082a, 0x04000088, 0x73008500, 0x82200824, 0x02000000, 0x20000500,
    0x00110800, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0xfc000000, 0x80200082, 0x00000000, 0x00000000, 0x80200082, 0x00000000, 0x00000000, 0x8f200082,
    0x000b51be, 0x003f0000, 0x80200082, 0x80045100, 0x00000000, 0x81200082, 0x00e453b0, 0x00c00f00,
    0x86fc3ffe, 0x0c8e500c, 0x00000000, 0x88000882, 0x0ce4fb02, 0x00000000, 0x86000882, 0x8044000c,
    0x0000f003, 0x81000882, 0x004300b0, 0x00000000, 0x80000882, 0x00000000, 0x00000000, 0x80000882,
    0x00000000, 0x000000fc, 0x80000882, 0x00000000, 0x00400500, 0x00000000, 0x08002000, 0x00800a00,
    0x00000000, 0x08002000, 0x204405a8, 0x00f800a2, 0x08002000, 0x20848a00, 0x000000a3, 0x08002000,
    0x3044c589, 0x002000c2, 0x08002000, 0xa084ea03, 0x002080a3, 0xff03e038, 0xb96ec589, 0x00f800c0,
    0x08020008, 0xc2a88a00, 0x00200c0e, 0x08020008, 0x827805a8, 0x00201208, 0x08020008, 0xe2a80a00,
    0x00001208, 0x08020008, 0x01680500, 0x00000c88, 0x08020008, 0x00800a00, 0x00000000, 0x08020008
};

class FontRendering
{
public:
    FontRendering() : m_font_tex((GLuint) -1) { }

    ~FontRendering()
    {
        // Delete OpenGL font texture
        if (m_font_tex != (GLuint) - 1)
            glDeleteTextures(1, &m_font_tex);
    }

    void DrawStringFixed6x12(
        int x, int y,
        const char *str,
        uint32 color = 0xFFFFFFFF,
        bool vertical = false)
    {
        // Keep a record of all text rendered during a frame
        m_text += str;
        m_text += "\n";

        // Draw text as textured quads
        uint xoffs = 0, yoffs = 0;
        const size_t length = std::strlen(str);
        for (uint i=0; i<length; i++)
        {
            if (str[i] == '\n')
            {
                xoffs = 0;
                yoffs -= 10;
                continue;
            }

            // Weird encoding magic to get the upper 127 characters, probably
            // somewhat wrong
            int idx = str[i];
            if (idx == -61)
                continue;
            if (idx < 0)
                idx = 255 - 1 - (61 + (-idx) - 127);

            // Position of character on the font grid
            const uint tx = (idx % font_grid_wdh);
            const uint ty =
                font_grid_hgt - ((idx - (idx % font_grid_wdh)) / font_grid_wdh + 1);

            // Texture coordinate origin of character
            const float ftx = float(tx * font_char_wdh) / float(font_tex_wdh);
            const float fty = float(ty * font_char_hgt) / float(font_tex_wdh);

            const uint idx_base = m_pos.size();

            // Position & texture coordinates
            m_tex_coords.push_back(Vec2f(
               ftx,
               fty));
            m_pos.push_back(Vec2f(x + xoffs, y + yoffs));
            m_tex_coords.push_back(Vec2f(
               ftx + float(font_char_wdh) / float(font_tex_wdh),
               fty));
            m_pos.push_back(Vec2f(x + xoffs + font_char_wdh, y + yoffs));
            m_tex_coords.push_back(Vec2f(
               ftx + float(font_char_wdh) / float(font_tex_wdh),
               fty + float(font_char_hgt) / float(font_tex_wdh)));
            m_pos.push_back(Vec2f(x + xoffs + font_char_wdh, y + font_char_hgt + yoffs));
            m_tex_coords.push_back(Vec2f(
               ftx,
               fty + float(font_char_hgt) / float(font_tex_wdh)));
            m_pos.push_back(Vec2f(x + xoffs, y + font_char_hgt + yoffs));

            // Colors
            for (uint rep=0; rep<4; rep++)
                m_colors.push_back(color);

            // Indices
            m_indices.push_back(idx_base + 0);
            m_indices.push_back(idx_base + 1);
            m_indices.push_back(idx_base + 3);
            m_indices.push_back(idx_base + 1);
            m_indices.push_back(idx_base + 2);
            m_indices.push_back(idx_base + 3);

            // For drawing vertical text
            if (vertical)    
            {
                xoffs = 0;
                yoffs -= 9;
            }
            else
                xoffs += font_char_wdh;
        }
    }

    void Render(bool filter_font_texture)
    {
        assert(m_pos.size() == m_tex_coords.size());
        assert(m_indices.size() % 6 == 0);
        assert(m_indices.size() / 6 * 4 == m_pos.size());

        if (m_indices.empty())
            return;

        // Preserve text
        m_last_frame_text = m_text;
        m_text.clear();

        // Initialize OpenGL font texture
        if (m_font_tex == (GLuint) -1)
        {
            // Create font texture
            glGenTextures(1, &m_font_tex);
            glBindTexture(GL_TEXTURE_2D, m_font_tex);

            // Convert bit packed font image to luminance texture
            uint tex_image[font_tex_wdh * font_tex_wdh];
            for (uint y=0; y<font_img_hgt; y++)
                for (uint x=0; x<font_img_wdh; x++)
                {
                    uint *dst = &tex_image[x + y * font_tex_wdh];
                    const uint src_idx = x + y * font_img_wdh;
                    // Extract bit (reversed in byte), store white / back pixel
                    (* dst) = (reinterpret_cast<const uchar *>(g_misc_fixed_6x12_data)[src_idx / 8]
                        & (1 << (7 - (src_idx % 8)))) ? 0xFFFFFFFF : 0x00FFFFFF;
                }

            // Upload texture image
            gluBuild2DMipmapLevels(
                GL_TEXTURE_2D,
                GL_RGBA8,
                font_tex_wdh,
                font_tex_wdh,
                GL_BGRA,
                GL_UNSIGNED_BYTE,
                0,
                0,
                8,
                tex_image);
        }

        // Bind font texture
        glBindTexture(GL_TEXTURE_2D, m_font_tex);
        glEnable(GL_TEXTURE_2D);

        // Texture filtering?
        if (filter_font_texture)
        {
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR_MIPMAP_LINEAR);
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
        }
        else
        {
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
            glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
        }

        // Alpha blending
        glEnable(GL_BLEND);
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

        // Draw
        glEnableClientState(GL_VERTEX_ARRAY);
        glEnableClientState(GL_TEXTURE_COORD_ARRAY);
        glEnableClientState(GL_COLOR_ARRAY);
        glVertexPointer(2, GL_FLOAT, 0, &m_pos[0]);
        glTexCoordPointer(2, GL_FLOAT, 0, &m_tex_coords[0]);
        glColorPointer(4, GL_UNSIGNED_BYTE, 0, &m_colors[0]);
        glDrawElements(GL_TRIANGLES, m_indices.size(), GL_UNSIGNED_INT, &m_indices[0]);
        glDisableClientState(GL_VERTEX_ARRAY);
        glDisableClientState(GL_TEXTURE_COORD_ARRAY);
        glDisableClientState(GL_COLOR_ARRAY);

        // Empty for the next frame
        m_pos.clear();
        m_tex_coords.clear();
        m_colors.clear();
        m_indices.clear();

        glDisable(GL_BLEND);
        glDisable(GL_TEXTURE_2D);
    }

    const char * GetLastFrameText() const { return m_last_frame_text.c_str(); }

protected:
    typedef std::pair<float, float> Vec2f;

    GLuint m_font_tex;
    std::vector<Vec2f> m_pos;
    std::vector<Vec2f> m_tex_coords;
    std::vector<uint32> m_colors;
    std::vector<GLuint> m_indices;

    std::string m_text;
    std::string m_last_frame_text;

    enum { font_grid_wdh = 16  };
    enum { font_grid_hgt = 16  };
    enum { font_img_wdh  = 96  };
    enum { font_img_hgt  = 192 };
    enum { font_char_wdh = 6   };
    enum { font_char_hgt = 12  };
    enum { font_tex_wdh  = 256 };

} g_font;

// GUI helpers
int InvX(const int x) { return g_wnd_wdh - x; }
int InvY(const int y) { return g_wnd_hgt - y; }

void DrawSpinningCube(uint x, uint y, uint width)
{
    // Draw a spinning cube as an indicator that the GUI is still updating

    glMatrixMode(GL_PROJECTION);
    glPushMatrix();
    glLoadIdentity();
    glOrtho(0, g_wnd_wdh, 0, g_wnd_hgt, 1.0f, width * 2);

    glMatrixMode(GL_MODELVIEW);
    glPushMatrix();
    glLoadIdentity();
    glTranslatef(x + width / 2.0f, y + width / 2.0f, - int(width));
    glScalef(width / 4.0f, width / 4.0f, width / 4.0f);
    const double cur_tick = TimerGetTick();
    glRotatef(360.0f * float(cur_tick / 4.0 - std::floor(cur_tick / 4.0)),
        0.0f, 1.0f, 1.0f);

    glEnable(GL_LIGHTING);
    glEnable(GL_LIGHT0); 
    glDisable(GL_CULL_FACE);
    glEnable(GL_DEPTH_TEST);
    glEnable(GL_NORMALIZE);

    // TODO: Winding isn't consistent on these
    glBegin(GL_QUADS); 
        glNormal3f( 0.0f, -1.0f,  0.0f);
        glVertex3f(-1.0f, -1.0f, -1.0f); 
        glVertex3f( 1.0f, -1.0f, -1.0f);
        glVertex3f( 1.0f, -1.0f,  1.0f);
        glVertex3f(-1.0f, -1.0f,  1.0f);
        glNormal3f( 0.0f,  1.0f,  0.0f);
        glVertex3f(-1.0f,  1.0f, -1.0f);
        glVertex3f( 1.0f,  1.0f, -1.0f);
        glVertex3f( 1.0f,  1.0f,  1.0f);
        glVertex3f(-1.0f,  1.0f,  1.0f);
        glNormal3f( 0.0f,  0.0f, -1.0f);
        glVertex3f(-1.0f, -1.0f, -1.0f);
        glVertex3f( 1.0f, -1.0f, -1.0f);
        glVertex3f( 1.0f,  1.0f, -1.0f);
        glVertex3f(-1.0f,  1.0f, -1.0f);
        glNormal3f( 0.0f,  0.0f,  1.0f); 
        glVertex3f(-1.0f, -1.0f,  1.0f);
        glVertex3f( 1.0f, -1.0f,  1.0f);
        glVertex3f( 1.0f,  1.0f,  1.0f); 
        glVertex3f(-1.0f,  1.0f,  1.0f);
        glNormal3f(-1.0f,  0.0f,  0.0f);  
        glVertex3f(-1.0f, -1.0f, -1.0f); 
        glVertex3f(-1.0f,  1.0f, -1.0f);
        glVertex3f(-1.0f,  1.0f,  1.0f);
        glVertex3f(-1.0f, -1.0f,  1.0f);
        glNormal3f( 1.0f,  0.0f,  0.0f);
        glVertex3f( 1.0f, -1.0f, -1.0f); 
        glVertex3f( 1.0f,  1.0f, -1.0f);
        glVertex3f( 1.0f,  1.0f,  1.0f);
        glVertex3f( 1.0f, -1.0f,  1.0f);
    glEnd();

    glDisable(GL_NORMALIZE);
    glDisable(GL_LIGHTING);
    glDisable(GL_DEPTH_TEST);
    glMatrixMode(GL_PROJECTION);
    glPopMatrix();
    glMatrixMode(GL_MODELVIEW);
    glPopMatrix();
}

void EnableLineAA()
{
    glEnable(GL_LINE_SMOOTH);
    glEnable(GL_BLEND);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
}

void DisableLineAA()
{
    glDisable(GL_LINE_SMOOTH);
    glDisable(GL_BLEND);
}

void DrawProgressBar(
    uint x, uint y,
    uint width, uint height,
    float progress,
    bool grey = false)
{
    const float bar_width = progress * float(width - 1) / 100.0f;

    if (grey)
        glColor3f(0.6f, 0.6f, 0.6f);

    // Bar
    glBegin(GL_QUADS);
        if (grey == false)
            glColor3f(0.0f, 0.3f, 0.0f);
        glVertex2f(x + 1,             y);
        glVertex2f(x + 1 + bar_width, y);
        if (grey == false)
            glColor3f(0.0f, 0.95f, 0.0f);
        glVertex2f(x + 1 + bar_width, y - (height / 2 - 1));
        glVertex2f(x + 1,             y - (height / 2 - 1));

        if (grey == false)
            glColor3f(0.0f, 0.95f, 0.0f);
        glVertex2f(x + 1,             y - (height / 2 - 1));
        glVertex2f(x + 1 + bar_width, y - (height / 2 - 1));
        if (grey == false)
            glColor3f(0.0f, 0.3f, 0.0f);
        glVertex2f(x + 1 + bar_width, y - (height - 1));
        glVertex2f(x + 1,             y - (height - 1));
    glEnd();

    // Border
    glPolygonMode(GL_FRONT_AND_BACK, GL_LINE);
    if (grey == false)
        glColor3f(1.0f, 1.0f, 1.0f);
    glBegin(GL_QUADS);
        glVertex2f(x,         y);
        glVertex2f(x + width, y);
        glVertex2f(x + width, y - height);
        glVertex2f(x,         y - height);
    glEnd();
    glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);

    if (grey)
        glColor3f(1.0f, 1.0f, 1.0f);
}

void DrawGradientBox(
    uint x, uint y,
    uint width, uint height,
    bool skip_border = false,
    bool grey_border = false)
{
    // Gradient
    glBegin(GL_QUADS);
        glColor3f(0.0f, 0.0f, 0.0f);
        glVertex2f(x,         y);
        glVertex2f(x + width, y);
        glColor3f(0.3f, 0.3f, 0.3f);
        glVertex2f(x + width, y - height);
        glVertex2f(x,         y - height);
    glEnd();

    // Border
    if (skip_border == false)
    {
        glPolygonMode(GL_FRONT_AND_BACK, GL_LINE);
        if (grey_border)
            glColor3f(0.5f, 0.5f, 0.5f);
        else
            glColor3f(1.0f, 1.0f, 1.0f);
        glBegin(GL_QUADS);
            glVertex2f(x,         y);
            glVertex2f(x + width, y);
            glVertex2f(x + width, y - height);
            glVertex2f(x,         y - height);
        glEnd();
        glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
    }

    glColor3f(1.0f, 1.0f, 1.0f);
}

uint DrawLeftTruncatedString(
    uint x,
    uint y,
    const char *str,
    uint32 color,
    uint width)
{
    // Draw a string truncated on the left to fit into the given box. Return the offset
    // at which we did start drawing

    // Compute how much we need to truncate at the start
    const size_t len = std::strlen(str);
    width /= 6;
    const uint offs = (len > width) ? len - width + 2 : 0;
    str = str + offs;

    // String
    g_font.DrawStringFixed6x12((offs == 0) ? x : x + 12, y, str, color);

    // Draw compact ellipsis (2 instead of 3 characters)
    if (offs != 0)
    {
        glColor3f(
            float((color & 0x000000FF)      ) / 255.0f,
            float((color & 0x0000FF00) >> 8 ) / 255.0f,
            float((color & 0x00FF0000) >> 16) / 255.0f);

        glBegin(GL_QUADS);
            glVertex2f(x, y + 2);
            glVertex2f(x + 2, y + 2);
            glVertex2f(x + 2, y + 2 + 2);
            glVertex2f(x, y + 2 + 2);

            glVertex2f(x + 4, y + 2);
            glVertex2f(x + 4 + 2, y + 2);
            glVertex2f(x + 4 + 2, y + 2 + 2);
            glVertex2f(x + 4, y + 2 + 2);

            glVertex2f(x + 8, y + 2);
            glVertex2f(x + 8 + 2, y + 2);
            glVertex2f(x + 8 + 2, y + 2 + 2);
            glVertex2f(x + 8, y + 2 + 2);
        glEnd();

        glColor3f(1.0, 1.0f, 1.0f);
    }

    return offs;
}

const char * SecondsToHMS(double seconds)
{
    // Convert seconds into an hours/minutes/seconds string

    const uint hours = uint(seconds) / (60 * 60);
    seconds -= hours * 60 * 60;
    uint minutes = uint(seconds) / 60;
    seconds -= minutes * 60;
    static char time_str[32]; // Not re-entrant
    std::snprintf(time_str, sizeof(time_str), "%ih%im%.1fs", hours, minutes, float(seconds));

    return time_str;
}

void DrawThreadDisplay()
{
    // Stats about running / swapped out threads
    uint running = 0;
    uint swapped_out = 0;
    for (std::vector<ProfileData::Thread>::const_iterator it=g_prof_data.m_threads.begin();
         it!=g_prof_data.m_threads.end();
         it++)
    {
        if ((* it).m_run_state == "Running")
            running++;
        if ((* it).m_swapped_out)
            swapped_out++;
    }
    const uint max_disp_threads = 16;
    char buf[512];
    std::snprintf(buf, sizeof(buf), "%i Threads (%i running, %i swapped out)%s",
        int(g_prof_data.m_threads.size()), running, swapped_out,
        (g_prof_data.m_threads.size() > max_disp_threads) ?
        ", Only 16 most active threads shown" : "");
    g_font.DrawStringFixed6x12(3, InvY(108), buf);

    // Thread times
    std::strncpy(buf, "Live thread CPU time: ", sizeof(buf));
    std::strncat(buf, SecondsToHMS(g_prof_data.m_live_threads_user_time), sizeof(buf));
    std::strncat(buf, " (User) ", sizeof(buf));
    std::strncat(buf, SecondsToHMS(g_prof_data.m_live_threads_system_time), sizeof(buf));
    std::snprintf(
        &buf[std::strlen(buf)], sizeof(buf) - std::strlen(buf), " (System), Ratio %.2f : 1",
        float(g_prof_data.m_live_threads_user_time / g_prof_data.m_live_threads_system_time));
    g_font.DrawStringFixed6x12(g_col_wdh, InvY(108), buf);

    //  Make sure we display the most important threads first
    std::vector<ProfileData::Thread> sorted_threads = g_prof_data.m_threads;
    std::sort(sorted_threads.begin(), sorted_threads.end());

    // Individual thread boxes
    for (uint thread=0; thread<max_disp_threads; thread++)
    {
        const bool valid = thread < g_prof_data.m_threads.size();

        // Box offsets
        const int xoffs = 3 + (thread - (thread % 4)) / 4 * 241;
        const int yoffs = InvY(110) + (thread % 4) * -28;

        ProfileData::Thread prof_thread;
        if (valid)
            prof_thread = sorted_threads[thread];

        // Grey out swapped out threads
        const bool grey_out = valid == false || prof_thread.m_swapped_out;

        // Gradient & box
        DrawGradientBox(xoffs, yoffs, 237, 25, false, grey_out);

        // No actual thread, just draw the box
        if (valid == false)
            continue;

        // Number
        if (grey_out)
            glColor3f(0.5f, 0.5f, 0.5f);
        else
            glColor3f(1.0f, 1.0f, 1.0f);
        std::snprintf(buf, sizeof(buf), "%i", thread);
        g_font.DrawStringFixed6x12(xoffs + 3, yoffs - 11, buf);
        glBegin(GL_LINE_STRIP);
            glVertex2f(xoffs, yoffs - 12);
            glVertex2f(xoffs + 17, yoffs - 12);
            glVertex2f(xoffs + 17, yoffs);
        glEnd();

        // PC / current symbol
        std::strncpy(buf, prof_thread.m_cur_symbol.c_str(), sizeof(buf));
        DrawLeftTruncatedString(xoffs + 3, yoffs - 23, buf, 0xFFFFFFFF, 237 - 25);

        // State & CPU usage
        std::snprintf(buf, sizeof(buf), "%s - CPU: %.1f%%",
            prof_thread.m_run_state.c_str(),
            prof_thread.m_cpu_usage_percentage);
        g_font.DrawStringFixed6x12(xoffs + 21, yoffs - 11, buf);

        // CPU usage bar
        DrawProgressBar(
            xoffs + 26 + std::strlen(buf) * 6,
            yoffs - 3.0f,
            40, 6,
            prof_thread.m_cpu_usage_percentage);

        // Running / stopped icon
        glPolygonMode(GL_FRONT_AND_BACK, GL_LINE);
        if (prof_thread.m_run_state == "Running")
        {
            EnableLineAA();
            if (prof_thread.m_swapped_out)
                glColor3f(0.5f, 0.5f, 0.5f);
            else
                glColor3f(0.0f, 1.0f, 0.0f);
            glBegin(GL_TRIANGLES);
                glVertex3f(237.0f + xoffs - 17.0f, yoffs - 25.0f + 5.0f, 0.0f);
                glVertex3f(237.0f + xoffs - 7.0f,  yoffs - 24.0f / 2.0f, 0.0f);
                glVertex3f(237.0f + xoffs - 17.0f, yoffs - 4.0f,         0.0f);
            glEnd();
            DisableLineAA();
        }
        else
        {
            glColor3f(1.0f, 0.0, 0.0f);
            glBegin(GL_QUADS);
                glVertex3f(237.0f + xoffs - 10.0f, yoffs - 24.0f + 5.0f, 0.0f);
                glVertex3f(237.0f + xoffs - 5.0f,  yoffs - 24.0f + 5.0f, 0.0f);
                glVertex3f(237.0f + xoffs - 5.0f,  yoffs - 11.0f + 5.0f, 0.0f);
                glVertex3f(237.0f + xoffs - 10.0f, yoffs - 11.0f + 5.0f, 0.0f);
                glVertex3f(237.0f + xoffs - 19.0f, yoffs - 24.0f + 5.0f, 0.0f);
                glVertex3f(237.0f + xoffs - 14.0f, yoffs - 24.0f + 5.0f, 0.0f);
                glVertex3f(237.0f + xoffs - 14.0f, yoffs - 11.0f + 5.0f, 0.0f);
                glVertex3f(237.0f + xoffs - 19.0f, yoffs - 11.0f + 5.0f, 0.0f);
            glEnd();
        }
        glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
    }

    glColor3f(1.0f, 1.0f, 1.0f);
}

uint32 GetPercentageColor(float percentage)
{
    // Color coding for percentage values

    assert(percentage >= 0.0f && percentage <= 100.0f);

    if (percentage >= 10.0f)
        return 0xFF00FF00; // Green
    else if (percentage < 1.0f)
        return 0xFF9F9F9F; // Grey
    else
        return 0xFFFFFFFF; // White
}

void DrawFunctionProfile()
{
    char buf[512];
    const uint top = InvY(231);

    // Header
    g_font.DrawStringFixed6x12(3, top, "Hits  Percent   Symbol");

    // Footer / statistics / options
    const float oldest_smp = float(g_prof_data.m_oldest_sample_used);
    std::snprintf(buf, sizeof(buf),
        "Took %i / %i [S]amples (target was idle %.1f%%) in %.2fs (aiming for 0.5s)\n"
        "Using %i in profile ([A]iming for >= %i, [R]eset), up to %im%.1fs old",
        g_prof_data.m_num_smp_collected,
        g_num_smp_target,
        100.0f - std::min(100.0f,
            float(g_prof_data.m_num_smp_collected) / float(g_num_smp_target) * 100.0f),
        float(g_prof_data.m_smp_collection_interval),
        g_prof_data.m_num_smp_collected_total,
        g_num_smp_profile,
        int(oldest_smp) / 60,
        oldest_smp - 60.0f * float(int(oldest_smp) / 60));
    g_font.DrawStringFixed6x12(5, 13, buf);

    // Gradient
    DrawGradientBox(3, top, g_col_wdh - 6, top - 3, true);

#ifndef NDEBUG
    uint sample_sum = 0;
    for (std::vector<ProfileData::Function>::const_iterator it=g_prof_data.m_functions.begin();
         it!=g_prof_data.m_functions.end();
         it++)
    {
        sample_sum += (* it).m_hits;
    }
    assert(sample_sum == g_prof_data.m_num_smp_collected_total);
#endif // NDEBUG

    // Function list
    float percent_total = 0.0f;
    uint bars_inserted = 0;
    float high_p = 0.0f;
    if (g_prof_data.m_functions.empty() == false)
    {
        high_p = float(g_prof_data.m_functions[0].m_hits) /
            float(g_prof_data.m_num_smp_collected_total) * 100.0f;
    }
    const uint max_funcs = top / 10 - 2;
    for (uint cur_func=0;
         cur_func<std::min(max_funcs - bars_inserted, uint(g_prof_data.m_functions.size()));
         cur_func++)
    {
        const ProfileData::Function& func = g_prof_data.m_functions[cur_func];
        uint yoffs = top - 13 - (cur_func + bars_inserted) * 10;
        const float percentage =
            float(func.m_hits) / float(g_prof_data.m_num_smp_collected_total) * 100.0f;

        // Draw separator line at certain percentages, don't bother if there's nothing over the line
        if (((percentage < 10.0f &&  bars_inserted                     == 0 && (high_p >= 10.0f)) ||
             (percentage < 1.0f  && (bars_inserted + (high_p < 10.0f)) == 1 && (high_p >= 1.0f))) &&
              cur_func > 0)
        {
            bars_inserted++;
            glBegin(GL_LINES);
                glVertex2f(3.0f, yoffs + 5.0f);
                glVertex2f(443, yoffs + 5.0f);
                glVertex2f(443, yoffs + 2.0f);
                glVertex2f(443, yoffs + 9.0f);
                glVertex2f(469, yoffs + 5.0f);
                glVertex2f(g_col_wdh - 3.0f, yoffs + 5.0f);
                glVertex2f(469, yoffs + 2.0f);
                glVertex2f(469, yoffs + 9.0f);
            glEnd();
            std::snprintf(buf, sizeof(buf), "%i%%", int(percent_total));
            g_font.DrawStringFixed6x12(448, yoffs, buf);
            yoffs -= 10;
        }

        percent_total += percentage;

        // Highlight currently selected function
        if (cur_func == g_cur_func_sel)
        {
            // Gradient
            glBegin(GL_QUADS);
                glColor3f(0.6f, 0.0f, 0.0f);
                glVertex2f(3.0f, yoffs);
                glColor3f(0.2f, 0.0f, 0.0f);
                glVertex2f(3.0f, yoffs + 11.0f);
                glColor3f(0.2f, 0.0f, 0.0f);
                glVertex2f(g_col_wdh - 3.0f, yoffs + 11.0f);
                glColor3f(0.6f, 0.0f, 0.0f);
                glVertex2f(g_col_wdh - 3.0f, yoffs);
            glEnd();
            glColor3f(1.0f, 1.0f, 1.0f);

            // Line to the top of the panel on the right side
            glBegin(GL_LINE_STRIP);
                glVertex2f(g_col_wdh - 3.0f, yoffs + 5.0f);
                glVertex2f(g_col_wdh - 2.0f, yoffs + 5.0f);
                glVertex2f(g_col_wdh - 2.0f, top - 13 + 5);
                glVertex2f(g_col_wdh - 0.0f, top - 13 + 5);
            glEnd();
        }

        // Table entry
        uint32 color;
        if (strcmp(g_symbol->SymbolIDToName(func.m_sym_id),
                   g_symbol->GetUnresolvedSymbolName()) == 0)
        {
            // Unresolved symbols are red
            color = 0xFF0000FF;
            // Also show module information
            std::snprintf(buf, sizeof(buf), "%s from %s",
                g_symbol->SymbolIDToName(func.m_sym_id),
                g_symbol->SymbolIDToModule(func.m_sym_id));
        }
        else
        {
            color = GetPercentageColor(percentage);
            std::strncpy(buf, g_symbol->SymbolIDToName(func.m_sym_id), sizeof(buf));
        }
        DrawLeftTruncatedString(99, yoffs, buf, color, g_col_wdh - 99);
        std::snprintf(buf, sizeof(buf), "%5i %4.1f%%",
            func.m_hits,
            percentage);
        g_font.DrawStringFixed6x12(3, yoffs, buf, color);

        // Percentage bar 
        DrawProgressBar(71, yoffs + 8, 20, 6, percentage, percentage < 1.0f);
    }

    // Table
    glBegin(GL_LINES);
        glVertex2f(3.0f, top - 1.0f);
        glVertex2f(g_col_wdh - 3.0f, top - 1.0f);
        glVertex2f(5.0f + 5.0f * 6.0f, top + 9.0f);
        glVertex2f(5.0f + 5.0f * 6.0f, 24.0f);
        glVertex2f(5.0f + 15.0f * 6.0f, top + 9.0f);
        glVertex2f(5.0f + 15.0f * 6.0f, 24.0f);
    glEnd();

    // Additional statistics in the header
    std::snprintf(buf, sizeof(buf), "top %.1f%%", percent_total);
    g_font.DrawStringFixed6x12(160, top, buf);
    float unresolved_percentage =
        float(g_prof_data.m_samples_unresolved) /
        float(g_prof_data.m_num_smp_collected_total) * 100.0f;
    if (std::isnan(unresolved_percentage))
        unresolved_percentage = 0.0f;
    std::snprintf(buf, sizeof(buf), "%.1f%% unresolved", unresolved_percentage);
    g_font.DrawStringFixed6x12(236, top, buf,
        (unresolved_percentage >= 10.0f) ? 0xFF0000FF : 0xFFFFFFFF);
    std::snprintf(buf, sizeof(buf), "%.1f%% symcache hits", g_symbol->GetCacheHitPercentage());
    g_font.DrawStringFixed6x12(349, top, buf);
}

void DrawCallTreeAndSourceViewBackground()
{
    const uint top = InvY(231);

    // Gradient
    DrawGradientBox(g_col_wdh, top, g_col_wdh - 6, top - 3, true);

    // Header separator line
    glBegin(GL_LINES);
        glVertex2f(g_col_wdh, top - 1.0f);
        glVertex2f(2 * g_col_wdh - 6.0f, top - 1.0f);
    glEnd();

    // Highlight to join up with the line from the selected function
    glColor3f(0.5f, 0.0f, 0.0f);
    glBegin(GL_QUADS);
        glColor3f(0.6f, 0.0f, 0.0f);
        glVertex2f(g_col_wdh, top - 13);
        glColor3f(0.2f, 0.0f, 0.0f);
        glVertex2f(g_col_wdh, top - 13 + 11.0f);
        glColor3f(0.2f, 0.0f, 0.0f);
        glVertex2f(2 * g_col_wdh - 6.0f, top - 13 + 11.0f);
        glColor3f(0.6f, 0.0f, 0.0f);
        glVertex2f(2 * g_col_wdh - 6.0f, top - 13);
    glEnd();
    glColor3f(1.0f, 1.0f, 1.0f);
}

void DrawCallTreeAndSourceViewFunction(uint descendants_cnt = uint(-1))
{
    const uint top = InvY(231);

    // Current function
    if (g_cur_func_sel >= g_prof_data.m_functions.size())
        return;
    const ProfileData::Function& func = g_prof_data.m_functions[g_cur_func_sel];

    // Descendant statistics
    const uint total_cnt              = func.m_hits + descendants_cnt;
    const float own_percentage        = float(func.m_hits) / float(total_cnt) * 100.0f;
    const float descendant_percentage = float(descendants_cnt) / float(total_cnt) * 100.0f;
    const float total_percentage      = float(total_cnt) /
                                        float(g_prof_data.m_num_smp_collected_total) * 100.0f;

    char buf[512];
    if (descendants_cnt != uint(-1))
    {
        // Repeat function name, add descendant statistics
        std::snprintf(
            buf, sizeof(buf),
            "%s - O: %.1f%%     (%i) | D: %.1f%%     (%i) | T:%.1f%%     (%i)",
            g_symbol->SymbolIDToName(func.m_sym_id),
            own_percentage,
            func.m_hits,
            descendant_percentage,
            descendants_cnt,
            total_percentage,
            total_cnt);
    }
    else
    {
        // Repeat function name and hit count, add module name
        std::snprintf(buf, sizeof(buf),
            "%s from %s - (%i)",
            g_symbol->SymbolIDToName(func.m_sym_id),
            g_symbol->SymbolIDToModule(func.m_sym_id),
            func.m_hits);
    }

    // Draw information. Prefer to cut off the repeated function name at the left side rather than
    // the actual new information on the right
    const uint xoffs = g_col_wdh + 2;
    const uint yoffs = top - 13;
    const uint trunc = DrawLeftTruncatedString(xoffs, yoffs, buf,
        g_symbol->SymbolIDToName(func.m_sym_id) == g_symbol->GetUnresolvedSymbolName() ?
            0xFF0000FF : 0xFF00FF00, g_col_wdh - 5);

    // Add progress bars for the descendant statistics
    if (descendants_cnt != uint(-1))
    {
        const char *bar_loc_own   = std::strstr(&buf[trunc],      "     ");
        const char *bar_loc_desc  = std::strstr(bar_loc_own + 1,  "     ");
        const char *bar_loc_total = std::strstr(bar_loc_desc + 1, "     ");
        for (uint i=0; i<3; i++)
        {
            const char *bar_loc = NULL;
            float percentage;
            switch (i)
            {
                case 0: bar_loc = bar_loc_own;   percentage = own_percentage;        break;
                case 1: bar_loc = bar_loc_desc;  percentage = descendant_percentage; break;
                case 2: bar_loc = bar_loc_total; percentage = total_percentage;      break;
            }
            DrawProgressBar(
                xoffs + (bar_loc - &buf[trunc]) * 6 + 3 + ((trunc > 0) ? 12 : 0),
                yoffs + 8,
                20, 6,
                percentage);
        }
    }
}

void DrawCallTree()
{
    char buf[512];
    const uint top = InvY(231);

    DrawCallTreeAndSourceViewBackground();

    // Header
    //
    // TODO: The merged symbol stuff should really be in the function profile
    std::snprintf(buf, sizeof(buf),
        "Call Tree ([M]ode: %s) | Mer[G]e symbol into caller (%i Merged, [C]lear)",
        g_call_tree_incoming ? "Incoming" : "Outgoing", int(g_prof_data.m_merge_sym.size()));
    g_font.DrawStringFixed6x12(g_col_wdh, top, buf);

    // Get call tree for the current function
    if (g_cur_func_sel >= g_prof_data.m_functions.size())
        return;
    const ProfileData::Function& func = g_prof_data.m_functions[g_cur_func_sel];
    const CallTree::Node *tree = func.m_incoming.GetRoot();

    // Capture failures?
    const float failure_percentage =
        float(func.m_stack_capture_failures) / float(func.m_hits) * 100.0f;
    const bool capture_failure_notice = func.m_hits > 10 && failure_percentage > 5.0f;
    if (capture_failure_notice)
    {
        // Seems like we can't do stack traversal for this function, display some
        // helpful advice about frame pointers
        std::snprintf(
            buf, sizeof(buf),
            "%.1f%% stack capture failures, compile with -fno-omit-frame-pointer",
            failure_percentage);
        g_font.DrawStringFixed6x12(g_col_wdh + 2, 3, buf, 0xFF0000FF);
    }

    // Are we asked to show the outgoing call tree instead?
    CallTree outgoing;
    uint root_children_hit_count = 0;
    if (g_call_tree_incoming == false)
    {
        // TODO: We actually compute the outgoing tree from the incoming ones right here. It's
        //       preferable to do it just for the selected function, but maybe we don't need to
        //       do it quite at 30FPS...

        // Compute the outgoing call tree from the incoming ones of all other functions
        for (std::vector<ProfileData::Function>::const_iterator it=g_prof_data.m_functions.begin();
             it!=g_prof_data.m_functions.end();
             it++)
        {
            if ((* it).m_sym_id == func.m_sym_id)
                continue;

            (* it).m_incoming.ExtractOutgoingCallArcs(func.m_sym_id, (* it).m_sym_id, &outgoing);
        }

        outgoing.SortSiblingLists();
        tree = outgoing.GetRoot();

        // Compute the sum of the hit count of all root nodes, needed for statistic in the
        // outgoing tree case
        uint32 cur_node = 0;
        if (tree != NULL)
        {
            while (cur_node != uint32(-1))
            {
                root_children_hit_count += tree[cur_node].m_hits;
                cur_node = tree[cur_node].m_sibling;
            }
        }
    }

    // Also display the descendant hit count for outgoing trees
    DrawCallTreeAndSourceViewFunction(g_call_tree_incoming ? uint(-1) : root_children_hit_count);

    if (tree == NULL)
        return;

    // Display tree. Draw function names and hit count statistics, connect nodes with
    // tree lines if they are parent & child but not directly adjacent vertically
    std::stack<uint32> st;
    st.push(0);
    std::stack<int> st_line; // Keep track which display line our parent is in
    st_line.push(0);
    uint32 cur_node;
    uint line = 1; // Current display line
    bool skip_count = tree[0].m_hits == func.m_hits;
    float percentage = 0.0f;
    while (st.empty() == false)
    {
        cur_node = st.top();
        st.pop();
        while (cur_node != uint32(-1))
        {
            // Stop drawing but keep processing stack entries after we're off-screen. Still
            // might need to draw tree lines to those nodes
            const uint max_lines = top / 10;
            if (line < max_lines - (capture_failure_notice ? 1 : 0))
            {
                const bool is_unknown =
                    std::strcmp(g_symbol->SymbolIDToName(tree[cur_node].m_sym_id),
                                g_symbol->GetUnresolvedSymbolName()) == 0;

                // Little connecting line from the symbol to the tree line. Don't need to
                // draw it if we're not having a line because we're adjacent to the parent,
                // except when this is only the first sibling
                if (line - st_line.top() > 1 ||
                    tree[cur_node].m_sibling != uint32(-1))
                {
                    glBegin(GL_LINES);
                        glVertex2f(g_col_wdh + 5 + st.size() * 6, top - 8 - line * 10);
                        glVertex2f(g_col_wdh + 7 + st.size() * 6, top - 8 - line * 10);
                    glEnd();
                }

                // Name
                char sym_name[512];
                std::snprintf(sym_name, sizeof(sym_name), is_unknown ? "%s from %s" : "%s",
                    g_symbol->SymbolIDToName(tree[cur_node].m_sym_id),
                    g_symbol->SymbolIDToModule(tree[cur_node].m_sym_id));

                // Show statistics about number of samples going through the current tree node
                if (g_call_tree_incoming)
                {
                    // Based on percentage of the root
                    percentage = float(tree[cur_node].m_hits) / float(func.m_hits) * 100.0f;
                }
                else
                {
                    // Based on the percentage of the sum of all root children. Only applies
                    // to root children, just keep coloring for the entire subtree
                    if (st.size() == 0)
                    {
                        percentage = float(tree[cur_node].m_hits) /
                                     float(root_children_hit_count) * 100.0f;
                        skip_count = false;
                    }
                    else
                    {
                        // We only have useful statistics for the first level of callees
                        skip_count = true;
                    }
                }
                // Hit count
                std::snprintf(
                    buf, sizeof(buf),
                    skip_count ? "%s" : "%s - %.1f%%     (%i)",
                    sym_name,
                    percentage,
                    tree[cur_node].m_hits);
                // Unresolved symbols are red, normal percentage coloring otherwise
                uint32 color = is_unknown ? 0xFF0000FF : GetPercentageColor(percentage);
                // Draw actual symbol name and hit count
                const uint xoffs = g_col_wdh + 2 + (st.size() + 1) * 6;
                const uint yoffs = top - 13 - line * 10; 
                const uint trunc = DrawLeftTruncatedString(
                    xoffs, yoffs, buf, color, g_col_wdh - (st.size() + 1) * 6 - 6);
                // Progress bar
                {
                    const char *bar_loc =
                        std::strstr(&buf[trunc], "    "); // Bar location in string
                    if (bar_loc != NULL)
                    {
                        DrawProgressBar(
                            xoffs + (bar_loc - &buf[trunc]) * 6 + 3 + ((trunc > 0) ? 12 : 0),
                            yoffs + 8,
                            20, 6,
                            percentage,
                            percentage < 1.0f);
                    }
                }
            }

            // Vertical coordinates for the tree line, clip at the bottom of the display. Also
            // make sure we don't draw over any notice
            const int y1 = std::max(3 + (capture_failure_notice ? 12 : 0),
                int(top) - 8 - int(line) * 10);
            const int y2 = std::max(3 + (capture_failure_notice ? 12 : 0),
                int(top) - 13 - int(st_line.top()) * 10 - 1);

            if (y1 != y2 &&                             // Not fully clipped off-screen?
                line - st_line.top() > 1 &&             // Not directly adjacent to parent?
                tree[cur_node].m_sibling == uint32(-1)) // Only need to draw at last sibling
            {
                glBegin(GL_LINES);
                    glVertex2f(g_col_wdh + 4 + st.size() * 6, y1);
                    glVertex2f(g_col_wdh + 4 + st.size() * 6, y2);
                glEnd();
            }

            // Traverse depth-first
            skip_count = false;
            if (tree[cur_node].m_child != uint32(-1))
            {
                st.push(tree[cur_node].m_sibling);
                st_line.push(line);

                // We can skip displaying the hit count if the child has the same
                if (tree[cur_node].m_child != uint32(-1))
                    if (tree[tree[cur_node].m_child].m_hits == tree[cur_node].m_hits)
                        skip_count = true;

                cur_node = tree[cur_node].m_child;
            }
            else
                cur_node = tree[cur_node].m_sibling;

            // We've drawn one more line
            line++;
        }

        st_line.pop();
    }
}

class SourceLineLookup
{
public:
    SourceLineLookup(const char *target_executable_path) :
        m_cache_hit(0),
        m_cache_miss(0)
    {
        // We search the target program's directory by default, add at the end
        std::string target_path = std::string(target_executable_path);
        target_path.erase(target_path.rfind("/"), target_path.length());

        // Fetch search path from the environment
        // TODO: Add support for wildcards
        const char * rsvp_src_path = getenv("RSVP_SRC_PATH");
        if (rsvp_src_path != NULL)
        {
            while ((* rsvp_src_path) != '\0')
            {
                // Find colon separator or end of string
                const char *end = std::strchr(rsvp_src_path, ':');
                if (end == NULL)
                    end = rsvp_src_path + std::strlen(rsvp_src_path);

                // Extract
                m_search_path.push_back(std::string(rsvp_src_path, end - rsvp_src_path));

                // Remove trailing slash
                if ((* --m_search_path.back().end()) == '/')
                    m_search_path.back().erase(--m_search_path.back().end());

                // Relative -> absolute (assume they're relative to the target executable)
                if (m_search_path.back()[0] == '.')
                    m_search_path.back().insert(0, target_path + "/");

                // Advance to the next path
                rsvp_src_path = end + 1;
            }
        }

        m_search_path.push_back(target_path);

#ifdef DBG_PRINT_PATH
        for (std::vector<std::string>::const_iterator it=m_search_path.begin();
             it!=m_search_path.end();
             it++)
        {
            std::printf("%s\n", (* it).c_str());
        }
#endif // DBG_PRINT_PATH
    }

    const char * Lookup(const SymSampleStats::SourceLocation& line)
    {
        // Look in the cache
        std::map<SymSampleStats::SourceLocation, std::string>::iterator it = m_cache.find(line);
        if (it != m_cache.end())
            m_cache_hit++; // Hit
        else
        {
            // TODO: We should really handle all I/O in another thread and display (Not Available)
            //       while data is being fetched

            // Miss
            m_cache_miss++;
            it = m_cache.insert(std::map<SymSampleStats::SourceLocation, std::string>::value_type
                (line, std::string())).first;

            // Locate file
            char file_name[1024];
            std::vector<std::string>::const_iterator it_path;
            for (it_path=m_search_path.begin();
                 it_path!=m_search_path.end();
                 it_path++)
            {
                std::snprintf(file_name, sizeof(file_name), "%s/%s",
                    (* it_path).c_str(),
                    g_symbol->FileIDToName(line.m_file_name_id));
                struct stat s;
                if (stat(file_name, &s) == 0)
                    break;
            }

            (* it).second = "(Not Available)"; // Error default

            // Did we find it?
            if (it_path != m_search_path.end())
            {
                // Look for the requested line
                std::FILE *file = std::fopen(file_name, "r");
                uint i;
                char buf[512];
                char *line_buf = buf;
                for (i=0; i<line.m_line_number; i++)
                    if (std::fgets(line_buf, sizeof(buf), file) == NULL)
                        break;
                std::fclose(file);

                // Did we reach it?
                if (i == line.m_line_number)
                {
                    // Eat leading white space
                    while ((* line_buf) == ' ' || (* line_buf) == '\t')
                        line_buf++;

                    // Store
                    (* it).second = std::string(line_buf);
                }
            }
        }

        return (* it).second.c_str();
    }

    size_t GetNumSearchPaths() const { return m_search_path.size() - 1; }

    float GetCacheHitPercentage() const
    {
        return float(m_cache_hit) / float(m_cache_hit + m_cache_miss) * 100.0f;
    }

protected:
    // Cache
    uint m_cache_hit;
    uint m_cache_miss;
    std::map<SymSampleStats::SourceLocation, std::string> m_cache;

    std::vector<std::string> m_search_path;

};

std::auto_ptr<SourceLineLookup> g_source;

void DrawSourceView()
{
    char buf[512];
    const uint top = InvY(231);

    DrawCallTreeAndSourceViewBackground();
    DrawCallTreeAndSourceViewFunction();

    // Header
    if (g_source->GetNumSearchPaths() == 0)
    {
        std::strncpy(
            buf,
            "Source View | Use RSVP_SRC_PATH to specify additional source file locations",
            sizeof(buf));
    }
    else
    {
        std::snprintf(buf, sizeof(buf),
            "Source View | Searching target dir. and %i locations specified by RSVP_SRC_PATH",
            int(g_source->GetNumSearchPaths()));
    }
    g_font.DrawStringFixed6x12(g_col_wdh, top, buf);

    // Current function
    if (g_cur_func_sel >= g_prof_data.m_functions.size())
        return;
    const ProfileData::Function& func = g_prof_data.m_functions[g_cur_func_sel];

    // Our source location map is already sorted by file name and then by lines in ascending order.
    // We now need to sort the files based on their total hit count
    uint unresolved_count = 0;
    std::vector<std::pair<uint, SymSampleStats::SourceLocation> > source_files;
    {
        uint16 cur_source_file = uint16(-1);
        uint hit_count = 0;
        std::map<SymSampleStats::SourceLocation, uint>::const_iterator it_start;
        for (std::map<SymSampleStats::SourceLocation, uint>::const_iterator it=
                 func.m_source_hits.begin();
             it!=func.m_source_hits.end();
             it++)
        {
            // Different file?
            if ((* it).first.m_file_name_id != cur_source_file)
            {
                // Don't add for the first element
                if (cur_source_file != uint16(-1))
                {
                    source_files.push_back(std::pair<uint, SymSampleStats::SourceLocation>
                        (hit_count, (* it_start).first));
                    // Record unresolved hit count
                    if (std::strcmp(g_symbol->FileIDToName((* it_start).first.m_file_name_id),
                                    g_symbol->GetUnresolvedSymbolName()) == 0)
                    {
                        unresolved_count = hit_count;
                    }
                }
                hit_count = 0;
                cur_source_file = (* it).first.m_file_name_id;
                it_start = it; // Need to keep the start of the run
            }

            // Accumulate hit count for the current file
            hit_count += (* it).second;
        }

        // Last run
        source_files.push_back(std::pair<uint, SymSampleStats::SourceLocation>
            (hit_count, (* it_start).first));
        // Record unresolved hit count
        if (std::strcmp(g_symbol->FileIDToName((* it_start).first.m_file_name_id),
                        g_symbol->GetUnresolvedSymbolName()) == 0)
        {
            unresolved_count = hit_count;
        }

        // Sort
        std::sort(source_files.begin(), source_files.end());
    }

    // Missing line-level debug information?
    const float failure_percentage = float(unresolved_count) / float(func.m_hits) * 100.0f;
    const bool symbol_failure_notice = func.m_hits > 10 && failure_percentage > 5.0f;
    if (symbol_failure_notice)
    {
        // Seems like we can't retrieve line-level information for this function, display some
        // helpful advice about dsymutil
        std::snprintf(
            buf, sizeof(buf),
            "%.1f%% failures when looking up line-level debug information, use 'dsymutil'",
            failure_percentage);
        g_font.DrawStringFixed6x12(g_col_wdh + 2, 3, buf, 0xFF0000FF);
    }

    // Draw lines in ascending order, sorted by source files, themselves sorted by hit count
    uint line = 1; // Current display line
    const uint max_lines = top / 10 - (symbol_failure_notice ? 1 : 0);
    for (std::vector<std::pair<uint, SymSampleStats::SourceLocation> >::const_reverse_iterator it=
             source_files.rbegin();
         it!=source_files.rend();
         it++)
    {
        // Source file name and statistics
        const float percentage = float((* it).first) / float(func.m_hits) * 100.0f;
        std::snprintf(buf, sizeof(buf), "Hits   Percent   Line  %s - %.1f%%     (%i)",
            g_symbol->FileIDToName((* it).second.m_file_name_id),
            percentage,
            (* it).first);
        g_font.DrawStringFixed6x12(
            g_col_wdh + 2,
            top - 13 - line * 10,
            buf,
            GetPercentageColor(percentage));
        const char * bar_loc = std::strstr(buf, "     ");
        DrawProgressBar(
            g_col_wdh + 2 + (bar_loc - buf) * 6 + 2,
            top - 13 - line * 10 + 8,
            20, 6,
            percentage,
            percentage < 1.0f);

        const uint header_line = line;
        if (++line >= max_lines) // Reached bottom of screen?
            break;

        // Lines for that source file
        std::map<SymSampleStats::SourceLocation, uint>::const_iterator it_start =
            func.m_source_hits.find((* it).second);
        assert(it_start != func.m_source_hits.end());
        while (it_start != func.m_source_hits.end() &&
               (* it_start).first.m_file_name_id == (* it).second.m_file_name_id)
        {
            // Line number and statistics
            const float percentage = float((* it_start).second) / float(func.m_hits) * 100.0f;
            std::snprintf(buf, sizeof(buf),
                (percentage == 100.0) ? "%5i %4.0f%%     %5i %s" : "%5i %4.1f%%     %5i %s",
                (* it_start).second,
                percentage,
                (* it_start).first.m_line_number,
                g_source->Lookup((* it_start).first));
            buf[78] = '\0';
            g_font.DrawStringFixed6x12(
                g_col_wdh + 2 + 6,
                top - 13 - line * 10,
                buf,
                GetPercentageColor(percentage));
        DrawProgressBar(
            g_col_wdh + 2 + 74,
            top - 13 - line * 10 + 8,
            20, 6,
            percentage,
            percentage < 1.0f);

            it_start++;

            if (++line >= max_lines) // Reached bottom of screen?
                break;
        }

        // Vertical table lines
        {
            const uint y_start = top - 14 - (header_line - 1) * 10;
            const uint y_end   = top - 13 - (line        - 1) * 10;
            glBegin(GL_LINES);
                glVertex2f(g_col_wdh + 40,  y_start);
                glVertex2f(g_col_wdh + 40,  y_end);
                glVertex2f(g_col_wdh + 100, y_start);
                glVertex2f(g_col_wdh + 100, y_end);
                glVertex2f(g_col_wdh + 136, y_start);
                glVertex2f(g_col_wdh + 136, y_end);
            glEnd();
        }

        if (++line >= max_lines) // Reached bottom of screen?
            break;
    }

    // The sorting and grouping code above is a bit tricky, double check we didn't lose any
    // locations or hits in the process
#ifndef NDEBUG
    uint total_count = 0;
    uint items = 0;
    for (std::vector<std::pair<uint, SymSampleStats::SourceLocation> >::const_reverse_iterator it=
             source_files.rbegin();
         it!=source_files.rend();
         it++)
    {
        std::map<SymSampleStats::SourceLocation, uint>::const_iterator it_start =
            func.m_source_hits.find((* it).second);
        uint file_count = 0;
        while (it_start != func.m_source_hits.end() &&
               (* it_start).first.m_file_name_id == (* it).second.m_file_name_id)
        {
            total_count += (* it_start).second;
            file_count  += (* it_start).second;
            items++;
            it_start++;
        }
        assert(file_count == (* it).first);
    }
    assert(total_count == func.m_hits);
    assert(items == func.m_source_hits.size());
#endif // NDEBUG
}

void DrawCPUUsage()
{
    // Compute total CPU usage by all threads of the task
    float cpu_total = 0.0f;
    for (std::vector<ProfileData::Thread>::const_iterator it=g_prof_data.m_threads.begin();
         it!=g_prof_data.m_threads.end();
         it++)
    {
        cpu_total += (* it).m_cpu_usage_percentage;
    }

    // CPU usage text
    char buf[512];
    std::snprintf(buf, sizeof(buf),
        "CPU %.1f%% (normalized %.1f%%), SysCalls Unix: %i/s Mach: %i/s",
        cpu_total,
        cpu_total / float(g_prof_data.m_num_cpus),
        g_prof_data.m_tei.syscalls_unix,
        g_prof_data.m_tei.syscalls_mach);
    g_font.DrawStringFixed6x12(3, InvY(12), buf);

    // CPU usage bar
    DrawProgressBar(3, InvY(14), g_col_wdh - 7, 10, cpu_total / float(g_prof_data.m_num_cpus));
}

std::string PrintBytesHumanReadable(uint64 bytes)
{
    // Convert byte count into more compact and readable KB / MB / GB string

    char buf[64];

    if (bytes < 1024)
        std::snprintf(buf, sizeof(buf), "%iB", int(bytes));
    else if (bytes < 1024 * 1024)
        std::snprintf(buf, sizeof(buf), "%.1fKB", float(double(bytes) / 1024.0));
    else if (bytes < 1024 * 1024 * 1024)
        std::snprintf(buf, sizeof(buf), "%.1fMB", float(double(bytes) / 1024.0 / 1024.0));
    else
        std::snprintf(buf, sizeof(buf), "%.2fGB", float(double(bytes) / 1024.0 / 1024.0 / 1024.0));

    return std::string(buf);
}

void DrawLabelledLineGraph(
    std::vector<uint64>& data,
    uint x,
    uint y,
    uint width,
    uint height,
    uint num_lbl,
    uint& scrollx_inout)
{
    // Draw a graph with num_lbl moving labels and legend from the byte values in data at x, y

    char buf[32];

    // Graph data
    uint64 graph_min = std::numeric_limits<uint64>::max();
    uint64 graph_max = 0;
    for (std::vector<uint64>::const_iterator it=data.begin(); it!=data.end(); it++)
    {
        graph_max = std::max(graph_max, (* it));
        graph_min = std::min(graph_min, (* it));
    }
    if (data.empty())
        graph_min = 0;
    const uint64 nonzero_graph_max = (graph_max == 0) ? 1 : graph_max;
    const double scale_offset = nonzero_graph_max  * 0.075;
    const double scale_factor = (height - 2.0) * (1.0 / (nonzero_graph_max  + scale_offset * 2));
    const float yoffs = 1.0f + y - height;

    // Legend
    {
        // Max
        const std::string max_str = PrintBytesHumanReadable(graph_max).c_str();
        g_font.DrawStringFixed6x12(
            x + width - 44 + (7 - max_str.length()) * 3, y - 11, max_str.c_str());
        g_font.DrawStringFixed6x12(x + width - 44, y - 18, "  max");
        // Middle
        const std::string mid_str = PrintBytesHumanReadable((graph_min + graph_max) / 2).c_str();
        g_font.DrawStringFixed6x12(
            x + width - 44 + (7 - mid_str.length()) * 3, y - height / 2 - 5, mid_str.c_str());
        // Min
        const std::string min_str = PrintBytesHumanReadable(graph_min).c_str();
        g_font.DrawStringFixed6x12(
            x + width - 44 + (7 - min_str.length()) * 3, y - height + 1, min_str.c_str());
        g_font.DrawStringFixed6x12(x + width - 44, y - height + 10, "  min");
    }
    glBegin(GL_LINE_STRIP);
        glVertex2f(x, y);
        glVertex2f(x + width, y);
        glVertex2f(x + width, y - height);
        glVertex2f(x, y - height);
    glEnd();
    width -= 48; // Part taken by the legend

    // Box
    DrawGradientBox(x, y, width, height);

    // Handle scrolling. Once there's enough data for the graph to overflow
    // on the right edge, we'll remove data on the left and scroll the data
    // and the label
    while (data.size() > width)
    {
        data.erase(data.begin());
        scrollx_inout++;
    }
    scrollx_inout = scrollx_inout % (width / (num_lbl + 1));

    // Line
    glColor3f(0.0f, 1.0f, 0.0f);
    glBegin(GL_LINE_STRIP);
        uint xstep = 0;
        for (std::vector<uint64>::const_iterator it=data.begin(); it!=data.end(); it++, xstep++)
        {
            glVertex2f(
                float(x) + 1.0f + float(xstep),
                yoffs + ((* it) + scale_offset) * scale_factor);
        }
    glEnd();
    glColor3f(1.0f, 1.0f, 1.0f);

    // Labels
    for (uint i=1; i<num_lbl + 2; i++)
    {
        // Position of current label
        uint xpos = (width / (num_lbl + 1)) * i - scrollx_inout;
        if (i == 1 && xpos >= data.size() && data.empty() == false)
            xpos = data.size() - 1; // Make first label track line till we hit the first spot
        if (xpos < data.size())
        {
            // Label line
            const bool top_label = (data[xpos] + scale_offset) * scale_factor < height / 2;
            glBegin(GL_LINES);
                if (top_label)
                    glVertex2f(float(x) + 1.0f + float(xpos), yoffs + height - 1.0f - 12.0f);
                else
                    glVertex2f(float(x) + 1.0f + float(xpos), yoffs - 1.0f + 12.0f);
                glVertex2f(
                    float(x) + 1.0f + float(xpos),
                    yoffs + (data[xpos] + scale_offset) * scale_factor +
                    (top_label ? 3.0f : -3.0f));
            glEnd();

            // Text
            std::strncpy(buf, PrintBytesHumanReadable(data[xpos]).c_str(), sizeof(buf));
            const int centerx =
                (uint) (float(std::strlen(buf)) / 2.0f * 6.0f);
            const int fontx = std::max(int(x) + 3, std::min(
                int(x + width) - (2 + centerx * 2), int(x) + 1 + int(xpos) - centerx));
            if (top_label)
                g_font.DrawStringFixed6x12(fontx, yoffs + height - 12.0f, buf);
            else
                g_font.DrawStringFixed6x12(fontx, yoffs, buf);
        }
    }
}

void DrawMemoryProfile()
{
    // Memory usage text
    char buf[512];
    std::snprintf(buf, sizeof(buf),
        "MEM %.1fMB (%.1f%% of %.1fGB), Page Faults: %i/s Ins: %i/s CoW: %i/s",
        float(double(g_prof_data.m_resident_memory) / 1024.0 / 1024.0),
        float(double(g_prof_data.m_resident_memory) / double(g_prof_data.m_phys_ram) * 100.0),
        float(double(g_prof_data.m_phys_ram) / 1024.0 / 1024.0 / 1024.0),
        g_prof_data.m_tei.faults,
        g_prof_data.m_tei.pageins,
        g_prof_data.m_tei.cow_faults);
    g_font.DrawStringFixed6x12(3, InvY(36), buf);

    // Graph
    static uint scrollx = 0;
    DrawLabelledLineGraph(g_prof_data.m_res_mem_hist, 3, InvY(38), 478, 58, 5, scrollx);
}

void DrawIOProfile()
{
    // I/O header
    char buf[512];
    std::snprintf(buf, sizeof(buf), "I/O %s/s (File System), IOPS: %i",
        PrintBytesHumanReadable(
            g_prof_data.m_bytes_read_sec + g_prof_data.m_bytes_written_sec).c_str(),
        g_prof_data.m_iops);
    g_font.DrawStringFixed6x12(g_col_wdh, InvY(36), buf);
    std::snprintf(buf, sizeof(buf), "Read: %s/s",
        PrintBytesHumanReadable(g_prof_data.m_bytes_read_sec).c_str());
    g_font.DrawStringFixed6x12(g_col_wdh + 277, InvY(36), buf, 0xFF00FF00);
    std::snprintf(buf, sizeof(buf), "Write: %s/s",
        PrintBytesHumanReadable(g_prof_data.m_bytes_written_sec).c_str());
    g_font.DrawStringFixed6x12(g_col_wdh + 377, InvY(36), buf, 0xFF0000FF);

    // Trace facility unavailable?
    if (g_prof_data.m_fs_usage_running == false)
    {
        DrawGradientBox(g_col_wdh, InvY(38), g_col_wdh - 7, 58);
        g_font.DrawStringFixed6x12(
            g_col_wdh + 20,
            InvY(67),
            "The kdebug trace facility used for I/O data gathering is not available\n"
            "Are you running fs_usage, sc_usage, latency or another profiler instance?",
            0xFF0000FF);
    }
    else
    {
        // Graph
        static uint scrollx = 0;
        DrawLabelledLineGraph(
            g_prof_data.m_combined_bytes_sec_hist, g_col_wdh, InvY(38), 478, 58, 5, scrollx);
    }
}

void DisplayFunc()
{
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

    char buf[512];

    g_prof_data.Lock();

    // Draw all profiling displays, need to have profiler data locked
    DrawCPUUsage();
    DrawMemoryProfile();
    DrawThreadDisplay();
    DrawFunctionProfile();
    DrawIOProfile();
    if (g_show_call_tree)
        DrawCallTree();
    else
        DrawSourceView();
    const float prof_cpu = g_prof_data.m_prof_cpu;

    g_prof_data.Unlock();

    // FPS counter
    static uint frames_per_second = 0;
    {
        static double last_tick = 0;
        static uint num_frames = 0;
        const double cur_tick = TimerGetTick();
        if (cur_tick - last_tick > 1.0)
        {
            last_tick = cur_tick;
            frames_per_second = num_frames;
            num_frames = 0;
        }
        num_frames++;
    }
    DrawSpinningCube(InvX(67) + (g_freeze_sampling_thread ? 12 : 0) , InvY(13), 13);

    // Top-right Header
    std::snprintf(buf, sizeof(buf),
        "[ESC] Quit | %s | [T]oggle Call Tree / Source | Sa[V]e Report |   %i FPS\n"
        "[J][K] Select Function | [F1] Help | [U]I Scale: %.1fx | [P]rofiler CPU: %4.1f%%",
        g_freeze_sampling_thread ? "Un[F]reeze" : "[F]reeze",
        frames_per_second,
        g_ui_scale, prof_cpu);

    g_font.DrawStringFixed6x12(g_col_wdh, InvY(12), buf);
    glBegin(GL_LINES);
        glVertex2f(g_col_wdh, InvY(24));
        glVertex2f(InvX(3), InvY(24));
    glEnd();

    // Resizing handle
    glColor3f(0.75f, 0.75f, 0.75f);
    glBegin(GL_LINES);
        glVertex2f(InvX(12), 0);
        glVertex2f(InvX(0), 12);
        glVertex2f(InvX(7), 0);
        glVertex2f(InvX(0), 7);
        glVertex2f(InvX(2), 0);
        glVertex2f(InvX(0), 2);
    glEnd();
    glColor3f(1.0f, 1.0f, 1.0f);

    // Render this frame's text. We only want filtering when we shrink the UI. This also fixes
    // potential filtering issues on GPUs with 1x size (only seen it on VirtualBox so far)
    g_font.Render(g_ui_scale < 1.0f);

    // Error checking
#ifndef NDEBUG
    const GLenum error = glGetError();
#endif // NDEBUG
    assert(error != GL_INVALID_ENUM);
    assert(error != GL_INVALID_VALUE);
    assert(error != GL_INVALID_OPERATION);
    assert(error != GL_STACK_OVERFLOW);
    assert(error != GL_STACK_UNDERFLOW);
    assert(error != GL_OUT_OF_MEMORY);
    assert(error != GL_TABLE_TOO_LARGE);
    assert(error == GL_NO_ERROR);

    glutSwapBuffers();
}

void Setup2DOpenGL()
{
    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    gluOrtho2D(0.0, GLdouble(g_real_wnd_wdh), 0.0, GLdouble(g_real_wnd_hgt));
    glTranslatef(0.375f, 0.375f, 0.0f); // Magic number working for NV & ATI
    glScalef(g_ui_scale, g_ui_scale, 0.0);
}

void ReshapeFunc(int width, int height)
{
    // Find closest height match (don't cut off text in the middle)
    g_wnd_hgt = height / g_ui_scale;
    g_wnd_hgt = std::max(int(300), int(g_wnd_hgt - ((g_wnd_hgt + 3) % 10)));
    g_wnd_hgt += 8 - (g_wnd_hgt % 10);

    g_real_wnd_wdh = g_wnd_wdh * g_ui_scale;
    g_real_wnd_hgt = g_wnd_hgt * g_ui_scale;

    // Adjust OpenGL
    Setup2DOpenGL();
    glViewport(0, 0, g_real_wnd_wdh, g_real_wnd_hgt);

    // In case we resized it
    glutReshapeWindow(g_real_wnd_wdh, g_real_wnd_hgt);
}

void KeyCallback(unsigned char key, int x, int y)
{
    switch (key)
    {
        case 27: // Escape, quit application
            exit(0);
            break;

        case 'f': // Freeze / Unfreeze sampling thread
            g_freeze_sampling_thread = !g_freeze_sampling_thread;
            break;

        case 's': // Change sampling attempts target
            g_num_smp_target = std::min(g_num_smp_target + 250, 5000u);
            break;
        case 'S':
            g_num_smp_target = std::max(g_num_smp_target - 250, 250u);
            break;

        case 'v': // Generate a simple text report from the current snapshot
            {
                // TODO: Check if the file already exists and change owner from root
                char file_name[128];
                std::snprintf(file_name, sizeof(file_name), "report_pid_%i_at_%is.txt",
                    g_prof_data.m_pid, int(TimerGetTick()));
                std::FILE *file = std::fopen(file_name,  "w");
                std::fputs(g_font.GetLastFrameText(), file);
                std::fclose(file);
                std::printf("Written %s\n", file_name);
            }
            break;

        case 'j': // Current function selection
            if (int(g_cur_func_sel) < InvY(231) / 10 - 5) // TODO: Don't re-compute this here
                g_cur_func_sel++;
            break;
        case 'k':
            if (g_cur_func_sel > 0)
                g_cur_func_sel--;
            break;

        case 'p': // Profile profiler
            {
                // TODO: We'll hang at exit while the child profiler is still running
                char pid_buf[32];
                std::snprintf(pid_buf, sizeof(pid_buf), "%i", int(getpid()));
                if (fork() == 0)
                {
                    execlp(
                        g_prof_data.m_prof_exe_name.c_str(),
                        g_prof_data.m_prof_exe_name.c_str(),
                        pid_buf, NULL);
                }
            }
            break;

        case 'm': // Call tree mode
            g_call_tree_incoming = !g_call_tree_incoming;
            break;

        case 'a': // Samples in profile
            g_num_smp_profile = std::min(g_num_smp_profile + 1000, 50000u);
            break;
        case 'A':
            g_num_smp_profile = std::max(g_num_smp_profile - 1000, 1000u);
            break;

        case 'r': // Reset profile samples
            g_reset_profile = true;
            break;

        case 'u': // Change UI scaling
            if (g_ui_scale == 0.5f)
                g_ui_scale = 0.7f;
            else if (g_ui_scale == 0.7f)
                g_ui_scale = 1.0f;
            else if (g_ui_scale == 1.0f)
                g_ui_scale = 2.0f;
            else if (g_ui_scale == 2.0f)
                g_ui_scale = 0.5f;
            ReshapeFunc(g_real_wnd_wdh, g_real_wnd_hgt);
            break;
        case 'U':
            if (g_ui_scale == 0.5f)
                g_ui_scale = 2.0f;
            else if (g_ui_scale == 0.7f)
                g_ui_scale = 0.5f;
            else if (g_ui_scale == 1.0f)
                g_ui_scale = 0.7f;
            else if (g_ui_scale == 2.0f)
                g_ui_scale = 1.0f;
            ReshapeFunc(g_real_wnd_wdh, g_real_wnd_hgt);
            break;

        case 't': // Toggle between the call tree / source view
            g_show_call_tree = !g_show_call_tree;
            break;

        case 'g': // Merge selected symbol
            g_prof_data.Lock();
            if (g_cur_func_sel < g_prof_data.m_functions.size())
            {
                g_prof_data.m_merge_sym.insert(g_prof_data.m_functions[g_cur_func_sel].m_sym_id);
                g_reset_profile = true;
            }
            g_prof_data.Unlock();
            break;

        case 'c': // Clear merged symbols
            g_prof_data.Lock();
            g_reset_profile = true;
            g_prof_data.m_merge_sym.clear();
            g_prof_data.Unlock();
            break;
    }
}

void SpecialKeyCallback(int key, int x, int y)
{
    switch (key)
    {
        // Vim style HJKL forwards
        case GLUT_KEY_LEFT:
            KeyCallback('h', x, y);
            break;
        case GLUT_KEY_DOWN:
            KeyCallback('j', x, y);
            break;
        case GLUT_KEY_UP:
            KeyCallback('k', x, y);
            break;
        case GLUT_KEY_RIGHT:
            KeyCallback('l', x, y);
            break;

        case GLUT_KEY_F1: // Help
            {
                // Open project URL, make sure we don't do it as root but as the actual user
                char buf[256];
                std::snprintf(buf, sizeof(buf), "sudo -u $SUDO_USER open %s", g_project_url);
                system(buf);
            }
            break;
    }
}

void IdleFunc()
{
    static double last_tick = 0.0;

    // Frame limiter
    while (true)
    {
        const double cur_tick = TimerGetTick();

        if (cur_tick - last_tick < (1.0 / g_max_fps))
        {
            usleep(1000 * (1000 / g_max_fps));
            continue;
        }

        last_tick = cur_tick;
        break;
    }

    glutPostRedisplay();
}

void Shutdown()
{
    // Stop sampling threads
    g_freeze_sampling_thread = false;
    g_stop_sampling_thread = true;
    if (pthread_join(g_sampling_thread, NULL) != 0)
        assert(!"pthread_join() for sampling thread failed");
}

int main(int argc, char *argv[])
{
    if (argc != 2)
    {
        std::printf(
            "rsvp - Realtime Sampling Visual Profiler\n"
            "Version 0.1 - (C) 2012 Tim C. Schröder (www.blitzcode.net)\n\n"
            "Usage: %s <PID or process name>\n"
            "Needs to run as root (sudo)\n\n"
            "Compile target application with -g to get symbol names and\n"
            "-fno-omit-frame-pointer for stack traces. Using -fno-inline\n"
            "might further improve symbol resolution and stack traces at\n"
            "the expense of reduced and / or skewed performance. For\n"
            "source and line-level information access to the object files\n"
            "or a .dSYM directory generated by 'dsymutil' is required.\n"
            "RSVP_SRC_PATH is used to locate source files.\n\n"
            "Please see %s for updates\n"
            "and documentation.\n",
            argv[0], g_project_url);
        return 1;
    }

    // Store executable name
    g_prof_data.m_prof_exe_name = argv[0];

    // Are we root?
    if (geteuid() != 0)
        FatalExit("Need to run as root - forgot 'sudo'?");

    // Initialize timer while we're still single threaded
    TimerGetTick();

    // Numeric PID or process name?
    if (isalpha(*argv[1]) == 0 && *argv[1] != '.' && *argv[1] != '/' && *argv[1] != '~')
        g_prof_data.m_pid = atoi(argv[1]); // PID
    else
    {
        // Process name, translate into a PID by using the ps utility
        char buf[1024];
        std::snprintf(buf, sizeof(buf), "ps -A | grep -v grep | grep -v %s | grep %s",
            argv[0], argv[1]);
        std::FILE *pipe = popen(buf, "r");
        assert(pipe != NULL);
        uint pid = 0;
        if (std::fscanf(pipe, "%u", &pid) != 1)
            FatalExit("Couldn't resolve process name to a PID");
        pclose(pipe);
        g_prof_data.m_pid = pid;
    }

    // Validate PID
    if (getpgid(g_prof_data.m_pid) < 0)
        if (errno == ESRCH)
            FatalExit("Invalid PID specified");

    // 32 or 64 bit target?
    {
        int mib[4] = { CTL_KERN, KERN_PROC, KERN_PROC_PID, 0 };
        mib[3] = g_prof_data.m_pid;
        size_t len = sizeof(kinfo_proc);
        kinfo_proc kp;

        if (sysctl(mib, 4, &kp, &len, NULL, 0) == -1)
            assert(!"sysctl() failed");

        g_prof_data.m_x64 = kp.kp_proc.p_flag & P_LP64;
    }

    // Use libproc to get an executable path from the process ID
    {
        char path_buf[PROC_PIDPATHINFO_MAXSIZE];
        if (proc_pidpath(g_prof_data.m_pid, path_buf, sizeof(path_buf)) <= 0)
            assert(!"proc_pidpath failed");

        g_prof_data.m_executable_path = path_buf;
    }

    // Initialize symbol management
    g_symbol = std::auto_ptr<SymbolManager>(new SymbolManager(g_prof_data.m_pid));

    // Initialize fs_usage pipe
    g_fs_usage = std::auto_ptr<FSUsage_Pipe>(new FSUsage_Pipe(g_prof_data.m_pid));

    // Initialize source line lookup
    g_source = std::auto_ptr<SourceLineLookup>
        (new SourceLineLookup(g_prof_data.m_executable_path.c_str()));

    // Determine memory & CPU cores in the system
    {
        int mib[2];
        size_t len;

        mib[0] = CTL_HW;
        mib[1] = HW_MEMSIZE;
        len = sizeof(g_prof_data.m_phys_ram);
        if (sysctl(mib, 2, &g_prof_data.m_phys_ram, &len, NULL, 0) == -1)
            assert(!"sysctl() failed");

        mib[0] = CTL_HW;
        mib[1] = HW_NCPU;
        len = sizeof(g_prof_data.m_num_cpus);
        if (sysctl(mib, 2, &g_prof_data.m_num_cpus, &len, NULL, 0) == -1)
            assert(!"sysctl() failed");
    }

    // Launch sampling thread
    if (pthread_create(&g_sampling_thread, NULL, SamplingThread, NULL) != 0)
        assert(!"Sampling thread creation failed");

    // Register exit callback
    if (std::atexit(Shutdown) != 0)
        assert(!"atexit() failed");

    // Initialize GLUT
    glutInit(&argc, argv);
    glutInitWindowSize(g_wnd_wdh, g_wnd_hgt);
    glutInitDisplayMode(GLUT_RGB | GLUT_DOUBLE | GLUT_DEPTH);
    {
        char title[512];
        std::snprintf(title, sizeof(title), "rsvp - %s (PID %i, x%s)",
            g_prof_data.m_executable_path.c_str(),
            g_prof_data.m_pid,
            g_prof_data.m_x64 ? "64" : "32");
        glutCreateWindow(title);
    }
    glutDisplayFunc(DisplayFunc);
    glutSpecialFunc(SpecialKeyCallback);
    glutKeyboardFunc(KeyCallback);
    glutReshapeFunc(ReshapeFunc);
    glutIdleFunc(IdleFunc);

    Setup2DOpenGL();
    glClearColor(0.0f, 0.0f, 0.0f, 1.0f);

    glutMainLoop();

    return 0;
}

