
# Default target depending on main output
.PHONY : all
all : rsvp 

# Compiler and linker flags
CXXFLAGS = -g -pthread -Wall -Wextra -Wno-unused-parameter \
           -O3 -mtune=native -fno-omit-frame-pointer \
	   -Wno-deprecated
#          -fno-inline
#          -DNDEBUG
LDFLAGS  = -framework OpenGL \
	   -framework GLUT

# Sources and objects. We assume all .cpp files in the directory are meant to
# be compiled
SRC = $(wildcard *.cpp)
OBJ = $(SRC:.cpp=.o)

# Rule for producing the main output
LD_OBJ = $(OBJ) $(patsubst %, %/rsvp, $(LIBSUBDIRS))
rsvp : $(LD_OBJ)
	$(CXX) -o $@ $(CXXFLAGS) $(LDFLAGS) $(LD_OBJ)

# Only include this if we actually build the main output, don't want to
# generate dependencies for the clean targets etc.
ifeq ($(MAKECMDGOALS), )
 
# Automatically generate dependencies with the compiler for each source file
%.d: %.cpp
	@set -e; rm -f $@; \
	 $(CXX) -MM $(CXXFLAGS) $< > $@.$$$$; \
	 sed 's,\($*\)\.o[ :]*,\1.o $@ : ,g' < $@.$$$$ > $@; \
	 $(RM) $@.$$$$

# Include the generated dependencies for object and dependency files. Be silent
# during the first compile where the .d files have not been generated yet and
# everything is recompiled
-include $(SRC:.cpp=.d)

endif

# Clean by deleting final output, dependency and object files
.PHONY : clean
clean:
	$(RM) rsvp $(OBJ) $(OBJ:.o=.d)

