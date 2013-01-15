Note: to compile x86 on 64-bit, must include option: /platform:x86

* x86: Also, make sure to COPY (clean did not work and gave me hours of debugging trouble) all the files from: C:\Program Files (x86)\Microsoft Research\Z3-4.1\bin
* 64-bit: copy (clean did not work) all files from: C:\Program Files (x86)\Microsoft Research\Z3-4.1\x64
** These go into the debug directory	C:\Users\tjohnson\Dropbox\Research\tools\passel\repos\trunk\src\dotnet\passel\bin\Debug\



* Design lessons learned for future versions
** 2013-01-08: Time transitions and discrete transitions: objects should be created representing all standard transition types.  For example, suppose we work with a standard hybrid automaton model with discrete locations and varying ODEs in each location.  Transitions between locations are easily specified since they just represent edges in a graph.  However, any time transition should also be represented by a similar object as a map from that location to the same location based on the particular dynamics of that location.  This allows easily iterating over all transitions in a location, regardless of whether they are continuous or discrete, and simplifies many program parts.  Similar architectural decisions must be made for representations of automata (e.g., different automata, global arbiters, etc.).