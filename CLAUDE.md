# CLAUDE.md - AI Assistant Guide for PASSEL

## Project Overview

**PASSEL** (PArameterized Safety Specifications for Embedded Liveness) is a formal verification tool for hybrid automata and distributed algorithms. It performs safety property verification using the Z3 SMT theorem prover with reachability analysis and symmetry reduction techniques.

### Key Capabilities
- Analyze parametric distributed protocols (Fischer's mutual exclusion, Peterson's algorithm, etc.)
- Handle hybrid automata with timed systems
- Export to multiple formats (Phaver, SpaceEx, HyTech, Uppaal, LaTeX)
- Support for both Windows and Linux/Mono execution
- Symmetry reduction for parametric verification

---

## Repository Structure

This repository uses an **SVN-style layout**:

```
/home/user/passel/
├── trunk/              # Main development area (ALL development happens here)
│   ├── src/            # Source code
│   │   ├── dotnet/     # C# .NET 4.0 implementation
│   │   │   └── passel/ # Main executable project
│   │   └── python/     # Python 3 supporting tools
│   ├── input/          # Test cases (77 XML files)
│   ├── output/         # Verification results
│   └── lib/            # External libraries (ANTLR, QuickGraph)
├── branch/             # Feature branches (currently empty)
├── tag/                # Release tags (currently empty)
└── README.txt          # Build configuration notes
```

### Critical Directory Locations

**Source Code:**
- C# Main Project: `/home/user/passel/trunk/src/dotnet/passel/`
- Python Tools: `/home/user/passel/trunk/src/python/`
- Unit Tests: `/home/user/passel/trunk/src/dotnet/passel_test/`

**Key Subdirectories in C# Project:**
- `/model/` - Hybrid automaton representation, reachability algorithms
- `/controller/` - Core orchestration, parsing, SMT integration, output
- `/view/` - Windows Forms GUI and visualization

**Test Cases:**
- Input files: `/home/user/passel/trunk/input/` (77 XML test cases)
- Output logs: `/home/user/passel/trunk/output/`

---

## Technology Stack

### Primary Languages
1. **C# (.NET 4.0)** - Main implementation (~12,700 lines)
   - Target: .NET 4.0 Client Profile
   - Platform: x86 (primary), x64 supported
   - Mono compatible for Linux

2. **Python 3** - Supporting verification tools
   - Direct Z3 API usage
   - Bounded model checking

### Key Dependencies

**NuGet Packages:**
- `QuickGraph 3.6.61119.7` - Graph algorithms and data structures

**External Libraries:**
- **Microsoft.Z3** - SMT solver (versions 4.1, 4.2, or 4.3.2 unstable)
  - Critical: Different Z3 versions have different capabilities
  - 4.3.2 unstable fixes some inductive invariant proofs
  - Must copy Z3 binaries to output directory
- **ANTLR 3.Runtime** - Parser generation for mathematical expressions
- **GraphSharp** - Graph visualization
- **VixCOM** - VMware interop

**System Libraries:**
- System.Windows.Forms - GUI
- System.Xml, System.Xml.Linq - XML parsing

---

## Build System

### Build Configurations

The project supports **6 build configurations**:

1. **Debug** - Standard debug build
2. **Release** - Standard release build
3. **bin-win-z3** - Windows with Z3 4.2
4. **bin-win-z3-unstable** - Windows with Z3 4.3.2 unstable
5. **bin-mono-z3** - Linux/Mono with Z3 4.2
6. **bin-mono-z3-unstable** - Linux/Mono with Z3 4.3.2 unstable

### Platform Notes

**Windows (x86):**
```bash
# Compile with x86 platform target
# Copy Z3 binaries from: C:\Program Files (x86)\Microsoft Research\Z3-4.1\bin
# To: bin\Debug\ or bin\Release\
```

**Windows (x64):**
```bash
# Copy Z3 binaries from: C:\Program Files (x86)\Microsoft Research\Z3-4.1\x64
```

**Linux/Mono:**
- Uses `libz3.so` instead of `z3.dll`
- DLL mapping configured in `app.config`
- Currently has graph library compatibility issues (under investigation)

### Building the Project

The project uses MSBuild/Visual Studio:
```bash
# Build using MSBuild
msbuild trunk/src/dotnet/passel/passel.csproj /p:Configuration=Debug

# Or use Visual Studio
# Open: trunk/src/dotnet/passel/passel.csproj
```

**Important:** Always use `/platform:x86` when building on 64-bit systems for x86 target.

---

## Code Architecture

### MVC Pattern

The codebase follows Model-View-Controller architecture:

**Model** (`/model/` - ~7,700 lines):
- `AHybridAutomaton.cs` - Abstract base class for hybrid automata
- `ConcreteHybridAutomaton.cs` - Concrete automaton implementation
- `AbstractHybridAutomaton.cs` - Abstract automaton for verification
- `Location.cs`, `Transition.cs` - Automaton structure
- `Variable.cs`, `VariableGlobal.cs`, `VariableIndexed.cs` - Variable types
- `Flow.cs` - Continuous dynamics (ODEs)
- `ReachSymmetric.cs` - **Symmetric reachability algorithm** (core verification)
- `TreeReach.cs` - Tree-based reachability
- `Property.cs` - Safety properties
- `Counterexample.cs` - Trace generation for failing properties
- `Holism.cs` - Global system context

**Controller** (`/controller/` - ~5,000 lines):
- `Controller.cs` - **Main orchestrator** (Singleton pattern)
  - Coordinates parser, SMT solver, and model
  - Access via: `Controller.Instance`
- `/parsing/` - Input parsing
  - `ParseHyXML.cs` - XML hybrid automaton parser
  - `/math/` - Mathematical expression parsing
    - `guard.g3` - ANTLR 3 grammar for expressions
    - `Expression.cs`, `BinaryExpression.cs`, `LogicalExpression.cs` - AST
- `/smt/` - SMT solver integration
  - `ISmtSymbols.cs` - Solver interface (abstraction layer)
  - `/z3/Z3Wrapper.cs` - **Z3 API wrapper** (primary SMT integration)
  - `SymbolsZ3.cs` - Z3 symbol management
- `/output/` - Result generation
  - `PrintPhaver.cs` - Export to Phaver format
  - `Debug.cs` - Debug logging

**View** (`/view/` - ~8,000 lines):
- `View.cs`, `View.Designer.cs` - Windows Forms GUI
- `ViewReach.cs` - Reachability visualization

### Design Patterns

1. **Singleton Pattern**
   - `Controller.Instance` - Global access to SMT solver and configuration
   - Always access controller via singleton

2. **Abstract Base Classes**
   - `AHybridAutomaton` - Base for all automaton types
   - `AState`, `AAgentDataTheory` - Abstract state representations
   - Inherit from these for new automaton types

3. **Visitor Pattern**
   - `EvaluationVisitor`, `LogicalExpressionVisitor` - Expression traversal
   - Used for expression evaluation and transformation

4. **SMT Abstraction**
   - `ISmtSymbols` interface - Solver-independent API
   - Currently only Z3 implementation, but designed for extensibility

---

## Input Format - Hybrid Automaton XML

The primary input format is XML-based hybrid automaton specification.

### Structure Example

```xml
<holism>
  <!-- System parameters -->
  <parameter name='N' type='index' comment='number of processes' />
  <parameter name='A' type='real' assumption='A == 5.0' />

  <!-- Global variables -->
  <variable name='g' type='index' update_type='Discrete' />

  <!-- Hybrid automaton definition -->
  <automaton name='fischer'>
    <!-- Indexed variable (one per process) -->
    <variable name='x[i]' type='real' update_type='Continuous' />

    <!-- Initial condition -->
    <initial equn='(forall i (x[i] = 0.0)) and g = 0' />

    <!-- Discrete location/mode -->
    <mode id='0' name='idle' initial='True'>
      <!-- Continuous dynamics (ODE) -->
      <dai variable='x[i]' equn='x[i]_dot = 0.0'/>
      <!-- Invariant (optional) -->
      <invariant equn='x[i] &lt;= A'/>
    </mode>

    <!-- Transition between modes -->
    <transition source='idle' destination='start'>
      <!-- Guard condition -->
      <guard equn='g = 0'/>
      <!-- Discrete update (action) -->
      <action equn='g&apos; = i and x[i]&apos; = 0.0'/>
    </transition>
  </automaton>

  <!-- Safety property to verify -->
  <property name='mutex' equn='not (exists i exists j (i != j and loc[i] = cs and loc[j] = cs))'/>
</holism>
```

### XML Elements Reference

- `<holism>` - Root element, global system container
- `<parameter>` - System parameters (N for process count, constants A, B, etc.)
- `<variable>` - Global or local variables (Discrete or Continuous)
- `<automaton>` - Hybrid automaton definition
- `<mode>` - Discrete location/state in automaton
- `<dai>` - Differential equation for continuous dynamics (`x_dot` notation)
- `<transition>` - Edge between locations
- `<guard>` - Transition enabling condition
- `<action>` - Discrete update on transition (primed variables `x'`)
- `<invariant>` - Location invariant
- `<initial>` - Initial state condition
- `<property>` - Safety property to verify

### Expression Syntax (from ANTLR grammar)

**Logical Operators:**
- `||`, `or` - Disjunction
- `&&`, `and` - Conjunction
- `not` - Negation
- `implies` - Implication
- `iff` - If and only if

**Comparison:**
- `<`, `<=`, `>`, `>=` - Relational
- `==`, `!=` - Equality

**Arithmetic:**
- `+`, `-`, `*`, `/` - Basic operations
- `%` - Modulo
- `^` - Power

**Quantifiers:**
- `forall i (expr)` - Universal quantification
- `exists i (expr)` - Existential quantification

**Special Notation:**
- `x[i]` - Indexed variables (parametric systems)
- `x_dot` - Time derivative (continuous dynamics)
- `x'` - Primed variable (next-state value)
- `loc[i]` - Location of process i

---

## Testing

### Unit Tests

**Project:** `passel_test`
- Framework: Visual Studio Unit Test Framework
- Target: .NET 4.5
- Location: `/home/user/passel/trunk/src/dotnet/passel_test/`

**Test Classes:**
1. `LogicalExpressionTest.cs` - Expression parsing and evaluation
2. `ParseTest.cs` - XML parsing verification
3. `ReachSymmetricTest.cs` - Symmetric reachability algorithm
4. `SymmetricStateTest.cs` - State symmetry operations

### Integration Tests

**77 XML test cases** in `/home/user/passel/trunk/input/`:

**Mutual Exclusion Protocols:**
- `fischer.xml` (42KB) - **Primary test case**, Fischer's protocol
- `fischer_umeno_global_clock.xml` - Variant with global time
- `fischer_buggy.xml` - Buggy variant for false-positive testing
- `peterson.xml` - Peterson's 2-process algorithm
- `bakery.xml` - Lamport's bakery algorithm
- `lynch_shavit.xml` - Lynch-Shavit protocol

**Cache Coherence:**
- `german.xml` - German cache coherence protocol

**Distributed Algorithms:**
- `token_ring.xml` - Token ring protocol
- `bully.xml` - Bully leader election

**Hybrid Systems:**
- `flocking.xml` - Flocking behavior
- `sats_timed_counter.xml` - Timed automata
- `clock_sync.xml` - Clock synchronization

**Expected Outputs:**
- Check `/home/user/passel/trunk/output/` for verification logs
- `fischer_proof.log` - Successful verification
- `fischer_buggy.log` - Counterexample generation

---

## Development Workflow

### Making Changes

1. **Always work in `/trunk/`**
   - This repository uses SVN structure
   - All development happens in trunk directory

2. **Understand the verification flow:**
   ```
   Input XML → ParseHyXML → Hybrid Automaton Model
                            ↓
                       Controller.Instance
                            ↓
                   Z3 SMT Solver (Z3Wrapper)
                            ↓
   Reachability Analysis (ReachSymmetric/TreeReach)
                            ↓
           Safety Property Verification
                            ↓
   Output (Phaver/SpaceEx) or Counterexample
   ```

3. **Key modification points:**
   - **Add new input format:** Extend `/controller/parsing/`
   - **Add new reachability algorithm:** Extend `/model/ReachSymmetric.cs` or create new class
   - **Add new SMT solver:** Implement `ISmtSymbols` interface
   - **Add new output format:** Add to `/controller/output/`
   - **Modify expression syntax:** Update `guard.g3` ANTLR grammar

4. **Critical design lesson** (from README.txt:10):
   > Time transitions and discrete transitions should be represented uniformly as transition objects. This allows easy iteration over all transitions in a location, regardless of continuous or discrete type.

### Testing Changes

1. **Run unit tests:**
   ```bash
   # Build test project
   msbuild trunk/src/dotnet/passel_test/passel_test.csproj

   # Run tests (if test runner available)
   vstest.console.exe passel_test.dll
   ```

2. **Run integration tests:**
   ```bash
   # Test with Fischer's protocol
   ./passel.exe trunk/input/fischer.xml

   # Test with buggy variant (should find counterexample)
   ./passel.exe trunk/input/fischer_buggy.xml

   # Compare output with expected logs in trunk/output/
   ```

3. **Verify different Z3 versions:**
   - Test with both 4.2 and 4.3.2 unstable
   - 4.3.2 fixes some inductive invariant proofs
   - Configuration-specific builds available

---

## Configuration Files

### Application Configuration

**`app.config`** - Main configuration:
- .NET 4.0 runtime settings
- DLL mapping for Mono compatibility
  - Windows: `z3.dll`
  - Linux: `libz3.so`
  - macOS: `libz3.dylib`

**Platform-Specific Configs** (`/config/`):
- `app.Debug.config`, `app.Release.config` - Standard builds
- `app.bin-win.config` - Windows-specific paths
- `app.bin-mono.config` - Linux-specific paths
- `app.bin-win-z3*.config` - Z3 version-specific (Windows)
- `app.bin-mono-z3*.config` - Z3 version-specific (Linux)

### Grammar Configuration

**`guard.g3`** - ANTLR 3 grammar:
- Language: CSharp3
- Defines mathematical expression syntax
- Generate parser: `java -jar antlr-3.5.2-complete.jar guard.g3`

---

## Key Conventions for AI Assistants

### Code Style

1. **Naming Conventions:**
   - Classes: PascalCase (`HybridAutomaton`, `ReachSymmetric`)
   - Methods: PascalCase (`ComputeReachability`, `ParseXML`)
   - Variables: camelCase (`currentState`, `transitionList`)
   - Private fields: camelCase with underscore prefix (`_smtSolver`, `_stateSpace`)
   - Interfaces: IPascalCase (`ISmtSymbols`)
   - Abstract classes: APascalCase (`AHybridAutomaton`)

2. **File Organization:**
   - One class per file
   - File name matches class name
   - Designer files for forms: `ClassName.Designer.cs`

3. **Namespaces:**
   - Root: `passel`
   - Model: `passel.model`
   - Controller: `passel.controller`
   - View: `passel.view`

### Common Patterns to Follow

1. **Accessing the SMT Solver:**
   ```csharp
   // Always use singleton
   var controller = Controller.Instance;
   var smtSolver = controller.SmtSymbols;
   ```

2. **Expression Evaluation:**
   ```csharp
   // Use visitor pattern
   var visitor = new EvaluationVisitor(context);
   var result = expression.Accept(visitor);
   ```

3. **State Representation:**
   - States are immutable where possible
   - Use `AState` abstract base for new state types
   - Implement equality and hashing for state comparison

4. **Transition Handling:**
   - Both continuous (time) and discrete transitions should be uniform
   - Iterate over all transition types together
   - Check guards before applying actions

### Critical Areas (Modify with Care)

1. **`ReachSymmetric.cs`** - Core verification algorithm
   - Symmetry reduction is complex
   - Changes may affect soundness
   - Always test with full test suite

2. **`Z3Wrapper.cs`** - SMT solver integration
   - Z3 API calls are version-sensitive
   - Quantifier elimination may behave differently across versions
   - Test with multiple Z3 versions

3. **`guard.g3` ANTLR Grammar** - Expression syntax
   - Changes require regenerating parser
   - May break existing XML test cases
   - Update ParseHyXML.cs if grammar changes

4. **XML Schema** - Input format
   - Many test cases depend on current format
   - Backward compatibility important
   - Document any schema changes

### Performance Considerations

1. **SMT Solver Calls:**
   - Expensive operation
   - Cache results when possible
   - Use incremental solving (push/pop contexts)

2. **State Space Exploration:**
   - Can be exponential
   - Symmetry reduction critical for scalability
   - Consider BDDs or other symbolic representations for large state spaces

3. **Graph Algorithms:**
   - QuickGraph library is optimized
   - Use built-in algorithms when available
   - Profile before optimizing

### Debugging Tips

1. **Enable Debug Output:**
   - `Debug.cs` in controller/output provides logging
   - Output goes to trunk/output/
   - Check `iniOptions.txt` for configuration

2. **Common Issues:**
   - Z3 binaries not found: Check DLL copying (see README.txt)
   - Quantifier elimination fails: May need Z3 4.3.2 unstable
   - Graph library errors on Mono: Known issue, under investigation
   - Parse errors: Check XML entity encoding (`&lt;`, `&gt;`, `&apos;`)

3. **Verification Debugging:**
   - Check counterexample traces for property violations
   - Visualize reachability graph in GUI
   - Export to Phaver for alternative verification
   - Compare with Python implementation results

---

## Known Issues and Limitations

### Current Problems

1. **Mono Graph Library Compatibility** (in progress)
   - Graph visualization may fail on Linux/Mono
   - Core verification still works
   - Issue logged in recent commits

2. **Z3 Version Sensitivity**
   - Z3 4.1/4.2: Some inductive invariants return "unknown"
   - Z3 4.3.2 unstable: Fixes most issues but API changes
   - Quantifier elimination behavior differs between versions

3. **Platform-Specific Builds**
   - Must manually copy Z3 binaries to output directory
   - Clean builds may remove Z3 DLLs (use COPY, not clean)
   - x86 vs x64 require different Z3 binary paths

### Future Improvements

From README.txt design lessons:
- **Uniform transition representation:** Continuous and discrete transitions should share same interface
- **Modular automaton composition:** Better support for global arbiters and composition
- **Architecture generalization:** Support for different automaton models beyond standard hybrid automata

---

## External Resources

### Documentation
- Z3 Theorem Prover: https://github.com/Z3Prover/z3
- ANTLR 3: https://www.antlr3.org/
- QuickGraph: https://quickgraph.codeplex.com/

### Related Tools
- **Phaver:** Polyhedral hybrid automaton verifier
- **SpaceEx:** State space explorer for hybrid systems
- **HyTech:** Hybrid technology tool
- **Uppaal:** Timed automata verification

### Papers and Theory
- Parametric verification and symmetry reduction
- Hybrid automata formal semantics
- SMT-based model checking
- Quantifier elimination in verification

---

## Quick Start for AI Assistants

When asked to work on this codebase:

1. **Understand the request context:**
   - Is it about verification algorithm? → Focus on `/model/ReachSymmetric.cs`
   - Is it about input parsing? → Focus on `/controller/parsing/`
   - Is it about SMT integration? → Focus on `/controller/smt/z3/`
   - Is it about adding test cases? → Add XML to `/trunk/input/`

2. **Check relevant test cases:**
   - Look in `/trunk/input/` for similar examples
   - Check `/trunk/output/` for expected behavior

3. **Maintain architectural patterns:**
   - Use singleton for Controller
   - Use visitor pattern for expressions
   - Follow MVC separation

4. **Test thoroughly:**
   - Run unit tests in passel_test
   - Test with multiple XML inputs
   - Verify with both Z3 versions if possible

5. **Document changes:**
   - Update comments in code
   - Add test cases for new features
   - Note any Z3 version dependencies

---

## Summary

PASSEL is a sophisticated formal verification framework combining:
- **C# implementation** for core algorithms and UI
- **Z3 SMT solver** for decidable verification
- **ANTLR parser** for mathematical expressions
- **Graph algorithms** for reachability computation
- **Multi-platform support** (Windows native, Linux via Mono)
- **Comprehensive test suite** with 77 distributed algorithm examples

The codebase is well-structured with clear MVC separation, but requires careful attention to Z3 version compatibility and platform-specific build configurations. Always test changes against the full test suite and verify correctness of verification results.

---

**Last Updated:** 2025-11-17
**Repository Size:** ~192 MB
**Primary Language:** C# (.NET 4.0)
**Lines of Code:** ~12,700 (excluding tests)
