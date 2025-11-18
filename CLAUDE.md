# CLAUDE.md - AI Assistant Guide for PASSEL

## Project Overview

**PASSEL** (Parameterized Symmetry Reduction for Safety Verification) is a research verification tool for analyzing parameterized concurrent/distributed systems. It verifies safety properties of systems with an arbitrary number of processes using SMT-based techniques and symmetry reduction.

**Key Capabilities:**
- Verifying parameterized hybrid automata (arbitrary N processes)
- Checking inductive invariants using Z3 SMT solver
- Synthesizing safety invariants for mutual exclusion protocols
- Bounded model checking with symmetry reduction
- Analyzing classic protocols: Fischer, Bakery, Token Ring, German cache, etc.

**Technology Stack:**
- **Language:** C# (.NET Framework 4.0)
- **SMT Solver:** Microsoft Z3 (versions 4.1, 4.2, 4.3.2)
- **Parser:** ANTLR 3
- **Graph Libraries:** QuickGraph 3.6, GraphSharp
- **GUI:** Windows Forms (optional, disabled for Mono builds)
- **Cross-platform:** Windows (native) and Linux (via Mono)

---

## Repository Structure

```
passel/
├── README.txt              # Build notes and design lessons
├── CLAUDE.md              # This file - AI assistant guide
│
├── trunk/                 # Main development (SVN-style layout)
│   ├── input/            # ~74 XML test specifications
│   │   ├── fischer_umeno_global_clock_buggy.xml
│   │   ├── bakery-lynch.xml
│   │   ├── token-ring.xml
│   │   ├── gcd.xml
│   │   └── ... (mutual exclusion protocols, hybrid systems)
│   │
│   ├── output/           # Generated verification outputs
│   │   └── phaver/      # PHAVer format files
│   │
│   ├── src/
│   │   ├── dotnet/passel/        # Main C# codebase
│   │   │   ├── passel.sln        # Visual Studio 2013 solution
│   │   │   ├── passel.csproj     # Main project file
│   │   │   │
│   │   │   ├── model/            # Domain models (15+ files)
│   │   │   │   ├── Holism.cs               (2520 lines) - Top-level system container
│   │   │   │   ├── AHybridAutomaton.cs     (1383 lines) - Abstract automaton base
│   │   │   │   ├── ReachSymmetric.cs       (1399 lines) - Symmetric reachability
│   │   │   │   ├── ConcreteHybridAutomaton.cs - Concrete automaton
│   │   │   │   ├── AbstractHybridAutomaton.cs (710 lines) - Predicate abstraction
│   │   │   │   ├── Transition.cs           (819 lines) - Transition logic
│   │   │   │   ├── Property.cs             (372 lines) - Safety properties
│   │   │   │   ├── Variable*.cs            - Variable representations
│   │   │   │   └── Location.cs, AbstractState.cs - State representations
│   │   │   │
│   │   │   ├── controller/       # Main orchestration (20+ files)
│   │   │   │   ├── Controller.cs           (3432 lines) - Main entry point (Singleton)
│   │   │   │   ├── parsing/
│   │   │   │   │   ├── ParseHyXML.cs       - XML parser for input specs
│   │   │   │   │   └── *.g3                - ANTLR3 grammars
│   │   │   │   ├── smt/z3/
│   │   │   │   │   └── Z3Wrapper.cs        - Z3 integration wrapper
│   │   │   │   └── output/
│   │   │   │       ├── PrintPhaver.cs      - PHAVer output generator
│   │   │   │       └── Debug.cs            - Debug utilities
│   │   │   │
│   │   │   ├── view/             # GUI visualization
│   │   │   │   └── View.cs       - Windows Forms + GraphSharp
│   │   │   │
│   │   │   ├── lib/              # Z3 DLLs (multiple versions)
│   │   │   │   ├── z3_4.1/
│   │   │   │   ├── z3_4.2/
│   │   │   │   └── z3_4.3.2/
│   │   │   │
│   │   │   ├── app.config        # Base configuration
│   │   │   ├── app.bin-win-z3.config           # Windows Z3 4.2
│   │   │   ├── app.bin-win-z3-unstable.config  # Windows Z3 4.3.2
│   │   │   ├── app.bin-mono-z3.config          # Linux Z3 4.2
│   │   │   └── app.bin-mono-z3-unstable.config # Linux Z3 4.3.2
│   │   │
│   │   └── python/       # Utility scripts for invariant processing
│   │
│   └── lib/
│       └── antlr/        # ANTLR3 libraries
│
├── branch/               # SVN-style branches (legacy)
└── tag/                  # SVN-style tags (legacy)
```

---

## Architecture Overview

PASSEL follows an MVC-like architecture:

```
┌────────────────────────────────────────────┐
│         Controller (Singleton)             │
│  - Main() entry point                      │
│  - Command-line parsing                    │
│  - Configuration management                │
│  - Workflow orchestration                  │
└──────────────┬─────────────────────────────┘
               │
       ┌───────┴────────┐
       │                │
┌──────▼─────┐   ┌──────▼──────┐
│  Parsing   │   │  Z3 Wrapper │
│  (ANTLR3)  │   │  (SMT API)  │
│  XML, Expr │   │  Tactics    │
└──────┬─────┘   └──────┬──────┘
       │                │
       └───────┬────────┘
               │
    ┌──────────▼────────────┐
    │   Model (Holism)      │
    │  ┌──────────────────┐ │
    │  │ Hybrid Automata  │ │
    │  │  - Indexed vars  │ │
    │  │  - Locations     │ │
    │  │  - Transitions   │ │
    │  │  - Properties    │ │
    │  └──────────────────┘ │
    └──────────┬────────────┘
               │
    ┌──────────▼────────────┐
    │ Verification Engines  │
    │  - Inductive Inv.     │
    │  - BMC                │
    │  - Symmetric Reach    │
    │  - Inv. Synthesis     │
    └──────────┬────────────┘
               │
    ┌──────────▼────────────┐
    │  Output Generators    │
    │  - PHAVer format      │
    │  - Console logs       │
    │  - Graph viz (GUI)    │
    └───────────────────────┘
```

---

## Key Conventions

### 1. Code Style

**Naming Conventions:**
- Classes: PascalCase (`ConcreteHybridAutomaton`, `Z3Wrapper`)
- Methods: PascalCase (`CheckInductiveInvariant`, `ParseXML`)
- Private fields: `_camelCase` with underscore prefix (`_instance`, `_vars`)
- Public fields/properties: PascalCase (`Instance`, `IndexedVariables`)
- Local variables: camelCase (`holism`, `expr`, `transition`)

**Documentation:**
- Use `/** ... */` JavaDoc-style comments for class/method documentation
- Single-line comments with `//` for inline explanations
- XML doc comments rarely used (older codebase style)

**Patterns:**
- Singleton pattern for `Controller` (thread-safe lazy initialization)
- Factory pattern for creating Z3 expressions
- Visitor-like pattern for AST traversal in parsing

### 2. Variable Naming in Model

**Mathematical Variables (in XML and code):**
- `N` - Number of processes (system parameter)
- `i`, `j`, `k` - Process indices (quantified variables)
- `x[i]` - Indexed variable (one per process)
- `g` - Global variable (shared across processes)
- `x'` or `x&apos;` - Primed variable (next-state)
- `x_dot` - Derivative (continuous dynamics)
- `q[i]` - Location/mode variable

**C# Variable Naming:**
- `IndexedVariables` - Dictionary of indexed vars
- `IndexedVariablesPrimed` - Primed indexed vars
- `GlobalVariables` - Global variables
- `ParameterVariables` - System parameters (N, etc.)

### 3. XML Input Format

Input specifications use custom XML schema:

```xml
<holism>
  <!-- System parameters -->
  <parameter name='N' type='index' comment='number of processes' />
  <parameter name='A' type='real' comment='timing constant' />

  <!-- Global variables -->
  <variable name='g' type='index' update_type='Discrete' comment='lock' />

  <!-- Assumptions/constraints -->
  <assumption equn='A &gt; 0.0 and B &gt; A' comment='timing constraints' />
  <assumption equn='N &gt;= 2 and N &lt;= 100' comment='bounds' />

  <!-- Automaton definition -->
  <automaton name='fischer_protocol'>
    <!-- Indexed variables (per process) -->
    <variable name='x[i]' type='real' update_type='Continuous' comment='timer' />

    <!-- Initial condition -->
    <initial equn='(forall i (x[i] == 0.0)) and g == 0' />

    <!-- Locations/modes -->
    <mode id='0' name='idle' initial='True'>
      <dai variable='x[i]' equn='x_dot[i] = 1.0'/>
      <invariant equn='x[i] &lt;= 10.0' />
      <stop equn='x[i] &gt;= 10.0' />
    </mode>

    <!-- Transitions -->
    <transition source='idle' destination='trying'>
      <guard equn='g == 0' />
      <action equn='g&apos; == i and x&apos;[i] == 0.0' />
    </transition>
  </automaton>

  <!-- Safety property -->
  <property equn='(forall i (forall j (i != j implies not (q[i] == crit and q[j] == crit))))'
            type='safety'
            comment='mutual exclusion' />
</holism>
```

**Important XML Quirks:**
- Use `&gt;` for `>`, `&lt;` for `<`, `&apos;` for `'`
- Derivatives: `x_dot[i]` in DAI (differential-algebraic inclusion)
- Quantifiers: `forall i (...)`, `exists i (...)`
- Primed vars: `x&apos;[i]` for next-state
- Implications: `implies` keyword, not `=>`

### 4. Build Configurations

**Available Configurations:**
- `Debug` / `Release` - Standard .NET builds
- `bin-win` - Windows build (no Z3)
- `bin-win-z3` - Windows + Z3 4.2
- `bin-win-z3-unstable` - Windows + Z3 4.3.2
- `bin-mono` - Linux/Mono build (no Z3)
- `bin-mono-z3` - Linux/Mono + Z3 4.2
- `bin-mono-z3-unstable` - Linux/Mono + Z3 4.3.2

**Platform:** All build for x86 (32-bit) architecture

### 5. Verification Modes

The tool supports multiple modes (command-line flag):

- `INDUCTIVE_INVARIANT` - Check if property is inductive invariant
- `BMC` - Bounded model checking
- `BMC_SYMMETRIC` - BMC with symmetry reduction
- `INVISIBLE_INVARIANTS` - Invisible invariants synthesis
- `SPLIT_INVARIANTS` - Invariant decomposition
- `OUTPUT_EXTERNAL_TOOL` - Generate PHAVer input files

---

## Development Workflows

### Building the Project

**Prerequisites:**
- Visual Studio 2013 or later (or MSBuild on Linux)
- .NET Framework 4.0 SDK
- Mono (for Linux builds)
- Z3 binaries in `lib/` directory

**Windows Build:**
```bash
# Navigate to project directory
cd trunk/src/dotnet/passel/

# Build with MSBuild (use appropriate configuration)
msbuild passel.sln /p:Configuration=bin-win-z3 /p:Platform=x86

# Output will be in:
# trunk/src/dotnet/passel/bin/bin-win-z3/
```

**Linux/Mono Build:**
```bash
cd trunk/src/dotnet/passel/

# Build with xbuild (deprecated) or msbuild
xbuild passel.sln /p:Configuration=bin-mono-z3 /p:Platform=x86

# Or with modern Mono:
msbuild passel.sln /p:Configuration=bin-mono-z3 /p:Platform=x86
```

**Important Build Notes:**
- Z3 DLLs must be copied to output directory (post-build event handles this)
- On Windows: `libz3.dll` is renamed to `z3.dll`
- On Linux: Both `libz3.so` and `libz3.dll` needed
- ANTLR3 grammars are compiled during build
- Platform must be x86 (not Any CPU or x64)

### Running the Tool

**Command-line Syntax:**
```bash
# Windows
passel.exe [options] <input.xml>

# Linux/Mono
mono passel.exe [options] <input.xml>
```

**Common Options:**
- `--mode=<MODE>` - Verification mode (see above)
- `--timeout=<SECONDS>` - Z3 timeout
- `--output=<FILE>` - Output file path
- `--gui` - Enable GUI visualization (Windows only)
- `--verbose` - Detailed logging

**Example:**
```bash
# Check inductive invariant for Fischer protocol
mono passel.exe --mode=INDUCTIVE_INVARIANT trunk/input/fischer_umeno_global_clock_buggy.xml

# Run BMC with symmetry reduction
mono passel.exe --mode=BMC_SYMMETRIC --timeout=300 trunk/input/bakery-lynch.xml

# Generate PHAVer output
mono passel.exe --mode=OUTPUT_EXTERNAL_TOOL --output=output.pha trunk/input/token-ring.xml
```

### Testing

**Test Project:** `trunk/src/dotnet/passel_test/passel_test.csproj`

**Test Inputs:** ~74 XML files in `trunk/input/`
- Fischer protocol variants
- Bakery algorithm (Lynch)
- Token ring protocols
- GCD computation
- SATS collision avoidance
- German cache coherence

**Running Tests:**
```bash
# Build test project
msbuild passel_test.csproj /p:Configuration=Debug

# Run tests (NUnit or manual execution)
# Note: Tests may be manual verification scripts rather than unit tests
```

---

## Common Tasks for AI Assistants

### 1. Adding a New Verification Mode

1. Add enum value to `PROGRAM_MODE` in `Controller.cs`
2. Implement verification logic in appropriate model class (e.g., `Holism.cs`, `ReachSymmetric.cs`)
3. Add command-line parsing in `Controller.Main()`
4. Wire up the mode in `Controller.Instance` workflow
5. Test with relevant input XML files

### 2. Modifying Z3 Integration

**Key Files:**
- `trunk/src/dotnet/passel/controller/smt/z3/Z3Wrapper.cs`

**Common Modifications:**
- Adjust solver tactics (quantifier elimination, simplification)
- Change timeout settings
- Add new Z3 API calls
- Handle new Z3 theories (arrays, datatypes, etc.)

**Z3 Version Compatibility:**
- Be aware of API changes between Z3 4.1, 4.2, and 4.3.2
- Test changes with all supported Z3 versions
- Quantifier elimination tactics changed significantly in 4.3.2

### 3. Extending the Input Language

1. Modify ANTLR3 grammar in `trunk/src/dotnet/passel/controller/parsing/*.g3`
2. Regenerate parser (automatic during build)
3. Update `ParseHyXML.cs` to handle new constructs
4. Extend model classes (`Holism.cs`, `Variable.cs`, etc.)
5. Update Z3 translation in `Z3Wrapper.cs`
6. Add test cases in `trunk/input/`

### 4. Adding New Output Formats

1. Create new output generator in `trunk/src/dotnet/passel/controller/output/`
2. Implement translation from internal model to target format
3. Follow pattern from `PrintPhaver.cs`
4. Add command-line option in `Controller.cs`
5. Test with various input specifications

### 5. Debugging Verification Failures

**Debugging Tools:**
- `Debug.cs` - Utility methods for printing Z3 expressions, models
- Console logging (verbose mode)
- Z3 proof/unsat core generation
- PHAVer output for external validation

**Common Issues:**
- Quantifier instantiation failures → Check Z3 tactics
- Timeout → Increase timeout, simplify model
- Unknown result → Try different Z3 version or tactics
- Incorrect property → Verify XML encoding, check for typos

**Debugging Workflow:**
1. Enable verbose logging
2. Check Z3 queries generated (print to console)
3. Test Z3 queries independently (SMT-LIB format)
4. Simplify input specification to minimal failing case
5. Compare with known-working examples

---

## Important Gotchas and Notes

### 1. Platform-Specific Issues

**Windows vs. Linux:**
- GUI (`View.cs`) only works on Windows (disabled with `#if !MONO`)
- GraphSharp visualization not available on Mono
- Z3 DLL naming differs: `z3.dll` (Windows) vs. `libz3.so` + `libz3.dll` (Linux)
- File paths: Use `Path.Combine()` for cross-platform compatibility

### 2. Z3 Version Differences

**Critical Differences:**
- Z3 4.3.2 changed quantifier elimination tactics
- Some properties provable in 4.2 return "unknown" in 4.3.2 and vice versa
- API method signatures changed between versions
- Always test with the specific Z3 version used in production

### 3. Build System Quirks

**Must Know:**
- Clean build may not work properly → Use COPY instead of clean (per README.txt)
- Z3 DLLs must be manually copied to output directory
- Platform must be x86, not Any CPU
- Post-build events critical for copying dependencies

### 4. XML Encoding

**Common Mistakes:**
- Forgetting to encode `<`, `>`, `'` in XML
- Using `=>` instead of `implies` for implication
- Mixing primed/unprimed variables incorrectly
- Quantifier scope issues: `(forall i (forall j (...)))` nesting

### 5. Memory and Performance

**Large Systems:**
- Verification time grows exponentially with system size (N)
- Z3 memory usage can be very high for complex properties
- Symmetry reduction crucial for scalability
- BMC depth should be limited to avoid state explosion

### 6. Research Tool Limitations

**Be Aware:**
- This is a research prototype, not production software
- Error handling may be minimal in some code paths
- Documentation sparse in some areas
- Some features may be experimental/incomplete
- Original development circa 2013-2014 (older .NET practices)

---

## Working with This Codebase

### Code Navigation Tips

**Entry Points:**
1. `Controller.Main()` - Program entry point
2. `Controller.Instance` - Singleton orchestrator
3. `Holism.cs` - Top-level system model
4. `ParseHyXML.cs` - Input file parsing
5. `Z3Wrapper.cs` - SMT solver interaction

**Key Data Structures:**
- `Holism` - Complete system specification
- `AHybridAutomaton` - Automaton abstraction
- `Transition` - Transition representation
- `Property` - Safety/liveness properties
- `Variable*` - Variable hierarchy (global, indexed)

### Modification Strategy

1. **Understand the verification workflow:**
   - Parse XML → Build model → Construct Z3 queries → Check satisfiability → Report results

2. **Identify the relevant layer:**
   - Parser layer: Input language changes
   - Model layer: Representation changes
   - Controller layer: Workflow/orchestration changes
   - SMT layer: Z3 interaction changes

3. **Make incremental changes:**
   - Test with simple examples first
   - Validate against known-correct results
   - Add logging/debugging output
   - Document assumptions and limitations

4. **Follow existing patterns:**
   - Singleton for Controller
   - Factory methods for Z3 expressions
   - Visitor-like patterns for AST traversal
   - Defensive null checks before Z3 calls

### Testing Strategy

**Manual Testing:**
1. Use small input files from `trunk/input/`
2. Start with simple properties (e.g., `gcd.xml`)
3. Progress to complex protocols (e.g., `bakery-lynch.xml`)
4. Compare results with known outcomes
5. Check for regressions in existing tests

**Automated Testing:**
- Create scripts to run all input files
- Compare output logs with baseline
- Check for crashes, timeouts, incorrect results
- Performance regression testing

---

## Git Workflow

**Current Branch:** `claude/claude-md-mi43plxhsfql8zpq-01Q1fuB6tJgYhBb1v91AFeou`

**Branch Strategy:**
- Develop on feature branches prefixed with `claude/`
- Commit frequently with descriptive messages
- Push to designated branch when changes complete

**Commit Message Style:**
Based on existing commits:
- Use descriptive messages explaining what changed and why
- Reference issue numbers if applicable
- Example: "added support for different versions of Z3 based on selected configuration"

**Important:** Always push to the correct branch with `git push -u origin <branch-name>`

---

## Resources and References

**External Tools:**
- **Z3 Theorem Prover:** https://github.com/Z3Prover/z3
- **PHAVer:** Polyhedral hybrid automaton verifier (Goran Frehse)
- **ANTLR 3:** Parser generator (www.antlr.org)

**Related Research:**
- Parameterized verification
- Symmetry reduction techniques
- Invisible invariants method
- SMT-based verification
- Hybrid automata verification

**Documentation:**
- `README.txt` - Build notes and design lessons
- XML comments in code (sparse)
- Example input files in `trunk/input/`

---

## Summary for AI Assistants

When working on PASSEL:

1. **Understand the domain:** This is formal verification, not typical software development
2. **Respect mathematical precision:** Variable names, formulas, and logic must be exact
3. **Test with Z3 in mind:** SMT solver behavior is critical and sometimes unpredictable
4. **Use existing examples:** The `trunk/input/` directory has excellent test cases
5. **Mind the platform:** Windows vs. Mono has real differences
6. **Be careful with Z3 versions:** Behavior varies significantly across versions
7. **Follow the MVC pattern:** Model, Controller, View separation is important
8. **Document changes:** This is research code, future researchers need context

**When in doubt:**
- Look at similar existing code
- Test with simple examples first
- Check Z3 documentation for API questions
- Validate against known-correct results

---

**Last Updated:** 2025-11-18
**Repository:** github.com/[organization]/passel
**License:** [Check repository for license information]
