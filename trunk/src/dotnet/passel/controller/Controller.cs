using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using System.Diagnostics;
using System.Threading;

using System.IO;

using Microsoft.Z3;

//using VixCOM;

using passel.controller;

using passel.model;
using passel.controller.output;
using passel.controller.smt;
using passel.controller.smt.z3;
using passel.controller.parsing;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using System.Windows.Forms;

namespace passel.controller
{
    /**
     * Main interface between external libraries (parsing, SMT solving, etc.) and local model manipulation and abstraction
     */
    public class Controller
    {
        /**
         * Singleton instance
         */
        private static Controller instance;

        /**
         * Z3 context (wrapper around it)
         */
        private Z3Wrapper _z3;

        /**
         * Special variable for control states / locations (modes)
         * - All other variables go into the _vars dictionary
         */
        //private IDictionary<String, Expr> _q;

        /**
         * Special variable for control states / locations (modes)
         * - All other variables go into the _vars dictionary
         */
        //private IDictionary<String, Expr> _qPrimed;
        
        /**
         * Indexed variables: input, e.g., (x i) returns the function corresponding to variable x at process i
         * 
         */
        private IDictionary<KeyValuePair<String, String>, Expr> _ivars;

        /**
         * Primed indexed variables: input, e.g., (x' i) returns the function corresponding to variable x at process i
         * 
         */
        private IDictionary<KeyValuePair<String, String>, Expr> _ivarsPrimed;

        /**
         * Parameter variables (N, S, etc.)
         */
        private IDictionary<String, Expr> _params;

        public IDictionary<String, Expr> UndefinedVariables;


        /**
         * Global variables
         */
        private IDictionary<String, Expr> _globalVariables;

        public IDictionary<String, FuncDecl> Functions;

        /**
         * Primed global variables
         */
        private IDictionary<String, Expr> _globalVariablesPrimed;

        /**
         * Location labels to value map
         */
        private IDictionary<String, Expr> _locations;

        /**
         * Process indices (i, j, k, etc.)
         */
        private IDictionary<String, Expr> _indices;

        /**
         * integer for control state
         */
        private UInt32 _qv = 0;

        /**
         * Set used to index processes
         */
        private Expr IndexSet;

        /**
         * Integer value of one
         */
        public Expr IntOne;

        public Expr IndexNone;
        public Expr IndexOne;
        public Expr IndexN;

        /**
         * Value selected for N (if any)
         */
        public uint IndexNValue;

        public uint IndexNValueLower;
        public uint IndexNValueUpper;

        public Expr RealInf;

        /**
         * I/O directory paths
         */
        public String InOutPath; // passel base directory name
        public String ReachPathWindows;
        public String ReachPathLinux;
        public String PhaverPathWindows;
        public String PhaverPathLinux;
        public String MemtimePathLinux;
        public String BatchSuffix; // for generating all output files (e.g., hscc2013, cav2013, etc)
        public String PhaverInputPathLinux;
        public String OutPath; // passel output file path (logs, phaver input files, etc.)
        public String InputPath; // passel input file path

        public String VMPath;

        /**
         * filename
         */
        public String InputFile;

        public List<String> InputFiles;

        /**
         * input file path
         */
        public String InputFilePath;

        /**
         * theory used to model variables of each agent in the system
         */
        public enum DataOptionType { array, uninterpreted_function };

        /**
         * set used to model indices of processes
         */
        public enum IndexOptionType { integer, natural, naturalOneToN, enumeration };

        public Dictionary<UInt32, String> LocationNumToName;

        public Dictionary<String, UInt32> LocationNameToNum;

        public Dictionary<Expr, String> LocationNumTermToName;

        /**
         * implies is weak, and is strict
         */
        public enum ExistsOptionType { implies, and }; // implies doesn't work

        /**
         * conjunction uses a conjunction of implications on control locations in the time transition, whereas separated checks the time transition repeatedly based on each location
         */
        public enum TimeOptionType { conjunction, separated };

        public DataOptionType DataOption = DataOptionType.uninterpreted_function;

        public IndexOptionType IndexOption = IndexOptionType.naturalOneToN;

        public ExistsOptionType ExistsOption = ExistsOptionType.and;

        public TimeOptionType TimeOption = TimeOptionType.conjunction;

        public Stopwatch TimerStats = new Stopwatch();

        public Dictionary<string,string> Config;

        public const String PRIME_SUFFIX = "'";
        public const String PRIME_SUFFIX_PARSER = "&apos;";
        public const String DOT_SUFFIX = "_dot";

        public const bool LOG_Z3 = false; // enable / disable z3 re-runnable log


        /**
         * Singleton constructor
         */
        private Controller()
        {
            this.InitializeZ3();

            this.InputFiles = new List<string>(); // don't want to trash these between calls
        }

        /**
         * Instantiate data structures, create Z3 object, populate data structures with pointers to Z3 objects, etc.
         */
        private void InitializeZ3()
        {
            //this._q = new Dictionary<String, Expr>();
            //this._qPrimed = new Dictionary<String, Expr>();
            this._ivars = new Dictionary<KeyValuePair<String, String>, Expr>();
            this._ivarsPrimed = new Dictionary<KeyValuePair<String, String>, Expr>();
            this._params = new Dictionary<String, Expr>();
            this.ParamsAssumps = new Dictionary<String, Expr>();
            this._globalVariables = new Dictionary<String, Expr>();
            this._globalVariablesPrimed = new Dictionary<String, Expr>();
            this.UndefinedVariables = new Dictionary<String, Expr>();
            this._locations = new Dictionary<String, Expr>();
            this._indices = new Dictionary<String, Expr>();
            this.LocationNumToName = new Dictionary<UInt32, String>();
            this.LocationNameToNum = new Dictionary<String, UInt32>();
            this.LocationNumTermToName = new Dictionary<Expr, String>();
            this.Functions = new Dictionary<String, FuncDecl>();

            this.Config = new Dictionary<string, string>();

            this.Config.Add("AUTO_CONFIG", "false"); // disable auto-configuration (use all logics)

            // fixed point options
            //this.Config.Add("DL_COMPILE_WITH_WIDENING", "true");
            //this.Config.Add("DL_UNBOUND_COMPRESSOR", "false"); 

            /*this.Config.Add("ARRAY_CANONIZE", "true");
            this.Config.Add("ARRAY_CG", "true");
            this.Config.Add("ARRAY_LAZY_IEQ", "true");
            this.Config.Add("ARRAY_WEAK", "true");
             */
            //this.Config.Add("ARRAY_SOLVER", "1"); // 0 to 3

            //this.Config.Add("QI_PROFILE", "true");
            //this.Config.Add("QI_PROFILE_FREQ", "1000");
            //this.Config.Add("MBQI_TRACE", "true");

            this.Config.Add("MODEL", "true");
            this.Config.Add("MBQI", "true"); //  (see http://research.microsoft.com/en-us/um/redmond/projects/z3/mbqi-tutorial/)


            //this.Config.Add("SOFT_TIMEOUT", "15000"); // in ms
            this.Config.Add("MODEL_ON_TIMEOUT", "true");
            
            //this.Config.Add("MBQI_MAX_CEXS", "500"); // crashes
            //this.Config.Add("MBQI_MAX_CEXS_INCR", "100");
            //this.Config.Add("MBQI_MAX_ITERATIONS", "50000");

            //this.Config.Add("NNF_MODE", "3"); // min: 0, max: 3, default: 0, NNF translation mode: 0 - skolem normal form, 1 - 0 + quantifiers in NNF, 2 - 1 + opportunistic, 3 - full.

            // HUGE runtime differences (3 was extremely slow); 1 also slow
            this.Config.Add("CNF_MODE", "0");

            this.Config.Add("QI_QUICK_CHECKER", "2"); // min: 0, max: 2, default: 0, 0 - do not use (cheap) model checker, 1 - instantiate instances unsatisfied by current model, 2 - 1 + instantiate instances not satisfied by current model.

            this.Config.Add("RECENT_LEMMA_THRESHOLD", "10000"); // default 100

            this.Config.Add("REDUCE_ARGS", "true");

            this.Config.Add("REL_CASE_SPLIT_ORDER", "1");

            this.Config.Add("BB_QUANTIFIERS", "true");

            //this.Config.Add("INST_GEN", "true");

            //this.Config.Add("QI_PROFILE", "true");



            // the following option was deprecated in version 4.3 of Z3 (latest version that can use it is 4.1)
            if (Microsoft.Z3.Version.Major <= 4 && Microsoft.Z3.Version.Minor <= 1)
            {
                this.Config.Add("ELIM_QUANTIFIERS", "true"); // if we fix N to be small, we can rely on MBQI, but if we have N large or unbounded, we may need Q.E.
            }
            this.Config.Add("ELIM_NLARITH_QUANTIFIERS", "true");
            this.Config.Add("ELIM_BOUNDS", "true");
            this.Config.Add("QI_LAZY_INSTANTIATION", "true");

            this.Config.Add("PULL_CHEAP_ITE_TREES", "true");
            this.Config.Add("EMATCHING", "true");
            this.Config.Add("MACRO_FINDER", "true");
            this.Config.Add("STRONG_CONTEXT_SIMPLIFIER", "true");
            this.Config.Add("CONTEXT_SIMPLIFIER", "true");

            //this.Config.Add("PI_NON_NESTED_ARITH_WEIGHT", "10");
            this.Config.Add("PI_PULL_QUANTIFIERS", "true");     // check with on / off 
            this.Config.Add("PULL_NESTED_QUANTIFIERS", "true"); // check with on / off (see mbqi tutorial)
            this.Config.Add("MODEL_PARTIAL", "false");
            this.Config.Add("MODEL_V2", "true");
            //this.Config.Add("VERBOSE", "10");

            this.Config.Add("DISPLAY_ERROR_FOR_VISUAL_STUDIO", "true");
            this.Config.Add("DISTRIBUTE_FORALL", "true");
            //this.Config.Add("SOLVER", "true");                              // SOLVER: boolean, default: false, enable solver during preprocessing step.

            this.Config.Add("MODEL_COMPACT", "true"); // slower, but more accurate (as in the models are more useful) it seems
            //this.Config.Add("MODEL_ON_FINAL_CHECK", "true"); // leave this off, prints lots of warnings, etc., but not to console out, might be a debug stream we aren't redirecting
            this.Config.Add("MODEL_COMPLETION", "false");
            this.Config.Add("DISPLAY_UNSAT_CORE", "false");

            this.Config.Add("Z3_SOLVER_LL_PP", "true");
            //this.Config.Add("Z3_SOLVER_SMT_PP", "true");


            this.Config.Add("PP_MAX_DEPTH", "32");
            this.Config.Add("PP_MIN_ALIAS_SIZE", "1000");
            this.Config.Add("PP_DECIMAL", "true");
            //this.Config.Add("PP_MIN_ALIAS_SIZE", "true");
            this.Config.Add("PP_SIMPLIFY_IMPLIES", "true");
            

            // bad syntax for next...
            //this.Config.Add("produce-proofs", "true");
            //this.Config.Add("produce-models", "true");
            //this.Config.Add("produce-unsat-cores", "true");
            //this.Config.Add("produce-assignments", "true");
            //this.Config.Add("expand-definitions", "true");

            //this.Config.Add("CNF_FACTOR", "10");
            //this.Config.Add("CNF_MODE", "3");

            //todo: SOFT_TIMEOUT // can use this option to force queries to return unknown instead of running forever

            //this.Config.Add("SPC", "true");

            //this.Config.Add("STATISTICS", "true"); // crashes
            /*
            this.Config.Add("ARITH_SOLVER", "2"); // simplex solver

            // we need nonlinear real arithmetic for converting the rectangular flow relation to a flow function
            this.Config.Add("NL_ARITH", "true"); // nonlinear arithmetic support: requires arith_solver 2
            this.Config.Add("NL_ARITH_GB_EQS", "true"); // boolean, default: false, enable/disable equations in the Grobner Basis to be copied to the Simplex tableau..
            this.Config.Add("NL_ARITH_ROUNDS", "2048"); // unsigned integer, default: 1024, threshold for number of (nested) final checks for non linear arithmetic..
            this.Config.Add("NL_ARITH_GB_THRESHOLD", "1024"); // unsigned integer, default: 512, Grobner basis computation can be very expensive. This is a threshold on the number of new equalities that can be generated..
            */
/*
NL_ARITH: boolean, default: true, enable/disable non linear arithmetic support. This option is ignored when ARITH_SOLVER != 2..
NL_ARITH_BRANCHING: boolean, default: true, enable/disable branching on integer variables in non linear clusters.
NL_ARITH_GB: boolean, default: true, enable/disable Grobner Basis computation. This option is ignored when NL_ARITH=false.
NL_ARITH_GB_PERTURBATE: boolean, default: true, enable/disable perturbation of the variable order in GB when searching for new polynomials..
NL_ARITH_MAX_DEGREE: unsigned integer, default: 6, max degree for internalizing new monomials..
 */


            //this.Config.Add("ARITH_ADAPTIVE", "true"); // TODO: REENABLE
            //this.Config.Add("ARITH_PROCESS_ALL_EQS", "true"); // TODO: RENABLE


            //this.Config.Add("ARITH_EUCLIDEAN_SOLVER", "true");
            //this.Config.Add("ARITH_FORCE_SIMPLEX", "true");
            //this.Config.Add("ARITH_MAX_LEMMA_SIZE", "512"); // default 128

            //this.Config.Add("CHECK_PROOF", "true");
            //this.Config.Add("DL_COMPILE_WITH_WIDENING", "true");
            //this.Config.Add("DACK", "2");
            //this.Config.Add("DACK_EQ", "true");

            // some bugs in the next ones
            //this.Config.Add("FWD_SR_CHEAP", "true");
            //this.Config.Add("LOOKAHEAD", "true");
            //this.Config.Add("MBQI_MAX_CEXS", "true"); // crashes
            //this.Config.Add("MODEL_VALIDATE", "true"); // corrupts memory?
            // end buggy ones


            //this.Config.Add("LOOKAHEAD_DISEQ", "true");

            //this.Config.Add("LIFT_ITE", "2"); // buggy: get memory corruption sometimes
            //this.Config.Add("ELIM_TERM_ITE", "true"); // buggy: get memory corruption sometimes

            //this.Config.Add("MINIMIZE_LEMMAS_STRUCT", "true");
            //this.Config.Add("MODEL_DISPLAY_ARG_SORT", "true");



            //this.Config.Add("enable-cores", "true");

            //this.Config.Add("DISPLAY_PROOF", "true");
            //this.Config.Add("PROOF_MODE", "1"); // BUG: DO NOT USE THIS OPTION, IT CAN CAUSE FORMULAS TO TOGGLE SATISFIABILITY

            this.Z3 = new Z3Wrapper(this.Config);
            this.Z3.PrintMode = Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT;

            this.IntType = Z3.MkIntSort();
            this.RealType = Z3.MkRealSort();
            //this.LocType = Z3.MkUninterpretedSort("loc");
            //this.LocType = Z3.MkIntSort();
            this.LocType = Z3.MkBitVecSort(this.LocSize);

            this.RealZero = Z3.MkReal(0);
            this.IntZero = Z3.MkInt(0);
            this.IntOne = Z3.MkInt(1);

            /* can't do the following to create augmented reals: assumptions are invalid
            this.RealInf = Z3.MkRealConst("inf");
            Term assumpInf;
            Term assumpInfBound = Z3.MkRealConst("anyRealValue");
            assumpInf = Z3.MkForall(0, new Term[] {assumpInfBound}, null, this.RealInf >= assumpInfBound);
            this.Z3.AssertCnstr(assumpInf);
            this.Params.Add("inf", this.RealInf);
             * */

            switch (this.IndexOption)
            {
                case IndexOptionType.integer:
                    {
                        //this._indexType = Z3.MkSetSort(Z3.MkIntSort());
                        this.IndexType = Z3.MkIntSort();
                        this.IndexNone = Z3.MkInt(0);
                        this.IndexOne = Z3.MkInt(1);
                        this.Params.Add("N", Z3.MkIntConst("N"));
                        this.IndexN = this.Params["N"];
                        break;
                    }
                case IndexOptionType.natural:
                    {
                        this.IndexType = Z3.MkIntSort();
                        this.IndexNone = Z3.MkInt(0);
                        this.IndexOne = Z3.MkInt(1);
                        this.Params.Add("N", Z3.MkIntConst("N"));
                        this.IndexN = this.Params["N"];
                        break;
                    }
                case IndexOptionType.naturalOneToN:
                    {
                        this.IndexType = Z3.MkIntSort();
                        this.IndexNone = Z3.MkInt(0);
                        this.IndexOne = Z3.MkInt(1);
                        this.Params.Add("N", Z3.MkIntConst("N"));
                        this.IndexN = this.Params["N"];
                        break;
                    }
                case IndexOptionType.enumeration:
                default:
                    {
                        //this._indexType = Z3.MkEnumerationSort("index", new string[] { "i1", "i2", "i3", "i4" });
                        this.IndexType = Z3.MkEnumSort("index", new string[] { "i0", "i1", "i2", "i3", "i4" }); // todo: parse the value of N, then create a sort with this many distinct elements
                        this.IndexOne = Z3.MkConst("i1", this.IndexType);
                        this.IndexNone = Z3.MkConst("i0", this.IndexType);
                        this.IndexN = Z3.MkConst("iN", this.IndexType);
                        break;
                    }
            }

            //this._indexSet = Z3.MkFullSet((SetSort)this._indexType); // todo: check if legal cast

            switch (this.DataOption)
            {
                case DataOptionType.array:
                    {
                        this.DataA.IndexedVariableDecl = new Dictionary<String, ArrayExpr>();
                        this.DataA.IndexedVariableDeclPrimed = new Dictionary<String, ArrayExpr>();
                        this.DataA.VariableDecl = new Dictionary<String, ArrayExpr>();
                        this.DataA.VariableDeclPrimed = new Dictionary<String, ArrayExpr>();
                        break;
                    }

                case DataOptionType.uninterpreted_function:
                default:
                    {
                        this.DataU.IndexedVariableDecl = new Dictionary<String, FuncDecl>();
                        this.DataU.IndexedVariableDeclPrimed = new Dictionary<String, FuncDecl>();
                        this.DataU.VariableDecl = new Dictionary<String, FuncDecl>();
                        this.DataU.VariableDeclPrimed = new Dictionary<String, FuncDecl>();
                        break;
                    }
            }


            // constants
            Expr int_zero = this.Z3.MkInt(0);
            Expr int_one = this.Z3.MkInt(1);
            Expr int_two = this.Z3.MkInt(2);
            Expr real_one = this.Z3.MkReal(1);

            // process index variables
            this._indices = new Dictionary<String, Expr>();

            this._indices.Add("h", this.Z3.MkIntConst("h"));
            this._indices.Add("i", this.Z3.MkIntConst("i"));
            this._indices.Add("j", this.Z3.MkIntConst("j"));
            this._indices.Add("k", this.Z3.MkIntConst("k"));
            this._indices.Add("l", this.Z3.MkIntConst("l"));
            this._indices.Add("m", this.Z3.MkIntConst("m"));
            this._indices.Add("n", this.Z3.MkIntConst("n"));

            /*
            this._indices.Add("h", this.Z3.MkConst("h", this.IndexType));
            this._indices.Add("i", this.Z3.MkConst("i", this.IndexType));
            this._indices.Add("j", this.Z3.MkConst("j", this.IndexType));
            Instance._indices.Add("k", this.Z3.MkConst("k", this.IndexType));
            this._indices.Add("l", this.Z3.MkConst("l", this.IndexType));
            this._indices.Add("m", this.Z3.MkConst("m", this.IndexType));
            this._indices.Add("n", this.Z3.MkConst("n", this.IndexType));
             */

            this.ExistentialConstants = new Dictionary<String, Expr>();

            ISmtSymbols smtSymbols = new SymbolsZ3();

            //this.Z3.EnableDebugTrace("debug");
        }

        /**
         * Singleton
         */
        public static Controller Instance
        {
            get 
            {
                if (instance == null)
                {
                    instance = new Controller();
                }
                return instance;
            }
        }

        /**
         * Gettor and settor for Z3 object
         */
        public Z3Wrapper Z3
        {
            get { return this._z3; }
            set { this._z3 = value; }
        }

        /**
         * Integer zero value
         */
        public Expr IntZero;

        /**
         * Real zero value
         */
        public ArithExpr RealZero;

        /**
         * Integer type
         */
        public Sort IntType;

        /**
         * Control location (state) type
         */
        public Sort LocType;

        /**
         * Number of bits for locations (states)
         */
        public uint LocSize = 4; // TODO: determine based on input file---going to require two parsing phases (since the control location sort is defined as a function of this size)

        /**
         * Index type: natural number between 1 and N
         */
        public Sort IndexType;

        /**
         * Real sort
         */
        public Sort RealType;

        /**
         * Indexed control locations / modes
         
        public IDictionary<String, Expr> Q
        {
            get { return this._q; }
            set { this._q = value; }
        }*/

        /**
         * Primed (for resets) Indexed control locations / modes
         
        public IDictionary<String, Expr> QPrimed
        {
            get { return this._qPrimed; }
            set { this._qPrimed = value; }
        }*/

        /**
         * Gettor and settor for indexed variables
         */
        public IDictionary<KeyValuePair<String, String>, Expr> IndexedVariables
        {
            get { return this._ivars; }
            set { this._ivars = value; }
        }

        /**
         * Gettor and settor for primed indexed variables
         */
        public IDictionary<KeyValuePair<String, String>, Expr> IndexedVariablesPrimed
        {
            get { return this._ivarsPrimed; }
            set { this._ivarsPrimed = value; }
        }

        /**
         * Index variables
         */
        public IDictionary<String, Expr> Indices
        {
            get { return this._indices; }
            set { this._indices = value; }
        }

        /**
         * Parameter variables
         */
        public IDictionary<String, Expr> Params
        {
            get { return this._params; }
            set { this._params = value; }
        }

        public IDictionary<String, Expr> ParamsAssumps; // TODO: refactor by adding a combined variable / parameter class, where params are variables with a "constant" / null update type, then has assumps be a member of this class

        /**
         * Global variables
         */
        public IDictionary<String, Expr> GlobalVariables
        {
            get { return this._globalVariables; }
            set { this._globalVariables = value; }
        }

        /**
         * Primed global variables
         */
        public IDictionary<String, Expr> GlobalVariablesPrimed
        {
            get { return this._globalVariablesPrimed; }
            set { this._globalVariablesPrimed = value; }
        }

        /**
         * Location labels to values
         */
        public IDictionary<String, Expr> Locations
        {
            get { return this._locations; }
            set { this._locations = value; }
        }

        public AgentDataArray DataA = new AgentDataArray(); // todo: refactor, use AAgentDataTheory super class with appropriate generics
        public AgentDataUninterpreted DataU = new AgentDataUninterpreted(); // todo: refactor

        public Holism Sys;

        public String InputFileExtension = ".xml";

        public IDictionary<String, Expr> ExistentialConstants;

        enum IOSTATE { SELECT_CASE_STUDY, SELECT_N, SELECT_OPERATION, EXECUTE_OPERATION };

        enum PROGRAM_MODE { INDUCTIVE_INVARIANT, OUTPUT_PHAVER, INPUT_PHAVER, INVISIBLE_INVARIANTS, SPLIT_INVARIANTS, BMC, DRAW_SYSTEM };
        private PROGRAM_MODE OPERATION;

        public view.View View;

        public static void ThreadDisplay()
        {
            Instance.View = new view.View(); // note, only the view thread will be able to modify
            Application.Run(Instance.View);
            Instance.View.Show();
        }

        enum PHAVER_INPUT_MODE { reachable_forward, reachable_backward };

        public static Expr[] getNIndices(uint N)
        {
            List<Expr> ids = new List<Expr>();
            for (uint i = 1; i <= N; i++)
            {
                uint idx = 'i' + i - 1;
                string sidx = ((char)idx).ToString();
                ids.Add(Instance.Indices[ sidx ]);
            }
            return ids.ToArray();
        }

        /**
         * Main entry to program
         * Accepts console input
         * @param args
         */
        public static void Main(String[] args)
        {
            String choice;
            Boolean selected_file = false, selected_n = false, selected_operation = false, terminate = false;
            Dictionary<int, string> inputFiles = new Dictionary<int, string>();
            int inputFileCount = 0;
            inputFiles.Add(inputFileCount++, "fischer_umeno.xml");
            inputFiles.Add(inputFileCount++, "fischer_umeno_buggy.xml");
            inputFiles.Add(inputFileCount++, "fischer_umeno_five_state.xml");
            inputFiles.Add(inputFileCount++, "fischer_umeno_five_state_buggy.xml");
            inputFiles.Add(inputFileCount++, "fischer_umeno_global_clock.xml");
            inputFiles.Add(inputFileCount++, "fischer_umeno_global_clock_buggy.xml");

            inputFiles.Add(inputFileCount++, "fischer_aux.xml");

            inputFiles.Add(inputFileCount++, "fischer_phaver.xml");
            inputFiles.Add(inputFileCount++, "fischer_phaver_const.xml");
            inputFiles.Add(inputFileCount++, "fischer_phaver_const_lastin.xml");

            inputFiles.Add(inputFileCount++, "fischer.xml");
            inputFiles.Add(inputFileCount++, "fischer_buggy.xml");

            inputFiles.Add(inputFileCount++, "fischer_bit.xml");

            inputFiles.Add(inputFileCount++, "fischer-equiv.xml");

            inputFiles.Add(inputFileCount++, "fischer-inv.xml");

            inputFiles.Add(inputFileCount++, "lynch_shavit.xml");

            inputFiles.Add(inputFileCount++, "sats_full.xml");
            inputFiles.Add(inputFileCount++, "sats.xml");
            inputFiles.Add(inputFileCount++, "sats_buggy.xml");
            inputFiles.Add(inputFileCount++, "sats_timed.xml");
            inputFiles.Add(inputFileCount++, "sats_timed_buggy.xml");
            inputFiles.Add(inputFileCount++, "sats_timed_counter.xml");

            inputFiles.Add(inputFileCount++, "sats-ii.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-harder.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-harder-3loc.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-harder-3loc-global-pointer.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-harder-basefinal.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-harder-sides.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-harder-sides-miss.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-harder-sides-miss-dynamics.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-harder-sides-miss-global.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-harder-sides-miss-global-dynamics.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-harder-sides-miss-global-pointer.xml");
            inputFiles.Add(inputFileCount++, "sats-ii-pointer.xml");

            inputFiles.Add(inputFileCount++, "mux-sem.xml");
            inputFiles.Add(inputFileCount++, "mux-sem-lastin.xml");
            inputFiles.Add(inputFileCount++, "mux-index.xml");
            inputFiles.Add(inputFileCount++, "mux-index-ta.xml");

            inputFiles.Add(inputFileCount++, "mux-sats.xml");

            inputFiles.Add(inputFileCount++, "ta-general.xml");

            inputFiles.Add(inputFileCount++, "ta-general-bool.xml");

            inputFiles.Add(inputFileCount++, "djikstra.xml");

            inputFiles.Add(inputFileCount++, "bakery-lynch.xml");

            inputFiles.Add(inputFileCount++, "german.xml");

            inputFiles.Add(inputFileCount++, "peterson.xml");
            inputFiles.Add(inputFileCount++, "szymanski.xml");

            inputFiles.Add(inputFileCount++, "token-ring.xml");

            inputFiles.Add(inputFileCount++, "bakery.xml");
            inputFiles.Add(inputFileCount++, "bakery_lamport.xml");
            inputFiles.Add(inputFileCount++, "bakery_lamport_buggy.xml");

            inputFiles.Add(inputFileCount++, "nfa.xml");
            inputFiles.Add(inputFileCount++, "nfa_buggy.xml");
            inputFiles.Add(inputFileCount++, "ta.xml");
            inputFiles.Add(inputFileCount++, "ta_buggy.xml");
            inputFiles.Add(inputFileCount++, "ra.xml");
            inputFiles.Add(inputFileCount++, "gv.xml");
            //inputFiles.Add(inputFileCount++, "gv_buggy.xml");
            inputFiles.Add(inputFileCount++, "flocking.xml");
            inputFiles.Add(inputFileCount++, "flocking_buggy.xml");
            inputFiles.Add(inputFileCount++, "bully.xml");
            inputFiles.Add(inputFileCount++, "bully_buggy.xml");

            inputFiles.Add(inputFileCount++, "gcd.xml");

            inputFiles.Add(inputFileCount++, "starl.xml");

            inputFiles.Add(inputFileCount++, "pointer-example.xml");
            inputFiles.Add(inputFileCount++, "gpointer-example.xml");


            inputFiles.Add(inputFileCount++, "hscc-example.xml");

            inputFiles.Add(inputFileCount++, "clock-sync.xml");

            inputFiles.Add(inputFileCount++, "prelim.xml");

            if (System.Environment.MachineName.ToLower().StartsWith("johnso99"))
            {
                Instance.InOutPath = "C:\\Documents and Settings\\tjohnson\\My Documents\\My Dropbox\\Research\\tools\\passel\\repos\\trunk\\";
            }
            else if (System.Environment.MachineName.ToLower().StartsWith("lh-laptop-w7"))
            {
                Instance.InOutPath = "C:\\Users\\tjohnson\\Dropbox\\Research\\tools\\passel\\repos\\trunk\\";
            }
            else if (System.Environment.MachineName.ToLower().StartsWith("lh-laptop-w8"))
            {
                Instance.InOutPath = "D:\\Dropbox\\Research\\tools\\passel\\repos\\trunk\\";
            }
            else
            {
                Instance.InOutPath = Directory.GetCurrentDirectory();
            }

            Instance.InputPath = Instance.InOutPath + "input\\";
            Instance.OutPath = Instance.InOutPath + "output\\";

            Instance.PhaverPathLinux = "/mnt/hgfs/Dropbox/Research/tools/phaver/";
            Instance.MemtimePathLinux = "/mnt/hgfs/Dropbox/Research/tools/memtime/memtime-1.3/memtime";
            Instance.BatchSuffix = "cav2013";
            Instance.PhaverInputPathLinux = "/mnt/hgfs/Dropbox/Research/tools/passel/repos/trunk/output/phaver/" + Instance.BatchSuffix + "/";

            Instance.PhaverPathWindows = "D:\\Dropbox\\Research\\tools\\phaver\\";
            Instance.ReachPathLinux = Instance.PhaverPathLinux + "reach/";
            Instance.ReachPathWindows = Instance.PhaverPathWindows + "reach\\";

            if (Controller.LOG_Z3)
            {
                Microsoft.Z3.Log.Open(Instance.OutPath + "z3_" + System.DateTime.Now.ToString("s").Replace(":", "-") + ".log"); // TODO: DO AS EARLY AS POSSIBLE
            }

            IOSTATE iostate = IOSTATE.SELECT_CASE_STUDY;
            bool batch = false;

            while (true)
            {
                if (terminate)
                {
                    break;
                }

                switch (iostate)
                {
                    case IOSTATE.SELECT_CASE_STUDY:
                        {
                            Console.WriteLine("Using directory path: " + Instance.InOutPath);
                            Console.WriteLine("Assuming input files in path: " + Instance.InputPath);

                            Console.WriteLine("Select an input file: \n\r");
                            foreach (var f in inputFiles)
                            {
                                Console.WriteLine("[" + f.Key.ToString() + "]" + " " + f.Value);
                            }
                            Console.WriteLine("[253] check all input files");
                            Console.WriteLine("[254] generate " + Instance.BatchSuffix + " PHAVer input files");
                            Console.WriteLine("[255] generate " + Instance.BatchSuffix +  "  table\n\r");
                            Console.WriteLine("[256] enter custom file\n\r");

                            choice = Console.ReadLine();

                            try
                            {
                                if (choice != null)
                                {
                                    int io_opt = int.Parse(choice);

                                    if (io_opt < inputFileCount)
                                    {
                                        Instance.InputFiles.Add(inputFiles[io_opt]);
                                    }
                                    else if (io_opt == 253)
                                    {
                                        Console.WriteLine("Batch processing, checking all files:");

                                        Instance.InputFiles = inputFiles.Values.ToList();

                                        batch = true;
                                    }
                                    else if (io_opt == 254 || io_opt == 255)
                                    {
                                        Console.WriteLine("Batch processing:");

                                        bool shorttest = false;

                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii.xml")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-harder.xml")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-harder-3loc.xml")).Value);

                                        if (!shorttest)
                                        {
                                            Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-harder-3loc-global-pointer.xml")).Value);
                                            Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-harder-basefinal.xml")).Value);
                                            Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-harder-sides.xml")).Value);
                                            Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-harder-sides-miss.xml")).Value);
                                            Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-harder-sides-miss-dynamics.xml")).Value);
                                            Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-harder-sides-miss-global.xml")).Value);
                                            //Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-harder-sides-miss-global-dynamics.xml")).Value);
                                            //Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-harder-sides-miss-global-pointer.xml")).Value);
                                            Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats-ii-pointer.xml")).Value);
                                        }

                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("mux-sem.xml")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("mux-sem-lastin.xml")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("mux-index.xml")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("mux-index-ta.xml")).Value);

                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("token-ring.xml")).Value);

                                        //Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("pointer-example.xml")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("gpointer-example.xml")).Value);

                                        //Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("prelim.xml")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("fischer.xml")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("fischer_aux.xml")).Value);

                                        batch = true;
                                    }
                                    else if (io_opt == 257) // forte / fmoods table
                                    {
                                        Console.WriteLine("Generating table for paper (correct vs. buggy versions):");

                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats_buggy")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats_timed")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("sats_timed_buggy")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("fischer_umeno_five_state")).Value);
                                        Instance.InputFiles.Add(inputFiles.First(a => a.Value.Contains("fischer_umeno_five_state_buggy")).Value);
                                        batch = true;
                                    }
                                    else if (io_opt == 256)
                                    {
                                        Console.WriteLine("Using path " + Instance.InputFiles);
                                        Instance.InputFiles.Add(Console.ReadLine()); //todo: dangerous
                                        Console.WriteLine("File: " + Instance.InputFile + "\n\r");
                                    }
                                    else
                                    {
                                        Console.WriteLine("Error, no file specified.\n\r");
                                        throw new Exception();
                                        // todo: handle error
                                    }
                                }
                            }
                            catch (Exception)
                            {
                                Instance.InputFiles.Add("fischer_umeno_five_state.xml");
                                Console.WriteLine("Error, picking default file: " + Instance.InputFiles.First() + ".\n\r");
                            }

                            Instance.InputFilePath = Instance.InputPath + Instance.InputFiles.First();

                            if (File.Exists(Instance.InputFilePath))
                            {
                                selected_file = true;
                            }
                            else
                            {
                                Console.WriteLine("Error: file " + Instance.InputFilePath + " does not exist, try again.");
                            }

                            if (selected_file)
                            {
                                iostate = IOSTATE.SELECT_N;
                                choice = null;
                                continue;
                            }
                            break;
                        }
                    case IOSTATE.SELECT_N:
                        {
                            Console.WriteLine("Specify a natural number value for N >= 1 (the number of automata)?  [default 0: enforces N >= 2 with no upper bound]");

                            choice = Console.ReadLine();

                            try
                            {
                                if (choice != null)
                                {
                                    choice = choice.Trim();
                                    if (choice.Contains("-"))
                                    {
                                        choice = choice.Replace(" ", "");
                                        String[] c = choice.Split(new char[] { '-', ',' });
                                        List<uint> cn = new List<uint>();

                                        foreach (var sub in c)
                                        {
                                            uint cv = uint.Parse(sub);
                                            if (cv >= 1)
                                            {
                                                cn.Add(cv);
                                            }
                                        }
                                        Console.WriteLine("Using range of N: ");

                                        if (cn.Count == 2)
                                        {
                                            Console.WriteLine(cn[0] + " to " + cn[1]);
                                            Instance.IndexNValue = cn[0];
                                            Instance.IndexNValueLower = cn[0];
                                            Instance.IndexNValueUpper = cn[1];
                                        }
                                    }
                                    else
                                    {
                                        uint io_n = uint.Parse(choice);

                                        if (io_n < 1)
                                        {
                                            Console.WriteLine("Using unbounded N");
                                        }
                                        else
                                        {
                                            Console.WriteLine("Using N = " + io_n);
                                            Instance.IndexNValue = io_n;
                                            Instance.IndexNValueLower = io_n;
                                            Instance.IndexNValueUpper = io_n;
                                        }
                                    }
                                    selected_n = true;
                                }
                            }
                            catch (Exception e)
                            {
                            }

                            if (selected_n)
                            {
                                iostate = IOSTATE.SELECT_OPERATION;
                                choice = null;
                                continue;
                            }
                            break;
                        }
                    case IOSTATE.SELECT_OPERATION:
                        {
                            Console.WriteLine("Select an operation to perform on the input file: ");

                            int i = 0; // todo: ensure i is initialized to lowest enum value and increments as enum does (normally 0, 1, 2, but might as well fix this at some point for general case)
                            foreach (PROGRAM_MODE p in Enum.GetValues(typeof(PROGRAM_MODE)))
                            {
                                Console.WriteLine("[" + i + "]" + p.ToString());
                                i++;
                            }

                            choice = Console.ReadLine();

                            try
                            {
                                if (choice != null)
                                {
                                    int io_op = int.Parse(choice);

                                    Instance.OPERATION = (PROGRAM_MODE)Enum.ToObject(typeof(PROGRAM_MODE), io_op); // cast int to enum
                                    selected_operation = true;
                                }
                            }
                            catch
                            {
                            }

                            if (selected_operation)
                            {
                                iostate = IOSTATE.EXECUTE_OPERATION;
                                terminate = true;
                            }
                            break;
                        }
                    default:
                        {
                            // error: should be unreachable
                            terminate = true;
                            break;
                        }
                }
            }


            String phaverBashScript = "#!/bin/bash\n\n" + 
                "ext=\".pha\"\n\n" +
                "# iterate over all benchmarks (supposing in subdirectories, e.g., bmname/thrust.pha)\n" +
                "for bm in " + Instance.PhaverInputPathLinux + "*$ext\n" +
                "do\n" +
	            "   for mode in 0\n" +
                "   do\n" +
                "       name=\"${bm:0:${#bm}-${#ext}}\" # strip extension\n" +
		        "       echo \"Running: $name with $mode\"\n" +
                "       cmd=\"" + Instance.MemtimePathLinux + " " + Instance.PhaverPathLinux + "$bm &> $bm.log\"\n" +
                "       echo \"$cmd\"\n" +
                "       #eval $cmd #run command\n" +
                "       echo \"\" #newline\n" +
                "   done\n" +
                "done\n";
            //System.IO.File.WriteAllText(@"C:\Users\tjohnson\Dropbox\Research\tools\phaver\" + Instance.BatchSuffix + "\phaver_bash", phaverBashScript);

            Instance.startMeasurement(); // initialize stopwatch

            // parse each input file (usually just one unless operating in batch mode)
            uint lb = Instance.IndexNValueLower;
            uint ub = Instance.IndexNValueUpper;
            if (!batch)
            {
                //lb = Controller.Instance.IndexNValue;
                //ub = Controller.Instance.IndexNValue;
            }

            
            foreach (String f in Instance.InputFiles)
            {
                Instance.InitializeZ3();

                Instance.InputFile = f;
                Instance.InputFilePath = Instance.InputPath + f;

                output.Debug.Write("Checking file: " + Instance.InputFilePath + "\n\r", output.Debug.MINIMAL);

                String AutomatonName = f.Split('.')[0];
                String LogFilename = Instance.OutPath + AutomatonName + "-output" + "-" + System.DateTime.Now.ToString("s").Replace(":", "-") + ".log";

                redirectConsole(LogFilename);

                output.Debug.Write("STATUS: Start time " + System.DateTime.Now.ToString("s"), output.Debug.MINIMAL);
                output.Debug.Write("STATUS: File: " + Instance.InputFilePath + "\n\r\n\r", output.Debug.MINIMAL);

                ParseHyXML.ParseFile(Instance.InputFilePath); // create Sys object

                string InputFileSysName = Instance.InputFile.Substring(0, Instance.InputFile.Length - Instance.InputFileExtension.Length);
                if (Instance.Sys.HybridAutomata.First().Name != InputFileSysName)
                {
                    output.Debug.Write("WARNING: input file name and automaton name do not match; filename is " + InputFileSysName + " and automaton name is " + Instance.sysname, output.Debug.MINIMAL);
                }

                string pat = "yyyy-MM-ddTHH-mm-ss";
                string now = DateTime.Now.ToString(pat);

                string fn = Instance.InputFile.Substring(0, Instance.InputFile.Length - 4); // strip .xml extension
                string fnall = "";
                String phaver_out_filename = "";

                switch (Instance.OPERATION)
                {
                    /*case PROGRAM_MODE.ENVIRONMENT_ABSTRACTION:
                        {
                            // counter / environment abstraction
                            //AbstractHybridAutomaton aha = new AbstractHybridAutomaton(sys, (AConcreteHybridAutomaton)sys.HybridAutomata.First());
                            //PrintPhaver.writeAbstractSystem(aha, "output.pha", PrintPhaver.OutputMode.phaver);
                            break;
                        }*/

                    // inductive invariant checking for small model theorem
                    case PROGRAM_MODE.INDUCTIVE_INVARIANT:
                        {
                            Instance.Sys.checkInductiveInvariants();
                            break;
                        }
                    case PROGRAM_MODE.DRAW_SYSTEM:
                        {
                            // start display thread
                            Thread t = new Thread(new ThreadStart(ThreadDisplay));
                            t.Start();

                            t.Join(1000); // wait for thread creation

                            Instance.View.drawSystem(Instance.Sys);

                            break;
                        }
                    case PROGRAM_MODE.OUTPUT_PHAVER:
                        {
                            for (uint nval = lb; nval <= ub; nval++)
                            {
                                Instance.IndexNValue = nval;
                                Console.WriteLine("Performing operations assuming N = " + Instance.IndexNValue);
                                String expName = AutomatonName + "_N=" + Instance.IndexNValue;
                                Controller.Instance.sysname = expName;

                                if (batch)
                                {
                                    fnall = fn + "_" + "N=" + Instance.IndexNValue + ".pha";
                                    phaver_out_filename = Instance.OutPath + "\\phaver\\" + Instance.BatchSuffix + "\\" + fnall; // todo: generalize
                                }
                                else
                                {
                                    fnall = fn + "_" + "N=" + Instance.IndexNValue + "_" + now + ".pha";
                                    phaver_out_filename = Instance.OutPath + "\\phaver\\" + fnall; // todo: generalize
                                }


                                Instance.appendMeasurement("starting", expName);

                                Controller.OutputPhaver(fnall, phaver_out_filename, expName, batch, "", 0);
                            }
                            break;
                        }
                    case PROGRAM_MODE.INPUT_PHAVER:
                        {
                            Console.WriteLine("Performing operations assuming N = " + Instance.IndexNValue);
                            String expName = AutomatonName + "_N=" + Instance.IndexNValue;
                            Controller.Instance.sysname = expName;
                            Instance.appendMeasurement("starting", expName);

                            Controller.InputReach(Instance.IndexNValue, expName, true, null, false, null);
                            Controller.projectAllProperties(Instance.IndexNValue);

                            //Instance.Sys.removeDuplicateProperties(); // remove duplicate properties (may get more during projection)
                            Instance.appendMeasurement("invariance_start", expName);
                            Instance.Sys.checkInductiveInvariants();
                            Instance.appendMeasurement("invariance_end", expName);
                            break;
                        }
                    case PROGRAM_MODE.INVISIBLE_INVARIANTS:
                        {
                            for (uint nval = lb; nval <= ub; nval++)
                            {
                                Instance.IndexNValue = nval;
                                Console.WriteLine("Performing invisible invariants assuming N = " + Instance.IndexNValue);
                                String expName = AutomatonName + "_N=" + Instance.IndexNValue;
                                Controller.Instance.sysname = expName;
                                Instance.appendMeasurement("starting", expName);

                                if (batch)
                                {
                                    fnall = fn + "_" + "N=" + Instance.IndexNValue + ".pha";
                                    phaver_out_filename = Instance.OutPath + "\\phaver\\" + Instance.BatchSuffix + "\\" + fnall; // todo: generalize
                                }
                                else
                                {
                                    fnall = fn + "_" + "N=" + Instance.IndexNValue + "_" + now + ".pha";
                                    phaver_out_filename = Instance.OutPath + "\\phaver\\" + fnall; // todo: generalize
                                }

                                Controller.OutputPhaver(fnall, phaver_out_filename, expName, batch, "", 0);
                                Controller.CallPhaver(fnall, expName);

                                Controller.InputReach(nval, expName, true, null, false, null);
                                Controller.projectAllProperties(Instance.IndexNValue);
                            }
                            String expNameL = AutomatonName + "_N=" + Instance.IndexNValue;

                            //Instance.Sys.removeDuplicateProperties(); // remove duplicate properties (may get more during projection)
                            Instance.appendMeasurement("invariance_start", expNameL);
                            Instance.Sys.checkInductiveInvariants();
                            Instance.appendMeasurement("invariance_end", expNameL);
                            break;
                        }
                    case PROGRAM_MODE.SPLIT_INVARIANTS:
                        {
                            List<String> newInitial = new List<string>();
                            List<String> newInitialNext = new List<string>();
                            uint iteration = 0;

                            Expr lastReach = Instance.Z3.MkFalse();
                            bool fp = false;
                            BoolExpr[] prevSplit = { Instance.Z3.MkFalse(), Instance.Z3.MkFalse() };

                            while (!fp) // breakout if fixedpoint
                            {
                                newInitial = new List<string>();
                                if (iteration == 0)
                                {
                                    newInitial.Add("");
                                }
                                else
                                {
                                    newInitial = newInitialNext;
                                    newInitialNext = new List<string>();
                                }


                                //List<String> reachsets = new List<string>();
                                for (uint nval = lb; nval <= ub; nval++)
                                {
                                    Instance.IndexNValue = nval;
                                    Console.WriteLine("Performing operations assuming N = " + Instance.IndexNValue);
                                    String expName = AutomatonName + "_N=" + Instance.IndexNValue;
                                    Controller.Instance.sysname = expName;
                                    Instance.appendMeasurement("starting", expName);
                                    //Controller.OutputPhaver(fnall, phaver_out_filename, expName, batch);
                                    //Controller.CallPhaver(fnall, expName);
                                    //Expr reachset = Instance.Sys.boundedModelCheck(Instance.IndexNValue, 0, Instance.Z3.MkFalse()); // compute reach set (BMC to fixed-point with empty set as illegal states => full reach set)
                                    //reachsets.Add(reachset.ToString());

                                    if (batch)
                                    {
                                        fnall = fn + "_" + "N=" + Instance.IndexNValue + ".pha";
                                        phaver_out_filename = Instance.OutPath + "\\phaver\\" + Instance.BatchSuffix + "\\" + fnall; // todo: generalize
                                    }
                                    else
                                    {
                                        fnall = fn + "_" + "N=" + Instance.IndexNValue + "_" + now + ".pha";
                                        phaver_out_filename = Instance.OutPath + "\\phaver\\" + fnall; // todo: generalize
                                    }

                                    foreach (var nis in newInitial)
                                    {
                                        output.Debug.Write("STATUS: split invariant iteration " + iteration);
                                        output.Debug.Write("STATUS: split invariant initial states: " + nis);

                                        Controller.OutputPhaver(fnall, phaver_out_filename, expName, batch, nis, iteration);
                                        Controller.CallPhaver(fnall, expName);

                                        List<Expr> pgcreachset = Controller.InputReach(nval, expName, true, null, true, prevSplit);

                                        Console.WriteLine("PREVIOUS SPLIT: ");
                                        Console.WriteLine(Instance.Z3.ExprArrayToString(prevSplit.ToArray()));

                                        // get the properties we're about to project (need their indices)
                                        //List<Property> projecting = Instance.Sys.Properties.FindAll(prop => prop.Status == StatusTypes.toProject);
                                        List<Property> projecting = Instance.Sys.Properties.FindAll(prop => prop.Unquantified != null);

                                        bool allfp = true;

                                        Controller.projectAllProperties(Instance.IndexNValue);
                                        if (projecting.Count >= 2)
                                        {
                                            BoolExpr fixedpoint = Instance.Z3.MkImplies((BoolExpr)projecting[0].Unquantified, (BoolExpr)prevSplit[0]);
                                            Model m;
                                            Expr[] core;
                                            String stat;
                                            if (!Instance.Z3.proveTerm(fixedpoint, out m, out core, out stat)) // not a fp
                                            {
                                                allfp &= false;
                                            }

                                            fixedpoint = Instance.Z3.MkImplies((BoolExpr)projecting[1].Unquantified, (BoolExpr)prevSplit[1]);
                                            if (!Instance.Z3.proveTerm(fixedpoint, out m, out core, out stat)) // not a fp
                                            {
                                                allfp &= false;
                                            }


                                            prevSplit[0] = (BoolExpr)projecting[0].Unquantified;
                                            projecting[0].Unquantified = null;
                                            prevSplit[1] = (BoolExpr)projecting[1].Unquantified;
                                            projecting[1].Unquantified = null;



                                        }
                                        //prevSplit[0] = (BoolExpr)Instance.Sys.Properties[first].Unquantified;
                                        //prevSplit[1] = (BoolExpr)Instance.Sys.Properties[first + 1].Unquantified;

                                        
                                        foreach (var v in pgcreachset)
                                        {/*
                                            BoolExpr fixedpoint = Instance.Z3.MkImplies((BoolExpr)v, (BoolExpr)lastReach);
                                            Model m;
                                            Expr[] core;
                                            String stat;
                                            if (!Instance.Z3.proveTerm(fixedpoint, out m, out core, out stat)) // not a fp
                                            {
                                                allfp &= false;
                                            }*/
                                            lastReach = v;



                                            newInitialNext.Add(pgreachToInitial(v, Instance.IndexNValue));
                                        }

                                        if (allfp)
                                        {
                                            output.Debug.Write("STATUS: split invariant fixedpoint reached.", output.Debug.MINIMAL);
                                            fp = true;
                                        }
                                        else
                                        {
                                            Instance.Sys.Properties.RemoveAll(prop => prop.SourceType != SourceTypes.user);
                                        }

                                        iteration++;
                                    }
                                }
                            }
                            String expNameL = AutomatonName + "_N=" + Instance.IndexNValue;
                            //Controller.InputReach(expNameL, false, reachsets); // for use with custom bmc


                            // todo: fixed point check with pgreachset

                            //Instance.Sys.removeDuplicateProperties(); // remove duplicate properties (may get more during projection)
                            Instance.appendMeasurement("invariance_start", expNameL);
                            Instance.Sys.checkInductiveInvariants();
                            Instance.appendMeasurement("invariance_end", expNameL);
                            break;
                        }
                    case PROGRAM_MODE.BMC:
                        {
                            //Instance.Sys.boundedModelCheckAllProperties();

                            for (uint nval = lb; nval <= ub; nval++)
                            {
                                Instance.IndexNValue = nval;
                                Console.WriteLine("Performing operations assuming N = " + Instance.IndexNValue);
                                String expName = AutomatonName + "_N=" + Instance.IndexNValue;
                                Controller.Instance.sysname = expName;
                                Instance.appendMeasurement("starting", expName);
                                //Controller.OutputPhaver(fnall, phaver_out_filename, expName, batch);
                                //Controller.CallPhaver(fnall, expName);
                                Expr reachset = Instance.Sys.boundedModelCheck(Instance.IndexNValue, 0, Instance.Z3.MkFalse()); // compute reach set (BMC to fixed-point with empty set as illegal states => full reach set)
                            }
                            //String expNameL = AutomatonName + "_N=" + Instance.IndexNValue;
                            //Controller.InputPhaver(expNameL);

                            break;
                        }
                    default:
                        {
                            //TODO: throw error should be unreachable
                            break;
                        }
                }
                output.Debug.Write("STATUS: stop time " + System.DateTime.Now.ToString("s"), output.Debug.MINIMAL);
                Instance.DeinitializeZ3();
            }

            String header = "benchmark,";
            header += "phaver time (s),phaver memory (MB),";
            //String header = "";
            String meas = "";
            String prev = "";
            bool headerDone = false;

            string itemStart = "starting";
            string itemEnd = "invariance_end";


            if (batch && (Instance.OPERATION == PROGRAM_MODE.INDUCTIVE_INVARIANT || Instance.OPERATION == PROGRAM_MODE.INPUT_PHAVER))
            {
                foreach (var v in Instance.TimeMeasurements)
                {
                    if (v.expname == itemStart)
                    {
                        meas += v.name + ",";

                        String logname = "C:\\Users\\tjohnson\\Dropbox\\Research\\tools\\passel\\repos\\trunk\\output\\phaver\\" + Instance.BatchSuffix + "\\" + v.name + ".pha.log"; // TODO: use path constants
                        if (File.Exists(logname))
                        {
                            String[] lns = Tail(File.OpenText(@logname), 10);

                            int idx = 0;
                            foreach (String ln in lns)
                            {
                                if (ln.Contains("elapsed"))
                                {
                                    break;
                                }
                                idx++;
                            }

                            String[] words = lns[idx].Split(',', '-');

                            foreach (var s in words)
                            {
                                String tmp = s.Trim();
                                if (tmp.EndsWith("elapsed"))
                                {
                                    meas += tmp.Split(' ')[0] + ",";
                                }
                                if (tmp.StartsWith("Max VSize", StringComparison.CurrentCultureIgnoreCase))
                                {
                                    String ss = tmp.Split('=')[1].Trim();
                                    ss = ss.Substring(0, ss.Length - "KB".Length);
                                    meas += (double.Parse(ss) / 1024.0) + ","; // KB -> MB
                                }
                            }
                            //0.39 user, 0.30 system, 0.71 elapsed -- Max VSize = 6212KB, Max RSS = 3164KB
                        }
                        else
                        {
                            meas += "nodata,nodata,";
                        }
                    }

                    if (!headerDone)
                    {
                        header += v.expname + ",";
                    }

                    if (v.value == null)
                    {
                        meas += v.runtime.TotalSeconds + ",";
                    }
                    else
                    {
                        meas += v.value + ",";
                    }

                    if (v.expname == itemEnd)
                    {
                        if (!(Instance.TimeMeasurements.IndexOf(v) == Instance.TimeMeasurements.Count - 1))
                        {
                            meas += "\n";
                        }
                        if (!headerDone)
                        {
                            header += "\n";
                        }
                        headerDone = true;
                    }

                    prev = v.name;
                }
                meas = header + meas;
                System.IO.File.WriteAllText(@"C:\Users\tjohnson\Dropbox\Research\tools\passel\repos\trunk\output\phaver\" + Instance.BatchSuffix + "\runtime.csv", meas);
            }
        }

        /**
         * Use phaver input file for invisible invariants
         */
        public static List<Expr> InputReach(uint N, String expName, bool phaver, List<String> reachsets, bool doSplit, BoolExpr[] prevSplit)
        {
            List<Expr> result = new List<Expr>();
            //Instance.Z3.MkFalse();
            Instance.appendMeasurement("init_done->starting_parsing", expName);
            //Instance.Sys.Properties = new List<Property>(); // clear all properties (todo: can add them back...)

            uint projectNMax = 2; // maximum number to project onto: will project onto 1, ..., projectNMax; usually choose 2

            PHAVER_INPUT_MODE input_mode = PHAVER_INPUT_MODE.reachable_forward;

            Controller.Instance.IndexNValue = N; // set global variable value
            //List<Expr> reachset = ParseHyXML.ParseReach("C:\\Users\\tjohnson\\Dropbox\\Research\\tools\\phaver\\ii_reach_N" + N); // parse reach set
            // TODO: generalize for > 1 automata
            List<String> reachset = null;
            /*try
            {
                if (N == 1)
                {
                    reachset = ParseHyXML.ParseReach("C:\\Users\\tjohnson\\Dropbox\\Research\\tools\\phaver\\" + Instance.Sys.HybridAutomata[0].Name + "_ii_reach_N" + N, false); // parse reach set
                }
                else if (N == 2)
                {
                    reachset = ParseHyXML.ParseReach("C:\\Users\\tjohnson\\Dropbox\\Research\\tools\\phaver\\" + Instance.Sys.HybridAutomata[0].Name + "_ii_reach_N" + N + "projected11", false); // parse reach set
                }
                else if (N >= 3)
                {
                    reachset = ParseHyXML.ParseReach("C:\\Users\\tjohnson\\Dropbox\\Research\\tools\\phaver\\" + Instance.Sys.HybridAutomata[0].Name + "_ii_reach_N" + N + "projected12", false); // parse reach set
                }
            }
            catch
            {*/
            if (phaver)
            {
                String reachname = Instance.ReachPathWindows + Instance.Sys.HybridAutomata[0].Name + "_N=" + N + ".reach";
                System.Console.WriteLine("Opening phaver output (reach set) file: " + reachname);
                reachset = ParseHyXML.ParseReach(reachname, false); // parse reach set
            }
            else
            {
                //reachset = new List<String>();
                //reachset.Add(reach.ToString()); // smt formatted
                reachset = reachsets;
            }

            //}

            uint Nmax = N;
            if (input_mode == PHAVER_INPUT_MODE.reachable_backward)
            {
                Nmax++; // compute with 2
            }

            for (uint projectN = 1; projectN <= projectNMax && projectN < Nmax; projectN++)  // assume 1 <= projectN < 10 (otherwise have to change regex below)
            {
                List<BoolExpr> prall = new List<BoolExpr>();
                foreach (var p in reachset)
                {
                    Property pr;
                    if (phaver)
                    {
                        pr = new Property(p, Property.PropertyType.safety, null, null);
                        pr.SourceType = SourceTypes.invisible_invariants;
                    }
                    else
                    {
                        pr = Property.PropertyFromSmt(p);
                    }

                    if (pr.Formula.IsImplies)
                    {
                        Expr tmp_all = Instance.Z3.MkAnd((BoolExpr)pr.Formula.Args[0], (BoolExpr)pr.Formula.Args[1]);
                        tmp_all = tmp_all.Simplify();

                        tmp_all = Instance.simplifyFormula(tmp_all);

                        //pr.Formula = tmp_all;
                        //pr.makePost();

                        //tmp_all = Instance.Z3.MkAnd((BoolExpr)tmp_all, Instance.Z3.MkAnd(Instance.Z3.AssumptionsUniversal.ToArray()));
                        prall.Add((BoolExpr)tmp_all); // add before modifying formula
                    }

                    //pr.Formula = pr.Formula.Simplify(); // simplify here vastly speeds removing redundancies later; note, do it after the previous isimplies

                    //pr.Formula = Instance.Z3.MkAnd((BoolExpr)pr.Formula, Instance.Z3.MkAnd(Instance.Z3.AssumptionsUniversal.ToArray())); // add data-type assumptions

                    List<Expr> bi = new List<Expr>();
                    foreach (var v in Instance.UndefinedVariables)
                    {
                        Regex projecting = new Regex("[" + (projectN + 1).ToString() + "-9]+[1-9]*"); // projectN followed by any number, have to change if we have projectN >= 10
                        if (projecting.IsMatch(v.Key) && Instance.Z3.findTerm(pr.Formula, Instance.UndefinedVariables[v.Key], true))
                        {
                            bi.Add(v.Value);
                        }
                    }

                    // do projection
                    if (bi.Count > 0 && projectN < N && input_mode == PHAVER_INPUT_MODE.reachable_forward)
                    {
                        pr.Formula = Instance.Z3.MkExists(bi.ToArray(), pr.Formula);
                        pr.Status = StatusTypes.toProject;
                        pr.ProjectedFrom = N;
                        pr.Project = projectN;
                    }
                    // just assert this version as a potential invariant
                    else
                    {
                        Expr tmpf = pr.Formula;
                        Instance.Z3.generalizeAllVariables(ref tmpf, N);
                        pr.Formula = tmpf;
                        pr.Status = StatusTypes.toProcess;

                        //Expr idxi = Instance.Indices["i"];
                        Expr idxi = Instance.Z3.MkIntConst("i");
                        BoolExpr idxBounds = Instance.Z3.MkAnd(Instance.Z3.MkGe((ArithExpr)idxi, (ArithExpr)Instance.IndexOne), Instance.Z3.MkLe((ArithExpr)idxi, (ArithExpr)Instance.IndexN));
                        List<BoolExpr> prabstr = new List<BoolExpr>();
                        for (uint i = 1; i <= N; i++)
                        {
                            BoolExpr tmp_abs = (BoolExpr)Instance.Z3.copyExpr(pr.Formula); // make a deep copy
                            tmp_abs = (BoolExpr)Instance.Z3.abstractGlobals(tmp_abs, N, projectN, i, 0); // j unused
                            prabstr.Add(tmp_abs);
                        }
                        pr.Formula = Instance.Z3.MkAnd(prabstr.ToArray());

                        switch (input_mode)
                        {
                            case PHAVER_INPUT_MODE.reachable_forward:
                                {
                                    pr.Formula = Instance.Z3.MkForall(getNIndices(N), Instance.Z3.MkImplies(idxBounds, (BoolExpr)pr.Formula));
                                    break;
                                }
                            case PHAVER_INPUT_MODE.reachable_backward:
                                {
                                    pr.Formula = Instance.Z3.MkForall(getNIndices(N), Instance.Z3.MkImplies(idxBounds, Instance.Z3.MkNot((BoolExpr)pr.Formula)));
                                    break;
                                }
                        }
                        pr.makePost(); // update post-state formula
                    }
                    //Instance.Sys.Properties.Add(pr); // TODO: never seems to be satisfied: this won't be, it's the AND version that's the problem---the quantified invariant would need to be IMPLIES
                }
                result.Add(projectAndGeneralize(input_mode, prall, expName, projectN, N, doSplit, prevSplit));
            }
            return result;
        }


        private static void projectAllProperties(uint N)
        {
            //Instance.Z3 = new Z3Wrapper(Instance.Config); // would have to copy things over, might bring over corruption if that's the problem
            //Controller.Instance.Z3.Assumptions.Add(Controller.Instance.Z3.MkEq(Controller.Instance.IndexN, Controller.Instance.Z3.MkInt(1)));
            //Instance.Sys.removeDuplicateProperties(); // remove duplicate properties

            output.Debug.Write("Universal assumptions (data types, etc.):\n\r", output.Debug.VERBOSE_STEPS);
            output.Debug.Write(Instance.Z3.ExprArrayToString(Instance.Z3.AssumptionsUniversal.ToArray()) + "\n\r\n\r", output.Debug.VERBOSE_STEPS);

            // project all properties specified as such
            foreach (var p in Instance.Sys.Properties)
            {
                if (p.Status == StatusTypes.toProject)
                {
                    System.Console.WriteLine("Property before projection:\n\r");
                    System.Console.WriteLine(p.Formula.ToString() + "\n\r\n\r");
                    Goal g = Instance.Z3.MkGoal();
                    g.Assert(Instance.Z3.AssumptionsUniversal.ToArray()); // data-type assumptions (MUST USE THIS)

                    /*
                    for (uint it = 1; it <= N; it++)
                    {
                        List<BoolExpr> locConstraint = new List<BoolExpr>();
                        foreach (var loc in Instance.Sys.HybridAutomata[0].Locations)
                        {
                            locConstraint.Add(Instance.Z3.MkEq(Instance.UndefinedVariables["q" + it.ToString()], loc.ValueTerm));
                        }
                        g.Assert(Instance.Z3.MkOr(locConstraint.ToArray()));
                    }*/

                    g.Assert((BoolExpr)p.Formula);

                    Params sparams = Instance.Z3.MkParams();
                    sparams.Add("elim_and", true);
                    sparams.Add("cache-all", true);
                    sparams.Add("hoist-cmul", true);
                    sparams.Add("hoist-mul", true);
                    sparams.Add("ite-extra-rules", true);
                    sparams.Add("local-ctx", true);
                    sparams.Add("pull-cheap-ite", true);


                    //Instance.Z3.MkTactic("propagate-ineqs"),  Instance.Z3.MkTactic("propagate-values"), Instance.Z3.MkTactic("elim-uncnstr"), Instance.Z3.MkTactic("elim-term-ite")
                    //Tactic tac = Instance.Z3.Then(Instance.Z3.MkTactic("qe"), Instance.Z3.With(Instance.Z3.MkTactic("simplify"), sparams), Instance.Z3.MkTactic("ctx-simplify"), Instance.Z3.MkTactic("skip")); ; // quantifier elimination for projection
                    Tactic tac = Instance.Z3.MkTactic("qe");
                    ApplyResult a;
                    a = tac.Apply(g);
                    a = a;

                    foreach (var sg in a.Subgoals)
                    {
                        // formula provides no information, remove it
                        if (sg.Formulas.Contains(Instance.Z3.MkTrue()))
                        {
                            //p.Status = StatusTypes.toDelete;
                            //break;
                        }


                        Expr e;
                        if (sg.Formulas.Length > 1)
                        {
                            e = Instance.Z3.MkAnd(sg.Formulas);
                        }
                        else
                        {
                            e = sg.Formulas[0];
                        }

                        /*
                        if (e.IsOr)
                        {
                            HashSet<Expr> tmp_args = new HashSet<Expr>();
                            for (int arg = 0; arg < e.NumArgs; arg++)
                            {
                                if (!e.Args[arg].IsTrue)
                                {
                                    tmp_args.Add(e.Args[arg]); // Expr.update requires same number of args, so we can't just delete the trues
                                }
                            }
                            e.Update(tmp_args.ToArray());
                        }*/
                        uint oldnum = e.NumArgs;
                        oldnum = oldnum;
                        e.Update(e.Args.Distinct().ToArray()); // distinct terms
                        uint newnum = e.NumArgs;
                        newnum = newnum;

                        Instance.Z3.generalizeAllVariables(ref e, p.Project);
                        p.Formula = e;

                        List<Expr> bound = new List<Expr>();
                        List<BoolExpr> idxBounds = new List<BoolExpr>();
                        if (p.Project >= 1)
                        {
                            //Expr idxi = Instance.Indices["i"];
                            Expr idxi = Instance.Z3.MkIntConst("i");
                            idxBounds.Add(Instance.Z3.MkAnd(Instance.Z3.MkGe((ArithExpr)idxi, (ArithExpr)Instance.IndexOne), Instance.Z3.MkLe((ArithExpr)idxi, (ArithExpr)Instance.IndexN)));
                            bound.Add(idxi);
                        }
                        if (p.Project >= 2)
                        {
                            //Expr idxj = Instance.Indices["j"];
                            Expr idxj = Instance.Z3.MkIntConst("j");
                            idxBounds.Add(Instance.Z3.MkAnd(Instance.Z3.MkGe((ArithExpr)idxj, (ArithExpr)Instance.IndexOne), Instance.Z3.MkLe((ArithExpr)idxj, (ArithExpr)Instance.IndexN)));
                            bound.Add(idxj);
                        }

                        //p.Formula = Instance.Z3.abstractGlobals(p.Formula, p.Project);

                        List<BoolExpr> prabstr = new List<BoolExpr>();
                        //for (int i = 1; i <= p.ProjectedFrom; i++)
                        //{
                        //    int j = 0;
                        //do
                        //{
                        BoolExpr tmp_abs = (BoolExpr)Instance.Z3.copyExpr(p.Formula); // make a deep copy
                        tmp_abs = (BoolExpr)Instance.Z3.abstractGlobals(tmp_abs, p.ProjectedFrom, p.Project, 1, 0);
                        //prabstr.Add(tmp_abs);
                        //j++;
                        //}
                        //    while (bound.Count > 1 && j <= p.ProjectedFrom);
                        //}
                        //prabstr = prabstr.Distinct().ToList();
                        //p.Formula = Instance.Z3.MkAnd(prabstr.ToArray());

                        p.Formula = tmp_abs;
                        p.Unquantified = p.Formula;

                        if (bound.Count == 1)
                        {
                            p.Formula = Instance.Z3.MkForall(bound.ToArray(), Instance.Z3.MkImplies(Instance.Z3.MkAnd(idxBounds.ToArray()), (BoolExpr)p.Formula)); // todo: check if > 1 subgoal
                        }
                        else
                        {
                            idxBounds.Add(Instance.Z3.MkDistinct(bound.ToArray())); // this is what pnueli2001tacas does
                            //e = Instance.Z3.MkAnd(Instance.Z3.MkDistinct(bound.ToArray()), (BoolExpr)e);
                            p.Formula = Instance.Z3.MkForall(bound.ToArray(), Instance.Z3.MkImplies(Instance.Z3.MkAnd(idxBounds.ToArray()), (BoolExpr)p.Formula)); // todo: check if > 1 subgoal
                        }
                        p.Status = StatusTypes.toProcess;
                    }
                    p.Formula = p.Formula.Simplify();
                    p.makePost(); // update post-state formula

                    /*
                    Goal gr = Instance.Z3.MkGoal(true, false, false);
                    //gr.Assert(z3.slvr.Assertions);
                    gr.Assert((BoolExpr)p.Formula);
                    Tactic tr = Instance.Z3.Repeat(Instance.Z3.Then(Instance.Z3.MkTactic("symmetry-reduce"), Instance.Z3.MkTactic("distribute-forall")));
                    ApplyResult ar;
                    ar = tr.Apply(gr);
                    ar = ar;

                    if (ar.NumSubgoals == 1)
                    {
                        p.Formula = Instance.Z3.MkAnd(ar.Subgoals[0].Formulas);
                    }
                    else
                    {
                        throw new Exception("Error in reduction");
                    }
                        */

                    //:elim-and
                    //distribute-forall
                    output.Debug.Write("Property after projection and generalization:\n\r", output.Debug.VERBOSE_STEPS);
                    output.Debug.Write(p.Formula.ToString() + "\n\r\n\r", output.Debug.VERBOSE_STEPS);
                }
            }

            Instance.Sys.Properties.RemoveAll(p => p.Status == StatusTypes.toDelete); // remove all useless properties
        }


        /**
         * Project and generalize after parsing formulas
         * 
         * May either generate a formula or a new set of states for another iteration
         */
        private static Expr projectAndGeneralize(PHAVER_INPUT_MODE input_mode, List<BoolExpr> prall, string expName, uint projectN, uint N, bool doSplit, BoolExpr[] prevSplit)
        {
            Expr result = Instance.Z3.MkFalse();
            //Instance.Sys.removeDuplicateProperties();

            bool toDelete = false;

            // TODO: measure prall length by iterating over all elements and adding up # total arguments? actually, could probably do this with a tactic...
            List<BoolExpr> newallNoGlobal = new List<BoolExpr>();
            List<BoolExpr> newall = new List<BoolExpr>();
            switch (input_mode)
            {
                case PHAVER_INPUT_MODE.reachable_forward:
                    {
                        Instance.appendMeasurement("P=" + projectN + "done_parsing->projection", expName);
                        // PROJECTION
                        for (int i = 0; i < 2; i++)
                        {
                            foreach (var v in prall)
                            {
                                Expr vCopy = Controller.Instance.Z3.copyExpr(v); // deep copy
                                Goal g = Instance.Z3.MkGoal(true, false, false);
                                //g.Assert(Instance.Z3.AssumptionsUniversal.ToArray()); // data-type assumptions


                                List<Expr> bi = new List<Expr>();
                                foreach (var udf in Instance.UndefinedVariables)
                                {
                                    Regex projecting = new Regex("[" + (projectN + 1).ToString() + "-9]+[1-9]*"); // projectN followed by any number, have to change if we have projectN >= 10
                                    if (projecting.IsMatch(udf.Key) && Instance.Z3.findTerm(vCopy, Instance.UndefinedVariables[udf.Key], true))
                                    {
                                        bi.Add(udf.Value);
                                    }
                                }

                                if (i == 0)
                                {
                                    // add index variables to project away
                                    foreach (var gv in Controller.Instance.Sys.Variables)
                                    {
                                        if (gv.Type == Variable.VarType.index)
                                        {
                                            bi.Add(Controller.instance.GlobalVariables[gv.Name]);
                                        }
                                    }
                                }

                                Expr newv = null;
                                // do projection
                                if (bi.Count > 0 && projectN < N)
                                {
                                    newv = Instance.Z3.MkExists(bi.ToArray(), vCopy);
                                }

                                if (newv != null)
                                {
                                    g.Assert((BoolExpr)newv);

                                    Params sparams = Instance.Z3.MkParams();
                                    //sparams.Add("elim_and", true);
                                    sparams.Add("cache-all", true);
                                    sparams.Add("hoist-cmul", true);
                                    sparams.Add("hoist-mul", true);
                                    //sparams.Add("ite-extra-rules", true);
                                    sparams.Add("local-ctx", true);
                                    //sparams.Add("pull-cheap-ite", true);

                                    //Tactic tac = Instance.Z3.MkTactic("qe"); // quantifier elimination for projection
                                    Tactic tac = Instance.Z3.Then(Instance.Z3.MkTactic("qe"), Instance.Z3.With(Instance.Z3.MkTactic("simplify"), sparams), Instance.Z3.MkTactic("propagate-ineqs"), Instance.Z3.MkTactic("propagate-values"), Instance.Z3.MkTactic("ctx-simplify"), Instance.Z3.MkTactic("skip")); ; // quantifier elimination for projection
                                    ApplyResult a;
                                    a = tac.Apply(g);
                                    a = a;

                                    foreach (var sg in a.Subgoals)
                                    {
                                        if (sg.Formulas.Contains(Instance.Z3.MkTrue()))
                                        {
                                            toDelete = true;
                                            //p.Status = StatusTypes.toDelete;
                                            break;
                                        }

                                        Expr e;
                                        if (sg.Formulas.Length > 1)
                                        {
                                            e = Instance.Z3.MkAnd(sg.Formulas);
                                        }
                                        else
                                        {
                                            e = sg.Formulas[0];
                                        }

                                        //if (e.IsOr)
                                        //{
                                        //    HashSet<Expr> tmp_args = new HashSet<Expr>();
                                        //    for (int arg = 0; arg < e.NumArgs; arg++)
                                        //    {
                                        //        if (!e.Args[arg].IsTrue)
                                        //        {
                                        //            tmp_args.Add(e.Args[arg]); // Expr.update requires same number of args, so we can't just delete the trues
                                        //        }
                                        //    }
                                        //    e.Update(tmp_args.ToArray());
                                        //}
                                        //uint oldnum = e.NumArgs;
                                        //oldnum = oldnum;
                                        //e.Update(e.Args.Distinct().ToArray()); // distinct terms
                                        //uint newnum = e.NumArgs;
                                        //newnum = newnum;

                                        Expr cp = Instance.Z3.copyExpr(e); // try deep copy...
                                        Instance.Z3.generalizeAllVariables(ref cp, N); // todo: set projection number
                                        if (i == 0)
                                        {
                                            newallNoGlobal.Add((BoolExpr)cp);

                                        }
                                        else
                                        {
                                            newall.Add((BoolExpr)cp);
                                        }
                                    }
                                }
                            }
                        }

                        Property prandNoGlobal = new Property(Instance.Z3.MkOr(newallNoGlobal.ToArray()));
                        prandNoGlobal.SourceType = SourceTypes.invisible_invariants;
                        prandNoGlobal.Formula = Instance.simplifyFormula(prandNoGlobal.Formula);
                        prandNoGlobal.makePost();

                        Instance.appendMeasurement("done_projection->generalization", expName);

                        prandNoGlobal.Status = StatusTypes.toProcess;
                        prandNoGlobal.Type = Property.PropertyType.safety;
                        prandNoGlobal = Instance.GeneralizeProperty(prandNoGlobal, projectN, N, true);

                        Property prand = new Property(Instance.Z3.MkOr(newall.ToArray()));
                        prand.SourceType = SourceTypes.invisible_invariants;
                        prand.Formula = Instance.simplifyFormula(prand.Formula);
                        prand.makePost();

                        if (toDelete)
                        {
                            prand.Status = StatusTypes.toDelete;
                        }
                        else
                        {
                            prand.Status = StatusTypes.toProcess;
                        }
                        prand.Type = Property.PropertyType.safety;

                        Expr concretizedNew = Instance.Z3.MkTrue();
                        List<Expr> clist = new List<Expr>();


                        if (doSplit)
                        {
                            prand = Instance.GeneralizeProperty(prand, projectN, N, false); // generalized without quantifiers (instantiating next)
                            prand.Unquantified = prand.Formula;

                            for (uint i = 1; i <= N; i++)
                            {
                                Expr concretized = Instance.Z3.copyExpr(prand.Formula); // deep copy (doing substitution)
                                concretized = Instance.Z3.MkOr(prevSplit[projectN - 1], (BoolExpr)concretized); //
                                //concretized = Instance.Z3.ToCNF(concretized);

                                concretized = concretized.Simplify();

                                if (projectN >= 2)
                                {
                                    for (uint j = 1; j <= N; j++)
                                    {
                                        if (i == j)
                                            continue;
                                        concretized = (BoolExpr)concretized.Substitute(new Expr[] { Instance.Indices["i"], Instance.Indices["j"] }, new Expr[] { Instance.Z3.MkInt(i), Instance.Z3.MkInt(j) });

                                        /*
                                        Tactic tc = Instance.Z3.MkTactic("ctx-solver-simplify");
                                        Goal g = Instance.Z3.MkGoal();
                                        g.Assert(Instance.Z3.AssumptionsUniversal.ToArray());
                                        g.Assert((BoolExpr)concretized);
                                        ApplyResult ar = tc.Apply(g);
                                        concretized = Instance.Z3.MkAnd(ar.Subgoals[0].Formulas);
                                        */
                                        concretizedNew = Instance.Z3.MkAnd((BoolExpr)concretizedNew, (BoolExpr)concretized);
                                        //clist.Add(Instance.Z3.MkAnd((BoolExpr)concretizedNew, (BoolExpr)concretized.Substitute(new Expr[] { Instance.Indices["i"], Instance.Indices["j"] }, new Expr[] { Instance.Z3.MkInt(i), Instance.Z3.MkInt(j) })));
                                        concretizedNew = Instance.Z3.ToCNF(concretizedNew); // actually dnf
                                    }
                                }
                                else
                                {
                                    concretizedNew = Instance.Z3.MkAnd((BoolExpr)concretizedNew, (BoolExpr)concretized.Substitute(Instance.Indices["i"], Instance.Z3.MkInt(i)));
                                    //clist.Add(Instance.Z3.MkAnd((BoolExpr)concretizedNew, (BoolExpr)concretized.Substitute(Instance.Indices["i"], Instance.Z3.MkInt(i))));
                                    concretizedNew = Instance.Z3.ToCNF(concretizedNew); // actually dnf
                                }
                            }
                            //concretizedNew = Instance.Z3.ToCNF(concretizedNew); // actually dnf

                            result = concretizedNew;
                            
                            //Expr dnf_concretizedNew = Instance.Z3.ToDNF(concretizedNew);
                        }

                        //prand.Formula = Instance.Z3.ToCNF(prand.Formula);
                        prand = Instance.GeneralizeProperty(prand, projectN, N, true); // add quantifiers

                        /*
                        // was hoping the following would eliminate the universal quantifier by expanding it out, but this didn't work (even though it's bounded 1-3)
                        Params ps = Instance.Z3.MkParams();
                        ps.Add("mbqi", true);
                        Tactic simplifier = Instance.Z3.Repeat(Instance.Z3.With(Instance.Z3.MkTactic("ctx-solver-simplify"), ps));
                        Tactic ts = Instance.Z3.Then(Instance.Z3.MkTactic("simplify"), Instance.Z3.MkTactic("qe"), Instance.Z3.Repeat(Instance.Z3.MkTactic("ctx-simplify")), simplifier);
                        Goal goal = Instance.Z3.MkGoal();
                        //goal.Assert(Instance.Z3.AssumptionsUniversal.ToArray());
                        goal.Assert((BoolExpr)prand.Formula.Substitute(Instance.IndexN, Instance.Z3.MkInt(N)));
                        ApplyResult ar = simplifier.Apply(goal);
                        Goal[] sgs = ar.Subgoals;
                        ar = ar;*/
                         


                        Instance.Sys.Properties.Add(prand);
                        Instance.Sys.Properties.Add(prandNoGlobal); // disable no-global generated invariants for now

                        Instance.appendMeasurement("done_generalization->invariance", expName);

                        break;
                    }
                case PHAVER_INPUT_MODE.reachable_backward:
                    {
                        Property prand = new Property(Instance.Z3.MkOr(prall.ToArray()));
                        prand.Status = StatusTypes.toProcess;
                        prand.Type = Property.PropertyType.safety;
                        prand.Formula = Instance.Z3.MkNot((BoolExpr)prand.Formula); // backward reachable states
                        prand.makePost();

                        prand = Instance.GeneralizeProperty(prand, projectN, N, true);

                        Instance.Sys.Properties.Add(prand);
                        break;
                    }
            }
            return result;
        }

        /**
         * print the projected, generalized, and conretized reach set to a phaver initial condition string
         */
        public static String pgreachToInitial(Expr concretizedNew, uint N)
        {
            List<string> newic = new List<string>();
            String allnewic = "";
            foreach (var scd in concretizedNew.Args)
            //foreach (var scd in clist)
            {
                SortedDictionary<uint, string> idxToLoc = new SortedDictionary<uint, string>();
                List<String> terms = new List<string>();
                foreach (var scc in scd.Args)
                {
                    //String stmp = scc.ToString(); // minimal clause
                    String sout = "";
                    sout = Instance.Z3.ToStringFormatted(scc, Z3Wrapper.PrintFormatMode.phaver);

                    if (sout.Contains("q"))
                    {
                        for (uint i = 1; i <= N; i++)
                        {
                            sout = sout.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                            if (sout.Contains("q_" + i.ToString()))
                            {
                                sout = sout.Replace("q_" + i.ToString(), "");
                                sout = sout.Replace("==", ""); // todo: check generality
                                idxToLoc.Add(i, sout.Trim());
                            }
                        }
                    }
                    else
                    {
                        bool breakout = false;
                        foreach (var l in Instance.Sys.HybridAutomata[0].Locations)
                        {
                            breakout |= sout.Contains(l.Label); // drop idle = b001, etc.
                        }
                        if (breakout)
                        {
                            continue;
                        }

                        for (uint i = 1; i <= N; i++)
                        {
                            sout = sout.Replace("[" + i.ToString() + "]", "_" + i.ToString());
                        }

                        terms.Add(sout);
                    }
                }

                // global automaton initial location
                if (Instance.Sys.Variables.Count > 0)
                {
                    allnewic += "default~";
                }

                allnewic += idxToLoc.Values.Aggregate((agg, next) => agg + "~" + next);

                // variable initial values
                if (terms.Count > 0)
                {
                    allnewic += " & " + terms.Aggregate((agg, next) => agg + " & " + next);
                }
                allnewic += ",";
            }
            output.Debug.Write(allnewic, output.Debug.MINIMAL);

            allnewic = allnewic.Substring(0, allnewic.Length - 1);

            return allnewic;
        }

        /**
         * Generate PHAVer input files
         */
        public static void OutputPhaver(string fnall, string phaver_out_filename, string expName, bool batch, string newInitial, uint iteration)
        {
            if (Instance.IndexNValue > 0)
            {
                String out_phaver = Instance.Sys.HybridAutomata[0].outputPhaverN(Instance.IndexNValue, Instance.PhaverPathLinux, newInitial, iteration); // todo: generalize if more than 1 automaton
                StreamWriter writer = new StreamWriter(phaver_out_filename);
                writer.Write(out_phaver);
                writer.Close();

                System.Console.WriteLine("FINISHED: Generating phaver input file from Passel description for N = " + Instance.IndexNValue + ": " + phaver_out_filename);
            }
            else
            {
                Console.WriteLine("ERROR: generating PHAVER output requires selecting a finite value for N.");
            }
        }

        /**
         * Call PHAVer in virtual machine (via VIX)
         */
        public static void CallPhaver(string fnall, string expName)
        {
            // from: http://tranxcoder.wordpress.com/2008/05/14/using-the-vixcom-library/
            string hostName = "localhost";
            string hostUser = "";
            string hostPassword = "";
            string virtualMachineUsername = "tjohnson";
            string virtualMachinePassword = "asdf!234";
            Instance.VMPath = "D:\\Virtual Machines\\Ubuntu\\Ubuntu.vmx";
            string exePath = Instance.PhaverPathLinux + "phaver";
            string phaver_out_filepath_vmware = "/mnt/hgfs/Dropbox/Research/tools/passel/repos/trunk/output/phaver/"; // TODO: generalize

            string exeParameters = phaver_out_filepath_vmware + fnall + " > " + Instance.PhaverPathLinux + fnall + "_VIX_LOG.txt";
            bool returnValue = false;
            // vmware vix is 32-bit, but I can't set project to 32-bit, because then Z3 won't work (get an exception when using the 32-bit library in 32-bit compilation mode...)
            try
            {
                VixWrapper vix = new VixWrapper();

                //
                // Connect to the VMWare Server
                //
                if (vix.Connect(hostName, hostUser, hostPassword))
                {
                    //
                    // Opening the VMX File
                    //
                    if (vix.Open(Instance.VMPath))
                    {
                        //
                        // Reverting to the ‘only’ snapshot
                        //
                        //if (vix.RevertToLastSnapshot())
                        //{
                        //
                        // Powering on the Virtual Machine
                        //
                        if (vix.PowerOn())
                        {
                            //
                            // Logging in to the Virtual Machine
                            //
                            if (vix.LogIn(virtualMachineUsername, virtualMachinePassword))
                            {
                                //
                                // Run the test program
                                //
                                int resultCode = 0;

                                System.Console.WriteLine("Calling phaver via VIX: " + exePath + exeParameters);

                                if (vix.RunProgram(exePath, exeParameters, out resultCode))
                                {
                                    if (resultCode == 0)
                                    {
                                        //
                                        // The test PASSED!
                                        //
                                        returnValue = true;
                                    }
                                    else
                                    {
                                        // The test FAILED!
                                        returnValue = false;
                                    }
                                }
                                else
                                {
                                    //
                                    // Unable to run test
                                    //
                                }
                            }
                            else
                            {
                                // Unable to login to the virtual machine
                            }

                            //vix.PowerOff();
                        }
                        else
                        {
                            // Unable to power on the virtual machine
                        }
                        //}
                        //else
                        //{
                        // Unable to revert to the last snapshot
                        //}
                    }
                    else
                    {
                        // Unable to open the VMX file
                    }
                }
                else
                {
                    // Unable to connect to the host
                }

                //return returnValue;
            }
            catch (COMException comExc)
            {
                //
                // COM Exception
                //
            }
        }

        ///<summary>Returns the end of a text reader.</summary>
        ///<param name="reader">The reader to read from.</param>
        ///<param name="lineCount">The number of lines to return.</param>
        ///<returns>The last lneCount lines from the reader.</returns>
        ///http://stackoverflow.com/questions/4619735/how-to-read-last-n-lines-of-log-file
        public static string[] Tail(TextReader reader, int lineCount)
        {
            var buffer = new List<string>(lineCount);
            string line;
            for (int i = 0; i < lineCount; i++)
            {
                line = reader.ReadLine();
                if (line == null) return buffer.ToArray();
                buffer.Add(line);
            }

            int lastLine = lineCount - 1;           //The index of the last line read from the buffer.  Everything > this index was read earlier than everything <= this indes

            while (null != (line = reader.ReadLine()))
            {
                lastLine++;
                if (lastLine == lineCount) lastLine = 0;
                buffer[lastLine] = line;
            }

            if (lastLine == lineCount - 1) return buffer.ToArray();
            var retVal = new string[lineCount];
            buffer.CopyTo(lastLine + 1, retVal, 0, lineCount - lastLine - 1);
            buffer.CopyTo(0, retVal, lineCount - lastLine - 1, lastLine + 1);
            return retVal;
        }

        public Expr simplifyFormula(Expr f)
        {
            //Tactic otac = Instance.Z3.Repeat(Instance.Z3.Then(Instance.Z3.MkTactic("propagate-values"), Instance.Z3.MkTactic("propagate-ineqs"), Instance.Z3.MkTactic("max-bv-sharing"), Instance.Z3.MkTactic("ctx-simplify"), Instance.Z3.MkTactic("ctx-solver-simplify")));
            Tactic otac = Instance.Z3.Repeat(Instance.Z3.Then(Instance.Z3.MkTactic("propagate-values"), Instance.Z3.MkTactic("propagate-ineqs"), Instance.Z3.MkTactic("max-bv-sharing"), Instance.Z3.MkTactic("ctx-simplify")));
            Goal og = Instance.Z3.MkGoal(true, false, false);
            og.Assert((BoolExpr)f);
            ApplyResult oa;
            oa = otac.Apply(og);
            List<BoolExpr> otmpList = new List<BoolExpr>();

            foreach (var sg in oa.Subgoals)
            {
                Expr e;
                if (sg.Formulas.Length > 1)
                {
                    e = Instance.Z3.MkAnd(sg.Formulas);
                }
                else
                {
                    e = sg.Formulas[0];
                }

                Expr cp = Instance.Z3.copyExpr(e); // try deep copy...
                otmpList.Add((BoolExpr)cp.Simplify());
            }
            if (otmpList.Count > 1)
            {
                return Instance.Z3.MkAnd(otmpList.ToArray());
            }
            return otmpList[0];
        }

        /**
         * Generalize a property
         */
        public Property GeneralizeProperty(Property p, uint projectN, uint N, bool quant)
        {
            List<Expr> bound = new List<Expr>();
            foreach (var v in Instance.UndefinedVariables)
            {
                Regex projecting = new Regex("[" + (projectN + 1).ToString() + "-9]+[1-9]*"); // projectN followed by any number, have to change if we have projectN >= 10
                if (projecting.IsMatch(v.Key) && Instance.Z3.findTerm(p.Formula, Instance.UndefinedVariables[v.Key], true))
                {
                    bound.Add(v.Value);
                }
            }

            if (bound.Count > 0 && projectN < N)
            {
                p.Formula = Instance.Z3.MkExists(bound.ToArray(), p.Formula);
                p.Status = StatusTypes.toProject;
                p.ProjectedFrom = N;
                p.Project = projectN;
            }
            else
            {
                Expr tmpf = p.Formula;
                Instance.Z3.generalizeAllVariables(ref tmpf, N);
                p.Formula = tmpf;
                p.Status = StatusTypes.toProcess;

                // IMPORTANT: THIS MUST HAPPEN ***BEFORE*** WE ADD QUANTIFIERS, OTHERWISE WE GET UNEXPECTED BEHAVIOR, POTENTIAL MEMORY CORRUPTION (i.e., doing term replacement over quantified variables has some bug)
                BoolExpr tmpand = (BoolExpr)Instance.Z3.copyExpr(p.Formula); // make a deep copy
                tmpand = (BoolExpr)Instance.Z3.abstractGlobals(tmpand, N, projectN, 1, 0);
                p.Formula = tmpand;
                /*
                 //TODO: 2013-01-10: maybe change back
                foreach (var s in Instance.Sys.HybridAutomata[0].Locations)
                {
                    p.Formula = p.Formula.Substitute(s.BitVectorExpr, s.LabelExpr);
                }*/


                List<Expr> boundIds = new List<Expr>();
                List<BoolExpr> idxBounds = new List<BoolExpr>();
                if (projectN >= 1)
                {
                    //Expr idxi = Instance.Indices["i"];
                    Expr idxi = Instance.Z3.MkIntConst("i");
                    idxBounds.Add(Instance.Z3.MkAnd(Instance.Z3.MkGe((ArithExpr)idxi, (ArithExpr)Instance.IndexOne), Instance.Z3.MkLe((ArithExpr)idxi, (ArithExpr)Instance.IndexN)));
                    boundIds.Add(idxi);
                }
                if (projectN >= 2)
                {
                    //Expr idxi = Instance.Indices["j"];
                    Expr idxi = Instance.Z3.MkIntConst("j");
                    idxBounds.Add(Instance.Z3.MkAnd(Instance.Z3.MkGe((ArithExpr)idxi, (ArithExpr)Instance.IndexOne), Instance.Z3.MkLe((ArithExpr)idxi, (ArithExpr)Instance.IndexN)));
                    boundIds.Add(idxi);
                }

                //p.Formula = Instance.Z3.abstractGlobals(p.Formula, projectN);
                /*List<BoolExpr> prabstr = new List<BoolExpr>();
                for (int i = 1; i <= N; i++)
                {
                    BoolExpr tmp_abs = (BoolExpr)Instance.Z3.copyExpr(p.Formula); // make a deep copy
                    tmp_abs = (BoolExpr)Instance.Z3.abstractGlobals(tmp_abs, N, projectN, i, -1); // j unused
                    prabstr.Add(tmp_abs);
                }*/
                //p.Formula = Instance.Z3.MkAnd(prabstr.ToArray());
                if (boundIds.Count > 1)
                {
                    idxBounds.Add(Instance.Z3.MkDistinct(boundIds.ToArray())); // i != j
                }

                if (quant)
                {
                    //p.Formula = Instance.Z3.MkForall(boundIds.ToArray(), Instance.Z3.MkImplies(Instance.Z3.MkAnd(idxBounds.ToArray()), Instance.Z3.MkImplies(Instance.Z3.MkDistinct(boundIds.ToArray()), (BoolExpr)p.Formula)));
                    p.Formula = Instance.Z3.MkForall(boundIds.ToArray(), Instance.Z3.MkImplies(Instance.Z3.MkAnd(idxBounds.ToArray()), (BoolExpr)p.Formula));
                    //p.Formula = Instance.Z3.MkForall(boundIds.ToArray(), Instance.Z3.MkImplies(Instance.Z3.MkAnd(idxBounds.ToArray()), Instance.Z3.MkOr((BoolExpr)p.Formula, Instance.Z3.MkEq(Instance.Indices["i"], Instance.Indices["j"]))));
                }
                p.makePost(); // update post-state formula
            }
            return p;
        }

        /**
         * Free memory used by Z3 context when done / enable creating a new one
         */
        public void DeinitializeZ3()
        {
            unredirectConsole();
            if (Controller.LOG_Z3)
            {
                Microsoft.Z3.Log.Close();
            }
            Instance.Z3.Dispose();
        }

        /**
         * Remove double spaces, newlines from a string
         */
        public static String Strip(String s)
        {
            return s.Replace("\n", "").Replace("\r", "").Replace("  ", "");
        }

        public static void redirectConsole(String outFilename)
        {
            //Console.Clear();
            lock (Controller.Instance)
            {
                // redirect console output to file
                StreamWriter fileOutput;
                oldOutput = Console.Out;
                fileOutput = new StreamWriter(
                    new FileStream(outFilename, FileMode.Create)
                );
                fileOutput.AutoFlush = true;

                Console.SetOut(fileOutput); // do the redirect
            }
        }

        public static TextWriter oldOutput = Console.Out;

        public static void unredirectConsole()
        {
            //Console.Clear();
            lock (Controller.Instance)
            {
                // redirect console output to file
                TextWriter fileOutput = oldOutput;
                oldOutput = Console.Out;
                //fileOutput = new StreamWriter(
                //    new FileStream(outFilename, FileMode.Create)
                //);
                //fileOutput.AutoFlush = true;

                Console.SetOut(fileOutput); // do the redirect
            }
            Instance.SW = Stopwatch.StartNew();
        }

        public Stopwatch SW;

        public List<Measurement> TimeMeasurements;

        public void startMeasurement()
        {
            Instance.TimeMeasurements = new List<Measurement>();
            Instance.SW = Stopwatch.StartNew();
            Instance.SW.Start();
        }

        public class Measurement
        {
            public String name;
            public String expname;
            public TimeSpan runtime;
            public String value;

            public Measurement(String n, String e, TimeSpan t)
            {
                this.name = n;
                this.expname = e;
                this.runtime = t;
            }

            public Measurement(String n, String e, String v)
            {
                this.name = n;
                this.expname = e;
                //this.runtime = t;
                this.value = v;
            }
        }

        public void appendMeasurement(String expname, String name) {
            TimeMeasurements.Add(new Measurement(name, expname, SW.Elapsed));
            Instance.SW.Restart();
        }

        public String sysname;

        public void appendLogEvent(String expname, String name, String value)
        {
            TimeMeasurements.Add(new Measurement(name, expname, value));
            //Instance.SW.Restart(); // don't restart
        }

    }
}
