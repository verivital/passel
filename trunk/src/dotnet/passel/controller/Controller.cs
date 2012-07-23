using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using System.Diagnostics;
using System.Threading;

using System.IO;

using Microsoft.Z3;

//using VixCOM;

using passel.model;
using passel.controller.output;
using passel.controller.smt;
using passel.controller.smt.z3;
using passel.controller.parsing;

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
        private IDictionary<String, Expr> _q;

        /**
         * Special variable for control states / locations (modes)
         * - All other variables go into the _vars dictionary
         */
        private IDictionary<String, Expr> _qPrimed;
        
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
        public int IndexNValue;

        public Expr RealInf;

        /**
         * I/O directory path
         */
        private String _inoutPath;

        /**
         * filename
         */
        private String _inputFile;

        private List<String> _inputFiles;

        /**
         * filen path
         */
        private String _inputFilePath;

        /**
         * theory used to model variables of each agent in the system
         */
        public enum DataOptionType { array, uninterpreted_function };

        /**
         * set used to model indices of processes
         */
        public enum IndexOptionType { integer, natural, naturalOneToN, enumeration };

        public Dictionary<UInt32, String> LocationNumToName;

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
        public const String DOT_SUFFIX = "_dot";


        /**
         * Singleton constructor
         */
        private Controller()
        {
            this.InitializeZ3();
        }

        /**
         * Instantiate data structures, create Z3 object, populate data structures with pointers to Z3 objects, etc.
         */
        private void InitializeZ3()
        {
            this._q = new Dictionary<String, Expr>();
            this._qPrimed = new Dictionary<String, Expr>();
            this._ivars = new Dictionary<KeyValuePair<String, String>, Expr>();
            this._ivarsPrimed = new Dictionary<KeyValuePair<String, String>, Expr>();
            this._params = new Dictionary<String, Expr>();
            this._globalVariables = new Dictionary<String, Expr>();
            this._globalVariablesPrimed = new Dictionary<String, Expr>();
            this._locations = new Dictionary<String, Expr>();
            this._indices = new Dictionary<String, Expr>();
            this.LocationNumToName = new Dictionary<UInt32, String>();
            this.LocationNumTermToName = new Dictionary<Expr, String>();
            this._inputFiles = new List<string>();
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
            //this.Config.Add("MBQI_MAX_ITERATIONS", "50000");


            this.Config.Add("ELIM_QUANTIFIERS", "true"); // if we fix N to be small, we can rely on MBQI, but if we have N large or unbounded, we may need Q.E.
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
            this.Config.Add("MODEL_COMPLETION", "true");
            this.Config.Add("DISPLAY_UNSAT_CORE", "true");

            this.Config.Add("Z3_SOLVER_LL_PP", "true");
            //this.Config.Add("Z3_SOLVER_SMT_PP", "true");

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

            Microsoft.Z3.Log.Open(this._inoutPath + "z3.log");

            //this.Z3.OpenLog("asserted.log"); // todo: deprecated

            this.IntType = Z3.MkIntSort();
            this.RealType = Z3.MkRealSort();
            //this.LocType = Z3.MkUninterpretedSort("loc");
            this.LocType = Z3.MkIntSort();

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
         * Index type: natural number between 1 and N
         */
        public Sort IndexType;

        /**
         * Real sort
         */
        public Sort RealType;

        /**
         * Indexed control locations / modes
         */
        public IDictionary<String, Expr> Q
        {
            get { return this._q; }
            set { this._q = value; }
        }

        /**
         * Primed (for resets) Indexed control locations / modes
         */
        public IDictionary<String, Expr> QPrimed
        {
            get { return this._qPrimed; }
            set { this._qPrimed = value; }
        }

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

        public IDictionary<String, Expr> ExistentialConstants;

        enum IOSTATE { SELECT_CASE_STUDY, SELECT_N, SELECT_OPERATION, EXECUTE_OPERATION };

        enum PROGRAM_MODE { INDUCTIVE_INVARIANT, OUTPUT_PHAVER, INPUT_PHAVER, BMC };
        private PROGRAM_MODE OPERATION;

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

            inputFiles.Add(inputFileCount++, "fischer.xml");
            inputFiles.Add(inputFileCount++, "fischer_buggy.xml");

            inputFiles.Add(inputFileCount++, "lynch_shavit.xml");

            inputFiles.Add(inputFileCount++, "sats_full.xml");
            inputFiles.Add(inputFileCount++, "sats.xml");
            inputFiles.Add(inputFileCount++, "sats_buggy.xml");
            inputFiles.Add(inputFileCount++, "sats_timed.xml");
            inputFiles.Add(inputFileCount++, "sats_timed_buggy.xml");
            inputFiles.Add(inputFileCount++, "sats_timed_counter.xml");

            inputFiles.Add(inputFileCount++, "bakery.xml");
            inputFiles.Add(inputFileCount++, "bakery_lamport.xml");
            inputFiles.Add(inputFileCount++, "bakery_lamport_buggy.xml");

            inputFiles.Add(inputFileCount++, "nfa.xml");
            inputFiles.Add(inputFileCount++, "nfa_buggy.xml");
            inputFiles.Add(inputFileCount++, "ta.xml");
            inputFiles.Add(inputFileCount++, "ta_buggy.xml");
            inputFiles.Add(inputFileCount++, "ra.xml");
            inputFiles.Add(inputFileCount++, "gv.xml");
            inputFiles.Add(inputFileCount++, "gv_buggy.xml");
            inputFiles.Add(inputFileCount++, "flocking.xml");
            inputFiles.Add(inputFileCount++, "flocking_buggy.xml");
            inputFiles.Add(inputFileCount++, "bully.xml");
            inputFiles.Add(inputFileCount++, "bully_buggy.xml");

            inputFiles.Add(inputFileCount++, "gcd.xml");

            inputFiles.Add(inputFileCount++, "starl.xml");

            if (System.Environment.MachineName.ToLower().StartsWith("johnso99"))
            {
                Instance._inoutPath = "C:\\Documents and Settings\\tjohnson\\My Documents\\My Dropbox\\Research\\tools\\passel\\repos\\trunk\\input\\";
            }
            else if (System.Environment.MachineName.ToLower().StartsWith("lh-lapto"))
            {
                Instance._inoutPath = "C:\\Users\\tjohnson\\Dropbox\\Research\\tools\\passel\\repos\\trunk\\input\\";
            }
            else
            {
                Instance._inoutPath = Directory.GetCurrentDirectory();
                //this._inoutPath = "D:\\Dropbox\\Research\\tools\\passel\\repos\\trunk\\input\\";
            }
            //Instance._inoutPath = Directory.GetCurrentDirectory() + "\\input\\"; // uncomment for release version

            IOSTATE iostate = IOSTATE.SELECT_CASE_STUDY;

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
                            Console.WriteLine("Using directory path: " + Instance._inoutPath);

                            Console.WriteLine("Select an input file: \n\r");
                            foreach (var f in inputFiles)
                            {
                                Console.WriteLine("[" + f.Key.ToString() + "]" + " " + f.Value);
                            }
                            Console.WriteLine("[255] generate FORTE/FMOODS table\n\r");
                            Console.WriteLine("[256] enter custom file\n\r");

                            choice = Console.ReadLine();

                            try
                            {
                                if (choice != null)
                                {
                                    int io_opt = int.Parse(choice);

                                    if (io_opt < inputFileCount)
                                    {
                                        Instance._inputFiles.Add(inputFiles[io_opt]);
                                    }
                                    else if (io_opt == 255)
                                    {
                                        Console.WriteLine("Generating table for paper (correct vs. buggy versions):");

                                        Instance._inputFiles.Add(inputFiles.First(a => a.Value.Contains("sats")).Value);
                                        Instance._inputFiles.Add(inputFiles.First(a => a.Value.Contains("sats_buggy")).Value);
                                        Instance._inputFiles.Add(inputFiles.First(a => a.Value.Contains("sats_timed")).Value);
                                        Instance._inputFiles.Add(inputFiles.First(a => a.Value.Contains("sats_timed_buggy")).Value);
                                        Instance._inputFiles.Add(inputFiles.First(a => a.Value.Contains("fischer_umeno_five_state")).Value);
                                        Instance._inputFiles.Add(inputFiles.First(a => a.Value.Contains("fischer_umeno_five_state_buggy")).Value);
                                    }
                                    else if (io_opt == 256)
                                    {
                                        Console.WriteLine("Using path " + Instance._inoutPath);
                                        Instance._inputFiles.Add(Console.ReadLine()); //todo: dangerous
                                        Console.WriteLine("File: " + Instance._inputFile + "\n\r");
                                    }
                                    else
                                    {
                                        // todo: handle error
                                    }
                                }
                            }
                            catch (Exception)
                            {
                                Instance._inputFiles.Add("fischer_umeno_five_state.xml");
                                Console.WriteLine("Error, picking default file: " + Instance._inputFiles.First() + ".\n\r");
                            }

                            Instance._inputFilePath = Instance._inoutPath + instance._inputFiles.First();

                            if (File.Exists(Instance._inputFilePath))
                            {
                                selected_file = true;
                            }
                            else
                            {
                                Console.WriteLine("Error: file " + Instance._inputFilePath + " does not exist, try again.");
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
                            Console.WriteLine("Specify a natural number value for N >= 2 (the number of automata)?  [default 0: enforces N >= 2 with no upper bound]");

                            choice = Console.ReadLine();

                            try
                            {
                                if (choice != null)
                                {
                                    int io_n = int.Parse(choice);

                                    if (io_n < 2)
                                    {
                                        Console.WriteLine("Using unbounded N");
                                    }
                                    else
                                    {
                                        Console.WriteLine("Using N = " + io_n);
                                        Instance.IndexNValue = io_n;
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

            // parse each input file (usually just one)
            foreach (String f in Instance._inputFiles)
            {
                Instance.InitializeZ3();

                Instance._inputFile = f;
                Instance._inputFilePath = Instance._inoutPath + f;

                Console.Write("Checking file: {0}\n\r", Instance._inputFilePath);

                String outFilename = Instance._inoutPath + "..\\output\\output" + "-" + Instance._inputFile.Split('.')[0] + "-" + System.DateTime.Now.ToString("s").Replace(":", "-") + ".log";

                //Console.Clear();
                lock (Console.Out)
                {
                    // redirect console output to file
                    StreamWriter fileOutput;
                    TextWriter oldOutput = Console.Out;
                    fileOutput = new StreamWriter(
                        new FileStream(outFilename, FileMode.Create)
                    );
                    fileOutput.AutoFlush = true;

                    Console.SetOut(fileOutput); // do the redirect
                }

                Console.Write("File: {0}\n\r\n\r", Instance._inputFilePath);

                ISmtSymbols smtSymbols = new SymbolsZ3();

                // constants
                Expr int_zero = Instance.Z3.MkInt(0);
                Expr int_one = Instance.Z3.MkInt(1);
                Expr int_two = Instance.Z3.MkInt(2);
                Expr real_one = Instance.Z3.MkReal(1);

                // process index variables
                Instance._indices = new Dictionary<String, Expr>();

                Instance._indices.Add("h", Instance.Z3.MkIntConst("h"));
                Instance._indices.Add("i", Instance.Z3.MkIntConst("i"));
                Instance._indices.Add("j", Instance.Z3.MkIntConst("j"));
                Instance._indices.Add("k", Instance.Z3.MkIntConst("k"));
                Instance._indices.Add("l", Instance.Z3.MkIntConst("l"));
                Instance._indices.Add("m", Instance.Z3.MkIntConst("m"));
                Instance._indices.Add("n", Instance.Z3.MkIntConst("n"));

                /*
                Instance._indices.Add("h", Instance.Z3.MkConst("h", Instance.IndexType));
                Instance._indices.Add("i", Instance.Z3.MkConst("i", Instance.IndexType));
                Instance._indices.Add("j", Instance.Z3.MkConst("j", Instance.IndexType));
                Instance._indices.Add("k", Instance.Z3.MkConst("k", Instance.IndexType));
                Instance._indices.Add("l", Instance.Z3.MkConst("l", Instance.IndexType));
                Instance._indices.Add("m", Instance.Z3.MkConst("m", Instance.IndexType));
                Instance._indices.Add("n", Instance.Z3.MkConst("n", Instance.IndexType));
                 */

                Instance.ExistentialConstants = new Dictionary<String, Expr>();

                switch (Instance.DataOption)
                {
                    case DataOptionType.array:
                        {
                            Sort locSort = Instance.Z3.MkArraySort(Instance.IndexType, Instance.IntType);
                            ArrayExpr q = (ArrayExpr)Instance.Z3.MkConst("q", locSort); // control location; todo: should map to finite control state (just hack to use integers for now)
                            Instance.DataA.IndexedVariableDecl.Add("q", q);
                            ArrayExpr qPrime = (ArrayExpr)Instance.Z3.MkConst("q" + Controller.PRIME_SUFFIX, locSort); ; // control location; todo: should map to finite control state (just hack to use integers for now)
                            Instance.DataA.IndexedVariableDeclPrimed.Add("q", qPrime);

                            // apply each index to the control location function
                            foreach (var pair in Instance.Indices)
                            {
                                Instance.Q.Add(pair.Key, Instance.Z3.MkSelect(q, pair.Value));
                                Instance.QPrimed.Add(pair.Key, Instance.Z3.MkSelect(qPrime, pair.Value));
                            }
                            break;
                        }
                    case DataOptionType.uninterpreted_function:
                    default:
                        {
                            FuncDecl q = Instance.Z3.MkFuncDecl("q", Instance.IndexType, Instance.LocType); // control location; todo: should map to finite control state (just hack to use integers for now)
                            Instance.DataU.IndexedVariableDecl.Add("q", q);
                            FuncDecl qPrime = Instance.Z3.MkFuncDecl("q" + Controller.PRIME_SUFFIX, Instance.IndexType, Instance.LocType); // control location; todo: should map to finite control state (just hack to use integers for now)
                            Instance.DataU.IndexedVariableDeclPrimed.Add("q", qPrime);

                            // apply each index to the control location function
                            foreach (var pair in Instance.Indices)
                            {
                                Instance.Q.Add(pair.Key, Instance.Z3.MkApp(q, pair.Value));
                                Instance.QPrimed.Add(pair.Key, Instance.Z3.MkApp(qPrime, pair.Value));
                            }
                            break;
                        }
                }

                Instance.Sys = ParseHyXML.ParseFile(Instance._inputFilePath);


                if (Instance._inputFile.Contains("sats"))
                {
                    // want to use a macro, e.g.: http://stackoverflow.com/questions/9313616/quantifier-in-z3
                    /**
                     * When you use (assert (forall ((i Int)) (> i 10))), i is a bounded variable and the quantified formula is equivalent to a truth value, which is false in this case.
                        I think you want to define a macro using quantifiers:

                        (declare-fun greaterThan10 (Int) Bool)
                        (assert (forall ((i Int)) (= (greaterThan10 i) (> i 10))))
                        And you can use them to avoid code repetition:

                        (declare-const x (Int))
                        (declare-const y (Int))
                        (assert (greaterThan10 x))
                        (assert (greaterThan10 y))
                        (check-sat)
                     * It is essentially the way to define macros using uninterpreted functions when you're working with Z3 API.
                     * Note that you have to set (set-option :macro-finder true) in order that Z3 replaces universal quantifiers with bodies of those functions.

                        However, if you're working with the textual interface, the macro define-fun in SMT-LIB v2 is an easier way to do what you want:

                        (define-fun greaterThan10 ((i Int)) Bool
                          (> i 10))
                     */



                    //Sort[] indexByIndex = { Instance.IndexType, Instance.IndexType };
                    /** TODO: TRY NEXT
                    
                    FuncDecl pathFunc = Instance.Z3.MkFuncDecl("path", Instance.IndexType, Instance.IndexType, Instance.Z3.MkBoolSort());
                    Term pathTerm = Instance.Z3.MkApp(pathFunc, Instance.Indices["i"], Instance.Indices["j"]);
                    Instance.Params.Add("path", pathTerm);
                    Term iEqj = Instance.Z3.MkEq(Instance.Indices["i"], Instance.Indices["j"]);
                    Term iNeqj = Instance.Z3.MkNot(iEqj);
                    Instance.Z3.AssertCnstr(Instance.Z3.MkIff(Instance.Z3.MkEq(pathTerm, Instance.Z3.MkTrue()), iEqj)); // base case

                    Term pathTermik = Instance.Z3.MkApp(pathFunc, Instance.Indices["i"], Instance.Indices["k"]);
                    Term nextEq = Instance.Z3.MkEq(Instance.IndexedVariables[new KeyValuePair<string, string>("next", "k")], Instance.Indices["j"]);
                    Term existsPart = Instance.Z3.MkExists(0, new Term[] { Instance.Indices["k"] }, null, pathTermik & nextEq);
                    Instance.Z3.AssertCnstr(Instance.Z3.MkIff(Instance.Z3.MkEq(pathTerm, Instance.Z3.MkTrue()), iNeqj & existsPart)); // inductive case
                    */
                    //Term pt = Instance.Z3.MkForall(0, new Term[] { Instance.Indices["i"], Instance.Indices["j"] }, null, );
                    //Property p = new Property();
                    //Instance.Sys.Properties.Add(p);
                }


                // add constraints on index variables (they are between 1 and N)
                //foreach (var pair in Instance._indices)
                //{
                    // 1 <= i <= N, 1 <= j <= N, etc.
                    //                Instance.Z3.AssertCnstr(Instance.Z3.MkGe(pair.Value, int_one));
                    //                Instance.Z3.AssertCnstr(Instance.Z3.MkLe(pair.Value, Instance.Params["N"])); // todo: error handling, what if we don't have this parameter in the specification file?
                //}

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
                    case PROGRAM_MODE.OUTPUT_PHAVER:
                        {
                            if (Instance.IndexNValue != null)
                            {
                                String out_phaver = Instance.Sys.outputPhaverN(Instance.IndexNValue);
                                string pat = "yyyy-MM-ddTHH-mm-ss";
                                string now = DateTime.Now.ToString(pat);
                                string fn = Instance._inputFile.Substring(0, Instance._inputFile.Length - 4); // strip .xml extension

                                StreamWriter writer = new StreamWriter(Instance._inoutPath + "..\\output\\phaver\\" + fn + "_" + "N=" + Instance.IndexNValue + "_" + now + ".pha");
                                writer.Write(out_phaver);
                                writer.Close();
                                // TODO: add call to PHAVER, then parse reach set as per next command
                                //ParseHyXML.ParseReach("C:\\Users\\tjohnson\\Dropbox\\Research\\tools\\phaver\\ii_reach"); // parse reach set

                                //VixCOM.VixLib a = new VixLib();
                                //a.
                            }
                            else
                            {
                                Console.WriteLine("ERROR: generating PHAVER output requires selecting a finite value for N.");
                            }

                            break;
                        }
                    case PROGRAM_MODE.INPUT_PHAVER:
                        {
                            List<Expr> reachset = ParseHyXML.ParseReach("C:\\Users\\tjohnson\\Dropbox\\Research\\tools\\phaver\\ii_reach_N" + Controller.instance.IndexNValue); // parse reach set



                            break;
                        }
                    case PROGRAM_MODE.BMC:
                        {
                            Instance.Sys.boundedModelCheckAllProperties();
                            break;
                        }
                    default:
                        {
                            //TODO: throw error should be unreachable
                            break;
                        }
                }
                Instance.DeinitializeZ3();
            }
        }

        /**
         * Free memory used by Z3 context when done / enable creating a new one
         */
        public void DeinitializeZ3()
        {
            Microsoft.Z3.Log.Close();
            Instance.Z3.Dispose();
        }

        /**
         * Remove double spaces, newlines from a string
         */
        public static String Strip(String s)
        {
            return s.Replace("\n", "").Replace("\r", "").Replace("  ", "");
        }
    }
}
