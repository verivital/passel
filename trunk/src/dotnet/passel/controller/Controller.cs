using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using System.Diagnostics;
using System.Threading;

using System.IO;

using Microsoft.Z3;

using phyea.model;
using phyea.controller.output;
using phyea.controller.smt;
using phyea.controller.smt.z3;
using phyea.controller.parsing;

namespace phyea.controller
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
        private IDictionary<String, Term> _q;

        /**
         * Special variable for control states / locations (modes)
         * - All other variables go into the _vars dictionary
         */
        private IDictionary<String, Term> _qPrimed;
        
        /**
         * Indexed variables: input, e.g., (x i) returns the function corresponding to variable x at process i
         * 
         */
        private IDictionary<KeyValuePair<String, String>, Term> _ivars;

        /**
         * Primed indexed variables: input, e.g., (x' i) returns the function corresponding to variable x at process i
         * 
         */
        private IDictionary<KeyValuePair<String, String>, Term> _ivarsPrimed;

        /**
         * Parameter variables (N, S, etc.)
         */
        private IDictionary<String, Term> _params;

        /**
         * Global variables
         */
        private IDictionary<String, Term> _globalVariables;

        /**
         * Primed global variables
         */
        private IDictionary<String, Term> _globalVariablesPrimed;

        /**
         * Location labels to value map
         */
        private IDictionary<String, Term> _locations;

        /**
         * Process indices (i, j, k, etc.)
         */
        private IDictionary<String, Term> _indices;

        /**
         * integer for control state
         */
        private UInt32 _qv = 0;

        /**
         * Integer sort
         */
        private Sort _intType;

        /**
         * Index type: natural number between 1 and N
         */
        private Sort _indexType;

        private Term _indexSet;

        /**
         * Real number sort
         */
        private Sort _realType;

        /**
         * Integer value of zero
         */
        private Term _intZero;

        /**
         * Integer value of one
         */
        public Term IntOne;

        public Term IndexNone;
        public Term IndexOne;
        public Term IndexN;

        public Term RealInf;

        /**
         * Real value of zero
         */
        private Term _realZero;

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

        public Dictionary<Term, String> LocationNumTermToName;

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
            this._q = new Dictionary<String, Term>();
            this._qPrimed = new Dictionary<String, Term>();
            this._ivars = new Dictionary<KeyValuePair<String, String>, Term>();
            this._ivarsPrimed = new Dictionary<KeyValuePair<String, String>, Term>();
            this._params = new Dictionary<String, Term>();
            this._globalVariables = new Dictionary<String, Term>();
            this._globalVariablesPrimed = new Dictionary<String, Term>();
            this._locations = new Dictionary<String, Term>();
            this._indices = new Dictionary<String, Term>();
            this.LocationNumToName = new Dictionary<UInt32, String>();
            this.LocationNumTermToName = new Dictionary<Term, String>();
             _inputFiles = new List<string>();

            Config c = new Config();

            c.SetParamValue("AUTO_CONFIG", "false"); // disable auto-configuration (use all logics)

            /*c.SetParamValue("ARRAY_CANONIZE", "true");
            c.SetParamValue("ARRAY_CG", "true");
            c.SetParamValue("ARRAY_LAZY_IEQ", "true");
            c.SetParamValue("ARRAY_WEAK", "true");
             */
            //c.SetParamValue("ARRAY_SOLVER", "1"); // 0 to 3

            //c.SetParamValue("QI_PROFILE", "true");
            //c.SetParamValue("QI_PROFILE_FREQ", "1000");
            //c.SetParamValue("MBQI_TRACE", "true");

            c.SetParamValue("MODEL", "true");
            c.SetParamValue("MBQI", "true"); //  (see http://research.microsoft.com/en-us/um/redmond/projects/z3/mbqi-tutorial/)
            //c.SetParamValue("MBQI_MAX_ITERATIONS", "50000");


            c.SetParamValue("ELIM_QUANTIFIERS", "true"); // if we fix N to be small, we can rely on MBQI, but if we have N large or unbounded, we may need Q.E.
            c.SetParamValue("ELIM_NLARITH_QUANTIFIERS", "true");
            c.SetParamValue("ELIM_BOUNDS", "true");
            c.SetParamValue("QI_LAZY_INSTANTIATION", "true");

            c.SetParamValue("PULL_CHEAP_ITE_TREES", "true");
            c.SetParamValue("EMATCHING", "true");
            c.SetParamValue("MACRO_FINDER", "true");
            c.SetParamValue("STRONG_CONTEXT_SIMPLIFIER", "true");
            c.SetParamValue("CONTEXT_SIMPLIFIER", "true");

            c.SetParamValue("PI_PULL_QUANTIFIERS", "true");     // check with on / off 
            c.SetParamValue("PULL_NESTED_QUANTIFIERS", "true"); // check with on / off (see mbqi tutorial)
            c.SetParamValue("MODEL_PARTIAL", "true");
            c.SetParamValue("MODEL_V2", "true");
            c.SetParamValue("VERBOSE", "10");

            c.SetParamValue("DISPLAY_ERROR_FOR_VISUAL_STUDIO", "true");
            c.SetParamValue("DISTRIBUTE_FORALL", "true");

            c.SetParamValue("MODEL_COMPACT", "true"); // slower, but more accurate (as in the models are more useful) it seems
            c.SetParamValue("MODEL_ON_FINAL_CHECK", "true");
            c.SetParamValue("MODEL_COMPLETION", "true");
            c.SetParamValue("DISPLAY_UNSAT_CORE", "true");






            // bad syntax for next...
            //c.SetParamValue("produce-proofs", "true");
            //c.SetParamValue("produce-models", "true");
            //c.SetParamValue("produce-unsat-cores", "true");
            //c.SetParamValue("produce-assignments", "true");
            //c.SetParamValue("expand-definitions", "true");

            //c.SetParamValue("CNF_FACTOR", "10");
            //c.SetParamValue("CNF_MODE", "3");

            //todo: SOFT_TIMEOUT // can use this option to force queries to return unknown instead of running forever

            //c.SetParamValue("SPC", "true");

            //c.SetParamValue("STATISTICS", "true"); // crashes

            c.SetParamValue("ARITH_SOLVER", "2"); // simplex solver
            c.SetParamValue("NL_ARITH", "true"); // nonlinear arithmetic support: requires arith_solver 2
            c.SetParamValue("NL_ARITH_GB_EQS", "true");
            c.SetParamValue("ARITH_ADAPTIVE", "true");
            c.SetParamValue("ARITH_PROCESS_ALL_EQS", "true");
            //c.SetParamValue("ARITH_EUCLIDEAN_SOLVER", "true");
            //c.SetParamValue("ARITH_FORCE_SIMPLEX", "true");
            //c.SetParamValue("ARITH_MAX_LEMMA_SIZE", "512"); // default 128

            //c.SetParamValue("CHECK_PROOF", "true");
            //c.SetParamValue("DL_COMPILE_WITH_WIDENING", "true");
            //c.SetParamValue("DACK", "2");
            //c.SetParamValue("DACK_EQ", "true");

            // some bugs in the next ones
            //c.SetParamValue("FWD_SR_CHEAP", "true");
            //c.SetParamValue("LOOKAHEAD", "true");
            //c.SetParamValue("MBQI_MAX_CEXS", "true"); // crashes
            //c.SetParamValue("MODEL_VALIDATE", "true"); // corrupts memory?
            // end buggy ones


            //c.SetParamValue("LOOKAHEAD_DISEQ", "true");

            //c.SetParamValue("LIFT_ITE", "2"); // buggy: get memory corruption sometimes
            //c.SetParamValue("ELIM_TERM_ITE", "true"); // buggy: get memory corruption sometimes

            //c.SetParamValue("MINIMIZE_LEMMAS_STRUCT", "true");
            //c.SetParamValue("MODEL_DISPLAY_ARG_SORT", "true");



            //c.SetParamValue("enable-cores", "true");

            //c.SetParamValue("DISPLAY_PROOF", "true");
            //c.SetParamValue("PROOF_MODE", "1"); // BUG: DO NOT USE THIS OPTION, IT CAN CAUSE FORMULAS TO TOGGLE SATISFIABILITY

            this._z3 = new Z3Wrapper(c);
            this.Z3.OpenLog("asserted.log");

            this._intType = Z3.MkIntSort();
            this._realType = Z3.MkRealSort();

            this._realZero = Z3.MkRealNumeral(0);
            this._intZero = Z3.MkIntNumeral(0);
            this.IntOne = Z3.MkIntNumeral(1);

            /* can't do the following to create augmented reals: assumptions are invalid
            this.RealInf = Z3.MkConst("inf", this.RealType);
            Term assumpInf;
            Term assumpInfBound = Z3.MkConst("anyRealValue", this.RealType);
            assumpInf = Z3.MkForall(0, new Term[] {assumpInfBound}, null, this.RealInf >= assumpInfBound);
            this.Z3.AssertCnstr(assumpInf);
            this.Params.Add("inf", this.RealInf);
             * */

            switch (this.IndexOption)
            {
                case IndexOptionType.integer:
                    {
                        //this._indexType = Z3.MkSetSort(Z3.MkIntSort());
                        this._indexType = Z3.MkIntSort();
                        this.IndexOne = Z3.MkIntNumeral(1);
                        this.Params.Add("N", Z3.MkConst("N", this._intType));
                        this.IndexN = this.Params["N"];
                        break;
                    }
                case IndexOptionType.natural:
                    {
                        this._indexType = Z3.MkIntSort();
                        this.IndexOne = Z3.MkIntNumeral(1);
                        this.Params.Add("N", Z3.MkConst("N", this._intType));
                        this.IndexN = this.Params["N"];
                        break;
                    }
                case IndexOptionType.naturalOneToN:
                    {
                        this._indexType = Z3.MkIntSort();
                        this.IndexOne = Z3.MkIntNumeral(1);
                        this.Params.Add("N", Z3.MkConst("N", this._intType));
                        this.IndexN = this.Params["N"];
                        break;
                    }
                case IndexOptionType.enumeration:
                default:
                    {
                        //this._indexType = Z3.MkEnumerationSort("index", new string[] { "i1", "i2", "i3", "i4" }, new FuncDecl[4], new FuncDecl[4]);
                        this._indexType = Z3.MkEnumerationSort("index", new string[] { "i0", "i1", "i2", "i3", "i4" }, new FuncDecl[5], new FuncDecl[5]); // todo: parse the value of N, then create a sort with this many distinct elements
                        this.IndexOne = Z3.MkConst("i1", this.IndexType);
                        this.IndexNone = Z3.MkConst("i0", this.IndexType);
                        this.IndexN = Z3.MkConst("iN", this.IndexType);
                        break;
                    }
            }

            this._indexSet = Z3.MkFullSet(this._indexType);

            switch (this.DataOption)
            {
                case DataOptionType.array:
                    {
                        this.DataA.IndexedVariableDecl = new Dictionary<String, Term>();
                        this.DataA.IndexedVariableDeclPrimed = new Dictionary<String, Term>();
                        this.DataA.VariableDecl = new Dictionary<String, Term>();
                        this.DataA.VariableDeclPrimed = new Dictionary<String, Term>();
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

            if (System.Environment.MachineName.ToLower().StartsWith("johnso99"))
            {
                this._inoutPath = "C:\\Documents and Settings\\tjohnson\\My Documents\\My Dropbox\\Research\\tools\\phyea\\repos\\trunk\\input\\";
            }
            else if (System.Environment.MachineName.ToLower().StartsWith("lh-lapto"))
            {
                this._inoutPath = "C:\\Users\\tjohnson\\Dropbox\\Research\\tools\\phyea\\repos\\trunk\\input\\";
            }
            else
            {
                this._inoutPath = "D:\\Dropbox\\Research\\tools\\phyea\\repos\\trunk\\input\\";
            }

            this.Z3.EnableDebugTrace("debug");
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

        public Z3Wrapper Z3
        {
            get { return this._z3; }
        }

        public Sort RealType
        {
            get { return this._realType; }
        }

        public Term IntZero
        {
            get { return this._intZero; }
        }

        public Term RealZero
        {
            get { return this._realZero; }
        }

        public Sort IntType
        {
            get { return this._intType; }
        }

        public Sort IndexType
        {
            get { return this._indexType; }
        }

        public Term IndexSet
        {
            get { return this._indexSet; }
        }

        /**
         * Indexed control locations / modes
         */
        public IDictionary<String, Term> Q
        {
            get { return this._q; }
            set { this._q = value; }
        }

        /**
         * Primed (for resets) Indexed control locations / modes
         */
        public IDictionary<String, Term> QPrimed
        {
            get { return this._qPrimed; }
            set { this._qPrimed = value; }
        }

        public IDictionary<KeyValuePair<String, String>, Term> IndexedVariables
        {
            get { return this._ivars; }
            set { this._ivars = value; }
        }

        public IDictionary<KeyValuePair<String, String>, Term> IndexedVariablesPrimed
        {
            get { return this._ivarsPrimed; }
            set { this._ivarsPrimed = value; }
        }

        /**
         * Index variables
         */
        public IDictionary<String, Term> Indices
        {
            get { return this._indices; }
            set { this._indices = value; }
        }

        /**
         * Parameter variables
         */
        public IDictionary<String, Term> Params
        {
            get { return this._params; }
            set { this._params = value; }
        }

        /**
         * Global variables
         */
        public IDictionary<String, Term> GlobalVariables
        {
            get { return this._globalVariables; }
            set { this._globalVariables = value; }
        }

        /**
         * Primed global variables
         */
        public IDictionary<String, Term> GlobalVariablesPrimed
        {
            get { return this._globalVariablesPrimed; }
            set { this._globalVariablesPrimed = value; }
        }

        /**
         * Location labels to values
         */
        public IDictionary<String, Term> Locations
        {
            get { return this._locations; }
            set { this._locations = value; }
        }

        public AgentDataArray DataA = new AgentDataArray(); // todo: refactor, use AAgentDataTheory super class with appropriate generics
        public AgentDataUninterpreted DataU = new AgentDataUninterpreted(); // todo: refactor

        public Holism Sys;

        /**
         * @param args
         */
        public static void Main(String[] args)
        {
            String choice;
            Boolean fileSelected = false;

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


            Console.WriteLine("Select an input file: \n\r");
            foreach (var f in inputFiles)
            {
                Console.WriteLine("[" + f.Key.ToString() + "]" + " " + f.Value);
            }
            Console.WriteLine("[255] generate FORTE/FMOODS table\n\r");
            Console.WriteLine("[256] enter custom file\n\r");

            while (true)
            {
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
                    //Console.WriteLine("Error, picking default file: " + this._inputFile + ".\n\r");
                }

                Instance._inputFilePath = Instance._inoutPath + instance._inputFiles.First();

                if (File.Exists(Instance._inputFilePath))
                {
                    fileSelected = true;
                }
                else
                {
                    Console.WriteLine("Error: file " + Instance._inputFilePath + " does not exist, try again.");
                }

                if (fileSelected)
                {
                    break;
                }
            }

            foreach (String f in Instance._inputFiles)
            {
                Instance._inputFile = f;
                Instance._inputFilePath = Instance._inoutPath + f;

                Console.Write("Checking file: {0}\n\r", Instance._inputFilePath);

                String outFilename;
                outFilename = Instance._inoutPath + "..\\output\\output" + "-" + Instance._inputFile.Split('.')[0] + "-" + System.DateTime.Now.ToString("s").Replace(":", "-") + ".log";

                //Console.Clear();
                lock (Console.Out)
                {
                    // redirect console output to file
                    StreamWriter fileOutput;
                    TextWriter oldOutput;

                    oldOutput = Console.Out;
                    fileOutput = new StreamWriter(
                        new FileStream(outFilename, FileMode.Create)
                    );
                    fileOutput.AutoFlush = true;

                    Console.SetOut(fileOutput); // do the redirect
                }

                Console.Write("File: {0}\n\r\n\r", Instance._inputFilePath);

                Instance.InitializeZ3();

                ISmtSymbols smtSymbols = new SymbolsZ3();

                // constants
                Term int_zero = Instance.Z3.MkIntNumeral(0);
                Term int_one = Instance.Z3.MkIntNumeral(1);
                Term int_two = Instance.Z3.MkIntNumeral(2);
                Term real_one = Instance.Z3.MkRealNumeral(1);

                // process index variables
                Instance._indices = new Dictionary<String, Term>();
                Instance._indices.Add("i", Instance.Z3.MkConst("i", Instance.IndexType));
                Instance._indices.Add("j", Instance.Z3.MkConst("j", Instance.IndexType));
                Instance._indices.Add("k", Instance.Z3.MkConst("k", Instance.IndexType));
                Instance._indices.Add("h", Instance.Z3.MkConst("h", Instance.IndexType));

                switch (Instance.DataOption)
                {
                    case DataOptionType.array:
                        {
                            Sort locSort = Instance.Z3.MkArraySort(Instance.IndexType, Instance.IntType);
                            Term q = Instance.Z3.MkConst("q", locSort); // control location; todo: should map to finite control state (just hack to use integers for now)
                            Instance.DataA.IndexedVariableDecl.Add("q", q);
                            Term qPrime = Instance.Z3.MkConst("q'", locSort); ; // control location; todo: should map to finite control state (just hack to use integers for now)
                            Instance.DataA.IndexedVariableDeclPrimed.Add("q", qPrime);

                            // apply each index to the control location function
                            foreach (var pair in Instance.Indices)
                            {
                                Instance.Q.Add(pair.Key, Instance.Z3.MkArraySelect(q, pair.Value));
                                Instance.QPrimed.Add(pair.Key, Instance.Z3.MkArraySelect(qPrime, pair.Value));
                            }
                            break;
                        }
                    case DataOptionType.uninterpreted_function:
                    default:
                        {
                            FuncDecl q = Instance.Z3.MkFuncDecl("q", Instance.IndexType, Instance.IntType); // control location; todo: should map to finite control state (just hack to use integers for now)
                            Instance.DataU.IndexedVariableDecl.Add("q", q);
                            FuncDecl qPrime = Instance.Z3.MkFuncDecl("q'", Instance.IndexType, Instance.IntType); // control location; todo: should map to finite control state (just hack to use integers for now)
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
                        It is essentially the way to define macros using uninterpreted functions when you're working with Z3 API. Note that you have to set (set-option :macro-finder true) in order that Z3 replaces universal quantifiers with bodies of those functions.

                        However, if you're working with the textual interface, the macro define-fun in SMT-LIB v2 is an easier way to do what you want:

                        (define-fun greaterThan10 ((i Int)) Bool
                          (> i 10))
                     */



                    //Sort[] indexByIndex = { Instance.IndexType, Instance.IndexType };
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

                    //Term pt = Instance.Z3.MkForall(0, new Term[] { Instance.Indices["i"], Instance.Indices["j"] }, null, );
                    //Property p = new Property();
                    //Instance.Sys.Properties.Add(p);
                }


                // add constraints on index variables (they are between 1 and N)
                foreach (var pair in Instance._indices)
                {
                    // 1 <= i <= N, 1 <= j <= N, etc.
                    //                Instance.Z3.AssertCnstr(Instance.Z3.MkGe(pair.Value, int_one));
                    //                Instance.Z3.AssertCnstr(Instance.Z3.MkLe(pair.Value, Instance.Params["N"])); // todo: error handling, what if we don't have this parameter in the specification file?
                }

                // counter / environment abstraction
                //AbstractHybridAutomaton aha = new AbstractHybridAutomaton(sys, (AConcreteHybridAutomaton)sys.HybridAutomata.First());

                // inductive invariant checking for small model theorem
                Instance.Sys.checkInductiveInvariants();

                //PrintPhaver.writeAbstractSystem(aha, "output.pha", PrintPhaver.OutputMode.phaver);
            }

            Instance.Z3.CloseLog();
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
