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
        private IDictionary<String, Term> _q = new Dictionary<String, Term>();

        /**
         * Special variable for control states / locations (modes)
         * - All other variables go into the _vars dictionary
         */
        private IDictionary<String, Term> _qPrimed = new Dictionary<String, Term>();
        
        /**
         * Indexed variables: input, e.g., (x i) returns the function corresponding to variable x at process i
         * 
         */
        private IDictionary<KeyValuePair<String, String>, Term> _ivars = new Dictionary<KeyValuePair<String, String>, Term>();

        /**
         * Primed indexed variables: input, e.g., (x' i) returns the function corresponding to variable x at process i
         * 
         */
        private IDictionary<KeyValuePair<String, String>, Term> _ivarsPrimed = new Dictionary<KeyValuePair<String, String>, Term>();

        /**
         * Parameter variables (N, S, etc.)
         */
        private IDictionary<String, Term> _params = new Dictionary<String, Term>();

        /**
         * Primed parameter variables (i.e., global variables)
         */
        private IDictionary<String, Term> _paramsPrimed = new Dictionary<String, Term>();

        /**
         * Location labels to value map
         */
        private IDictionary<String, Term> _locations = new Dictionary<String, Term>();

        /**
         * Process indices (i, j, k, etc.)
         */
        private IDictionary<String, Term> _indices = new Dictionary<String, Term>();

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

        /**
         * theory used to model variables of each agent in the system
         */
        public enum DataOptionType { array, uninterpreted_function };

        /**
         * set used to model indices of processes
         */
        public enum IndexOptionType { integer, natural, naturalOneToN, enumeration };

        /**
         * implies is weak, and is strict
         */
        public enum ExistsOptionType { implies, and };

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
            Config c = new Config();

            c.SetParamValue("AUTO_CONFIG", "false"); // disable auto-configuration (use all logics)

            /*c.SetParamValue("ARRAY_CANONIZE", "true");
            c.SetParamValue("ARRAY_CG", "true");
            c.SetParamValue("ARRAY_LAZY_IEQ", "true");
            c.SetParamValue("ARRAY_WEAK", "true");
             */
            //c.SetParamValue("ARRAY_SOLVER", "1"); // 0 to 3

            c.SetParamValue("MODEL", "true");

            c.SetParamValue("QI_PROFILE", "true");
            c.SetParamValue("QI_PROFILE_FREQ", "1000");

            c.SetParamValue("ELIM_QUANTIFIERS", "true");
            c.SetParamValue("STRONG_CONTEXT_SIMPLIFIER", "true");
            c.SetParamValue("CONTEXT_SIMPLIFIER", "true");

            c.SetParamValue("EMATCHING", "true");
            c.SetParamValue("MACRO_FINDER", "true");
            c.SetParamValue("MBQI", "true"); //  (see http://research.microsoft.com/en-us/um/redmond/projects/z3/mbqi-tutorial/)
            c.SetParamValue("MBQI_MAX_ITERATIONS", "50000");
            c.SetParamValue("MBQI_TRACE", "true");
            c.SetParamValue("PI_PULL_QUANTIFIERS", "true");
            c.SetParamValue("PULL_NESTED_QUANTIFIERS", "true");
            c.SetParamValue("MODEL_PARTIAL", "true");
            c.SetParamValue("MODEL_V2", "true");
            c.SetParamValue("VERBOSE", "10");

            c.SetParamValue("MODEL_COMPACT", "true"); // slower, but more accurate (as in the models are more useful) it seems

            c.SetParamValue("MODEL_ON_FINAL_CHECK", "true");

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

            //c.SetParamValue("CHECK_PROOF", "true");
            c.SetParamValue("DISPLAY_ERROR_FOR_VISUAL_STUDIO", "true");
            c.SetParamValue("DISTRIBUTE_FORALL", "true");
            c.SetParamValue("DL_COMPILE_WITH_WIDENING", "true");
            //c.SetParamValue("DACK", "2");
            //c.SetParamValue("DACK_EQ", "true");
            
            c.SetParamValue("QI_LAZY_INSTANTIATION", "true");
            c.SetParamValue("ELIM_BOUNDS", "true");

            // some bugs in the next ones
            //c.SetParamValue("ELIM_NLARITH_QUANTIFIERS", "true");
            //c.SetParamValue("FWD_SR_CHEAP", "true");
            //c.SetParamValue("LOOKAHEAD", "true");
            //c.SetParamValue("MBQI_MAX_CEXS", "true"); // crashes
            //c.SetParamValue("MODEL_VALIDATE", "true"); // corrupts memory?
            // end buggy ones

            
            //c.SetParamValue("LOOKAHEAD_DISEQ", "true");

            c.SetParamValue("PULL_CHEAP_ITE_TREES", "true");
            //c.SetParamValue("LIFT_ITE", "2"); // buggy: get memory corruption sometimes
            //c.SetParamValue("ELIM_TERM_ITE", "true"); // buggy: get memory corruption sometimes

            c.SetParamValue("MINIMIZE_LEMMAS_STRUCT", "true");
            c.SetParamValue("MODEL_COMPLETION", "true");
            c.SetParamValue("MODEL_DISPLAY_ARG_SORT", "true");

            c.SetParamValue("ARITH_EUCLIDEAN_SOLVER", "true");
            c.SetParamValue("ARITH_FORCE_SIMPLEX", "true");
            c.SetParamValue("ARITH_MAX_LEMMA_SIZE", "512"); // default 128

            //c.SetParamValue("enable-cores", "true");
            
            c.SetParamValue("DISPLAY_UNSAT_CORE", "true");
            c.SetParamValue("DISPLAY_PROOF", "true");
            c.SetParamValue("PROOF_MODE", "1");

            this._z3 = new Z3Wrapper(c);
            this.Z3.OpenLog("asserted.log");

            this._intType = Z3.MkIntSort();
            this._realType = Z3.MkRealSort();

            this._realZero = Z3.MkRealNumeral(0);
            this._intZero = Z3.MkIntNumeral(0);
            this.IntOne = Z3.MkIntNumeral(1);

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
                this._inoutPath = "C:\\Documents and Settings\\tjohnson\\My Documents\\My Dropbox\\SmallModels\\code\\input\\";
            }
            else if (System.Environment.MachineName.ToLower().StartsWith("lh-lapto"))
            {
                this._inoutPath = "C:\\Users\\tjohnson\\Dropbox\\SmallModels\\code\\input\\";
            }
            else
            {
                this._inoutPath = "D:\\Dropbox\\SmallModels\\code\\input\\";
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
         * Primed parameter variables
         */
        public IDictionary<String, Term> ParamsPrimed
        {
            get { return this._paramsPrimed; }
            set { this._paramsPrimed = value; }
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
            Console.WriteLine("Select an input file option: \n\r[0] smt_fischer_hyxml.xml (default)\n\r[1] smt_fischer_buggy_hyxml.xml\n\r[2] smt_sats_hyxml.xml\n\r[3] smt_sats_buggy_hyxml.xml\n\r[4] smt_nfa_hyxml.xml\n\r[5] smt_nfa_buggy_hyxml.xml\n\r[6] smt_ta_hyxml.xml\n\r[7] smt_ta_buggy_hyxml.xml\n\r[8] smt_gv_hyxml.xml\n\r[9] smt_gv_buggy_hyxml.xml\n\r[10] smt_sats_timed_hyxml.xml\n\r[11] smt_sats_timed_buggy_hyxml.xml\n\r[12] smt_flocking_hyxml.xml\n\r[13] smt_flocking_buggy_hyxml.xml\n\r[256] enter custom file\n\r");

            while (true)
            {
                choice = Console.ReadLine();
                try
                {
                    if (choice != null)
                    {
                        UInt32 io_opt = UInt32.Parse(choice);

                        switch (io_opt)
                        {
                            case 0:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_fischer_hyxml.xml";
                                    break;
                                }
                            case 1:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_fischer_buggy_hyxml.xml";
                                    break;
                                }
                            case 2:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_sats_hyxml.xml";
                                    break;
                                }
                            case 3:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_sats_buggy_hyxml.xml";
                                    break;
                                }
                            case 4:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_nfa_hyxml.xml";
                                    break;
                                }
                            case 5:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_nfa_buggy_hyxml.xml";
                                    break;
                                }
                            case 6:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_ta_hyxml.xml";
                                    break;
                                }
                            case 7:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_ta_buggy_hyxml.xml";
                                    break;
                                }
                            case 8:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_gv_hyxml.xml";
                                    break;
                                }
                            case 9:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_gv_buggy_hyxml.xml";
                                    break;
                                }
                            case 10:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_sats_timed_hyxml.xml";
                                    break;
                                }
                            case 11:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_sats_timed_buggy_hyxml.xml";
                                    break;
                                }
                            case 12:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_flocking_hyxml.xml";
                                    break;
                                }
                            case 13:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_flocking_buggy_hyxml.xml";
                                    break;
                                }
                            case 14:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_fischer_umeno_hyxml.xml";
                                    break;
                                }
                            case 256:
                                {
                                    Console.WriteLine("Using path " + Instance._inoutPath);
                                    Instance._inputFile = Instance._inoutPath + Console.ReadLine();
                                    Console.WriteLine("File: " + Instance._inputFile + "\n\r");
                                    break;
                                }
                            default:
                                {
                                    Instance._inputFile = Instance._inoutPath + "smt_fischer_hyxml.xml";
                                    break;
                                }
                        }
                    }
                }
                catch (Exception)
                {
                    Instance._inputFile = Instance._inoutPath + "smt_fischer_hyxml.xml";
                    //Console.WriteLine("Error, picking default file: " + this._inputFile + ".\n\r");
                }

                if (File.Exists(Instance._inputFile))
                {
                    fileSelected = true;
                }
                else
                {
                    Console.WriteLine("Error: file " + Instance._inputFile + " does not exist, try again.");
                }

                if (fileSelected)
                {
                    break;
                }
            }

            Console.Write("Checking file: {0}\n\r", Instance._inputFile);

            String outFilename;
            outFilename = Instance._inoutPath + "output" + System.DateTime.Now.ToString("s").Replace(":", "-") + ".log";

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

            Console.Write("File: {0}\n\r\n\r", Instance._inputFile);

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

            Instance.Sys = ParseHyXML.ParseFile(Instance._inputFile);

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
