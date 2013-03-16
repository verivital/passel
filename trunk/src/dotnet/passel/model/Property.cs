using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller.smt.z3;

using passel.controller;
using passel.controller.parsing;
using passel.controller.parsing.math;
using passel.controller.parsing.math.ast;

namespace passel.model
{
    public enum StatusTypes
    {
        disproved,
        inductive,
        inductiveInvariant,
        inductiveWeak,
        unknown,
        toProcess,
        toProject,
        toDelete,
    }

    public enum SourceTypes
    {
        invisible_invariants,
        split_invariants,
        user,
    }

    /**
     * 
     */
    public class Property
    {
        public Expr InductiveFormula;
        private Expr _formula;
        public String FormulaStr;
        private PropertyType _type;
        public StatusTypes Status = StatusTypes.toProcess;
        public List<Counterexample> Counterexamples = new List<Counterexample>();
        public List<Expr> InductiveInvariants = new List<Expr>();
        public List<String> Statistics = new List<String>();

        public List<Transition> TransitionsProved = new List<Transition>();
        public Boolean TrajectoryProved = false;
        public Boolean InitialProved = false;


        // have to use this since the .NET apis have poor support for traversing quantifiers (e.g., have to do crazy things like string replacement since you apparently can access a mapping from fresh variable names to quantified variables)
        public Expr Unquantified;

        // if we prove a property, record the pass through the set of properties in which it was proved (so we may order the properties appropriately to decrease runtime)
        public int ProvedPass = 0;

        public int QuantInstantiations = 0;

        public TimeSpan Time;

        public uint Project = 0; // N projected onto (abstract)
        public uint ProjectedFrom = 0; // N projected from (concrete)

        public void addInductiveInvariant(Expr ii)
        {
            InductiveInvariants.Add(ii);
        }

        public Expr Formula
        {
            get
            {
                return this._formula;
            }
            set { this._formula = value; }
        }

        public PropertyType Type
        {
            get { return this._type; }
            set { this._type = value; }
        }

        public SourceTypes SourceType;
        
        public Expr Post;

        /**
         * 
         */
        public enum PropertyType
        {
            eventually,
            termination,    // ranking function synthesis

            safety_weak,
            safety,         // equiv invariant
            invariant,      // equiv safety

            bad,            // neg safety
            unreachable,    // equiv bad, neg safety
        }

        /**
         * 
         */
        public enum RankingTemplateType
        {
            affine,     // ranking function is generated as an affine (linear) function of program variables
            linear,     // equiv affine
        }

        public RankingTemplateType TemplateType;

        public Expr FormulaRankLhs;
        public Expr FormulaRankRhs;

        public override String ToString()
        {
            return this.Formula.ToString();
        }

        /**
         * 
         */
        public static Property PropertyFromSmt(String pstr)
        {
            //BoolExpr prop = Controller.Instance.Z3.ParseSMTLIB2String( "(benchmark tst :formula" + pstr + ")");
            //pstr = pstr.Replace("\n", "").Replace("\r", "");
            //new Sort[] { Controller.Instance.LocType }
            //foreach (var decl in Controller.Instance.DataU.IndexedVariableDecl.Values)
            //{
            //    decl.
            //}
            pstr = "(assert " + pstr + ")";


            //BoolExpr prop = Controller.Instance.Z3.ParseSMTLIB2String(pstr, null, null, null, null);
            //BoolExpr prop = Controller.Instance.Z3.ParseSMTLIB2String("(assert " + pstr + ")", null, null, null, Controller.Instance.DataU.IndexedVariableDecl.Values.ToArray());
            //BoolExpr prop = Controller.Instance.Z3.ParseSMTLIB2String("(declare-fun a () (_ BitVec 8)) (assert (bvuge a #x10)) (assert (bvule a #xf0))");


            // set up declarations and names (doesn't use existing context information)
            List<FuncDecl> decls = new List<FuncDecl>();
            List<Symbol> names = new List<Symbol>();
            foreach (var decl in Controller.Instance.DataU.IndexedVariableDecl)
            {
                decls.Add(decl.Value);
                names.Add(decl.Value.Name);
            }

            foreach (var decl in Controller.Instance.DataU.VariableDecl)
            {
                decls.Add(decl.Value);
                names.Add(decl.Value.Name);
            }

            foreach (var decl in Controller.Instance.GlobalVariables)
            {
                decls.Add(decl.Value.FuncDecl);
                names.Add(decl.Value.FuncDecl.Name);
            }

            foreach (var decl in Controller.Instance.Locations)
            {
                decls.Add(decl.Value.FuncDecl);
                names.Add(decl.Value.FuncDecl.Name);
            }

            foreach (var decl in Controller.Instance.Indices)
            {
                decls.Add(decl.Value.FuncDecl);
                names.Add(decl.Value.FuncDecl.Name);
            }

            foreach (var decl in Controller.Instance.Params)
            {
                decls.Add(decl.Value.FuncDecl);
                names.Add(decl.Value.FuncDecl.Name);
            }

            // for q_1, etc.
            foreach (var decl in Controller.Instance.IndexedVariables)
            {
                decls.Add(decl.Value.FuncDecl);
                names.Add(decl.Value.FuncDecl.Name);
            }

            decls = decls.Distinct().ToList();
            //names = names.Distinct().ToList();
            names = names.GroupBy(n => n.ToString()).Select(grp => grp.First()).ToList(); // distinct didn't work

            pstr = pstr.Replace("\n", "");
            pstr = pstr.Replace("\r", "");

            // from params
            //decls.Add(Controller.Instance.IndexN.FuncDecl);
            //names.Add(Controller.Instance.IndexN.FuncDecl.Name);
            System.Console.WriteLine("Before smt parsing");
            BoolExpr prop = Controller.Instance.Z3.ParseSMTLIB2String(pstr, null, null, names.ToArray(), decls.ToArray());
            System.Console.WriteLine("Done with smt parsing");
            //BoolExpr prop = Controller.Instance.Z3.ParseSMTLIB2String(pstr);
            return new Property(prop);
        }

        /**
         * 
         */
        public Property(Expr f)
        {
            this._formula = f;
            this.Post = primeAllByValue( f);
        }

        /**
         * Hack to avoid thrashing original formula
         */
        private Expr primeAllByValue(Expr f)
        {
            // huge hack to avoid clobbering original formula with pass-by-reference
            // we create a new z3 context and "translate" (copy) the term to that context, then copy it back
            // we cannot just "translate" to the same context, because it checks if the context is the same and returns the original reference if so
            Context tmpcontext = new Context(Controller.Instance.Config);
            Expr fcopy = f.Translate(tmpcontext);
            Expr fcopyback = fcopy.Translate(Controller.Instance.Z3);

            Controller.Instance.Z3.primeAllVariables(ref fcopyback);
            return fcopyback;
        }

        /**
         * Make a primed version of the formula for the post-state representation
         */
        public void makePost()
        {
            this.Post = primeAllByValue(this.Formula);
        }

        public Property(String f, PropertyType t, String post, String template)
        {
            this.FormulaStr = f;
            this._type = t;
            this.Status = StatusTypes.toProcess;

            switch (this._type)
            {
                // todo next: change for abstraction, using for inductive invariant checking now
                case Property.PropertyType.eventually:
                    // todo:
                    break;
                case Property.PropertyType.bad:         // neg invariant
                case Property.PropertyType.unreachable: // neg invariant
                    FormulaStr = "!(" + this.FormulaStr + ")"; // negate
                    break;

                // do nothing
                case Property.PropertyType.invariant:   // invariant
                case Property.PropertyType.safety:      // invariant
                    break;
            }

            if (this._formula == null && f != null)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = Expression.Parse(this.FormulaStr);
                Expression.FixTypes(ref tmptree);
                this._formula = LogicalExpression.CreateTerm(tmptree);
            }

            if (post == null)
            {
                post = f;
            }

            if (post != null)
            {
                //Antlr.Runtime.Tree.CommonTree tmptree = Expression.Parse(post);
                //this.Post = LogicalExpression.CreateTerm(tmptree);
                //Controller.Instance.Z3.primeAllVariables(ref this.Post); // prime all variables in post-state formula

                this.Post = primeAllByValue(this.Formula);
            }

            switch (this.Type)
            {
                case PropertyType.termination: // pass through
                case PropertyType.eventually:
                    {
                        if (template != null)
                        {
                            Enum.TryParse<RankingTemplateType>(template, false, out this.TemplateType);
                        }

                        switch (this.TemplateType)
                        {
                            default:
                                {
                                    // todo: generalize for indexed variables
                                    // todo: make 2nd argument be the tuple-length we are currently add (needs another parsing input)

                                    List<BoolExpr> ts = new List<BoolExpr>();
                                    // todo: temporarily, we will make the tuple be the length of the number of variables
                                    for (int i = 0; i < Controller.Instance.GlobalVariables.Count; i++)
                                    {
                                        ts.Add(Controller.Instance.Z3.MkGe((ArithExpr)this.generateAffineTemplate(Controller.Instance.GlobalVariables, "i", i, false), Controller.Instance.RealZero)); // template >= 0
                                    }

                                    this.Formula = Controller.Instance.Z3.MkAnd(ts.ToArray()); // todo: detect size; actually, we should override this in MkAnd to not actually do a mkand if length is 1

                                    Expr lhs = this.generateAffineTemplate(Controller.Instance.GlobalVariables, "c", 0, true);
                                    Expr rhs = this.generateAffineTemplate(Controller.Instance.GlobalVariablesPrimed, "c", 0, true); // todo: assumes GlobalVariables and GlobalVariablesPrimed are in the same order

                                    this.FormulaRankLhs = lhs;
                                    this.FormulaRankRhs = rhs;
                                    break;
                                }
                        }
                        break;
                    }
                case Property.PropertyType.safety_weak:
                    {
                        // do nothing, already has post set
                        break;
                    }
                case Property.PropertyType.invariant:
                case Property.PropertyType.safety:
                default:
                    {
                        break;
                    }
            }
        }

        public Expr generateAffineTemplate(IDictionary<String, Expr> lv, String prefix, int base_num, bool linear)
        {
            Expr t = null;
            List<ArithExpr> ts = new List<ArithExpr>();
            
            for (int i = 0; i <= lv.Count; i++)
            {
                // don't concat the affine term if linear is true
                if (i == lv.Count && linear)
                {
                    break;
                }

                String name = prefix + base_num.ToString() + "_" + i.ToString();
                Expr factor = Controller.Instance.Z3.MkRealConst(name); // todo: toreal detection
                if (!Controller.Instance.ExistentialConstants.ContainsKey(name))
                {
                    Controller.Instance.ExistentialConstants.Add(name, factor); // global list of constants
                }

                if (i < lv.Count)
                {
                    ts.Add(Controller.Instance.Z3.MkMul((ArithExpr)factor, Controller.Instance.Z3.MkInt2Real((IntExpr)lv.Values.ElementAt(i))));
                }
                else
                {
                    ts.Add((ArithExpr)factor); // affine part only
                }
            }

            // todo: toreal detection
            t = Controller.Instance.Z3.MkAdd(ts.ToArray()); // c0_0 * v0 + c0_1 * v1 + .. * c0_1 * vn
            return t;
        }
    }
}
