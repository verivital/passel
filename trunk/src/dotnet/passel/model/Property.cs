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
    }

    /**
     * 
     */
    public class Property
    {
        private static Z3Wrapper z3 = Controller.Instance.Z3;


        public Expr InductiveFormula;
        private Expr _formula;
        public String FormulaStr;
        private PropertyType _type;
        public StatusTypes Status = StatusTypes.toProcess;
        public List<Counterexample> Counterexamples = new List<Counterexample>();
        public List<Expr> InductiveInvariants = new List<Expr>();
        public List<String> Statistics = new List<String>();

        // if we prove a property, record the pass through the set of properties in which it was proved (so we may order the properties appropriately to decrease runtime)
        public int ProvedPass = 0;

        public int QuantInstantiations = 0;

        public TimeSpan Time;

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

        /**
         * 
         */
        public Property(Expr f)
        {
            this._formula = f;
        }

        public Property(String f, PropertyType t, String post, String template)
        {
            this.FormulaStr = f;
            this._type = t;

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
                this._formula = LogicalExpression.CreateTerm(tmptree);
            }

            if (post != null)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = passel.controller.parsing.math.Expression.Parse(post);
                this.Post = LogicalExpression.CreateTerm(tmptree);
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
                                        ts.Add(z3.MkGe((ArithExpr)this.generateAffineTemplate(Controller.Instance.GlobalVariables, "i", i, false), Controller.Instance.RealZero)); // template >= 0
                                    }

                                    this.Formula = z3.MkAnd(ts.ToArray()); // todo: detect size; actually, we should override this in MkAnd to not actually do a mkand if length is 1

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
                        this.Post = this.Formula;
                        break;
                    }
            }
            this.Post = this.Formula;
            z3.primeAllVariables(ref this.Post); // prime all variables in post-state formula
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
                Expr factor = z3.MkRealConst(name); // todo: toreal detection
                if (!Controller.Instance.ExistentialConstants.ContainsKey(name))
                {
                    Controller.Instance.ExistentialConstants.Add(name, factor); // global list of constants
                }

                if (i < lv.Count)
                {
                    ts.Add(z3.MkMul((ArithExpr)factor, z3.MkInt2Real((IntExpr)lv.Values.ElementAt(i))));
                }
                else
                {
                    ts.Add((ArithExpr)factor); // affine part only
                }
            }

            // todo: toreal detection
            t = z3.MkAdd(ts.ToArray()); // c0_0 * v0 + c0_1 * v1 + .. * c0_1 * vn
            return t;
        }
    }
}
