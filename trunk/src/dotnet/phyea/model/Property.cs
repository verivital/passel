using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using phyea.controller;
using phyea.controller.parsing;
using phyea.controller.parsing.math;
using phyea.controller.parsing.math.ast;

namespace phyea.model
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
        public Term InductiveFormula;
        private Term _formula;
        public String FormulaStr;
        private PropertyType _type;
        public StatusTypes Status = StatusTypes.toProcess;
        public List<Counterexample> Counterexamples = new List<Counterexample>();
        public List<Term> InductiveInvariants = new List<Term>();
        public List<String> Statistics = new List<String>();

        // if we prove a property, record the pass through the set of properties in which it was proved (so we may order the properties appropriately to decrease runtime)
        public int ProvedPass = 0;

        public TimeSpan Time;

        public void addInductiveInvariant(Term ii)
        {
            InductiveInvariants.Add(ii);
        }
        
        public Term Formula
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

        public Term Post;


        /**
         * 
         */
        public enum PropertyType
        {
            eventually,
            safety_weak,
            safety,         // equiv invariant
            invariant,      // equiv safety

            bad,            // neg safety
            unreachable,    // equiv bad, neg safety
        }

        /**
         * 
         */
        public Property(Term f)
        {
            this._formula = f;
        }

        public Property(String f, PropertyType t, String post)
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

            if (this._formula == null)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = Expression.Parse(this.FormulaStr);
                this._formula = LogicalExpression.CreateTerm(tmptree);
            }

            if (post != null)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = phyea.controller.parsing.math.Expression.Parse(post);
                this.Post = LogicalExpression.CreateTerm(tmptree);
            }


            switch (this.Type)
            {
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
            Controller.Instance.Z3.primeAllVariables(ref this.Post); // prime all variables in post-state formula
        }
    }
}
