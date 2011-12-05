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
        proved,
        unknown
    }

    /**
     * 
     */
    public class Property
    {
        private Term _formula;
        private String _formulaStr;
        private PropertyType _type;
        public StatusTypes Status;
        public List<Counterexample> Counterexamples = new List<Counterexample>();
        public Term InductiveInvariant;
        public Term TimedInductiveInvariant;

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
        }


        /**
         * 
         */
        public enum PropertyType
        {
            eventually,

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

        public Property(String f, PropertyType t)
        {
            this._formulaStr = f;
            this._type = t;

            switch (this._type)
            {
                // todo next: change for abstraction, using for inductive invariant checking now
                case Property.PropertyType.eventually:
                    // todo:
                    break;
                case Property.PropertyType.bad:         // neg invariant
                case Property.PropertyType.unreachable: // neg invariant
                    // do nothing
                    _formulaStr = "!(" + _formulaStr + ")"; // negate
                    break;
                case Property.PropertyType.invariant:   // invariant
                case Property.PropertyType.safety:      // invariant
                    break;
            }

            if (this._formula == null)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = Expression.Parse(_formulaStr);
                this._formula = LogicalExpression.CreateTerm(tmptree);
            }
        }
    }
}
