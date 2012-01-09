using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using phyea.controller;

namespace phyea.model
{
    /**
     * Environment states
     */
    public class EnvironmentState : Location {
        /**
         * 
         */
	    private Counter _count;

        /**
         * Maximum value this predicate counter may be
         */
        private UInt32 _maxCount;

        /**
         * 
         */
	    private Term _predicate;

        /**
         * 
         */
        private Term _statePredicate;

        /**
         * 
         */
        private Term _environmentPredicate;

        /**
         * 
         */
        public EnvironmentState(String label, UInt32 value, uint c, Term predicate)
            : base(label, value, false)
        {
            this._count = new Counter(c);
            this._predicate = predicate;
            //this._predicate = Controller.Instance.Z3.Simplify(this._predicate);
            this._statePredicate = Controller.Instance.Z3.MkEq(Controller.Instance.Q["i"], Controller.Instance.Z3.MkIntNumeral(value));
            //this._statePredicate = Controller.Instance.Z3.Simplify(this._statePredicate);

            this._environmentPredicate = Controller.Instance.Z3.MkAnd(new Term[] { Controller.Instance.Z3.MkNot(Controller.Instance.Z3.MkEq(Controller.Instance.Indices["i"], Controller.Instance.Indices["j"])), this._statePredicate, this._predicate });
            //this._environmentPredicate = Controller.Instance.Z3.Simplify(this._environmentPredicate);
	    }
	
	    public Counter Count
        {
            get { return this._count; }
            set { this._count = value; }
	    }

        /**
         * 
         */
        public Term LocationPredicate
        {
            get { return this._statePredicate; }
            set { this._statePredicate = value; }
        }
        
        /**
         * 
         */
	    public Term Predicate
        {
            get { return this._predicate; }
            set { this._predicate = value; }
	    }

        /**
         * 
         */
        public Term EnvironmentPredicate
        {
            get
            {
                // todo: efficiency: generate these once only
                Pattern[] pats = new Pattern[] { Controller.Instance.Z3.MkPattern(new Term[] { Controller.Instance.Indices["j"] }) };
                if (this.Count == Counter.All)
                {
                    Term[] bound = new Term[] { Controller.Instance.Indices["j"] };
                    return Controller.Instance.Z3.MkForall(0, bound, null, this._environmentPredicate);
                }
                if (this.Count == Counter.AllButOne)
                {
                    Term[] bound = new Term[] { Controller.Instance.Indices["j"] };
                    return Controller.Instance.Z3.MkForall(0, bound, null, this._environmentPredicate); // todo: make nested quantifier
                }
                if (this.Count == Counter.None)
                {
                    Term[] bound = new Term[] { Controller.Instance.Indices["j"] };
                    return Controller.Instance.Z3.MkForall(0, bound, null, Controller.Instance.Z3.MkNot(this._environmentPredicate));
                }
                // otherwise, it's between 1 and the cutoff, so generate the necessary number of quantifiers
                else
                {
                    uint tmp = this.Count.Value;
                    List<Term> bound = new List<Term>();
                    for (; tmp > 0; tmp--)
                    {
                        bound.Add(Controller.Instance.Indices["j"]); // todo: grab an appropriate index, need a list of all of them / a way to introduce fresh ones appropriately
                    }

                    return Controller.Instance.Z3.MkExists(0, bound.ToArray(), null, this._environmentPredicate); // todo: also need to make sure the environment predicate gets appropriately done, i.e., might have to replace internal indices based on the previous
                }
            }
            set { this._environmentPredicate = value; }
        }

        /**
         * 
         */
        public override String ToString()
        {
            //return ": q_j = " + this.Value.ToString() + " and " + this.Predicate.ToString();
            return Controller.Strip(this.EnvironmentPredicate.ToString());
        }

        /**
         * Deep copy
         */
        public override object Clone()
        {
            EnvironmentState eq = new EnvironmentState((String)this.Label.Clone(), this.Value, this.Count.Value, this._predicate);
            eq.VariableRates = this.VariableRates;
            return eq;
        }
    }
}
