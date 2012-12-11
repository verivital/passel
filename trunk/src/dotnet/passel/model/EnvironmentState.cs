using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;

namespace passel.model
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
	    private Expr _predicate;

        /**
         * 
         */
        private Expr _statePredicate;

        /**
         * 
         */
        private Expr _environmentPredicate;

        /**
         * 
         */
        public EnvironmentState(String label, UInt32 value, uint c, Expr predicate)
            : base(label, value, false)
        {
            this._count = new Counter(c);
            this._predicate = predicate;
            //this._predicate = Controller.Instance.Z3.Simplify(this._predicate);
            this._statePredicate = Controller.Instance.Z3.MkEq(Controller.Instance.IndexedVariables[new KeyValuePair<string,string>("q", "i")], Controller.Instance.Z3.MkInt(value));
            //this._statePredicate = Controller.Instance.Z3.Simplify(this._statePredicate);

            this._environmentPredicate = Controller.Instance.Z3.MkAnd(new BoolExpr[] { Controller.Instance.Z3.MkNot(Controller.Instance.Z3.MkEq(Controller.Instance.Indices["i"], Controller.Instance.Indices["j"])), (BoolExpr)this._statePredicate, (BoolExpr)this._predicate });
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
        public Expr LocationPredicate
        {
            get { return this._statePredicate; }
            set { this._statePredicate = value; }
        }
        
        /**
         * 
         */
        public Expr Predicate
        {
            get { return this._predicate; }
            set { this._predicate = value; }
	    }

        /**
         * 
         */
        public Expr EnvironmentPredicate
        {
            get
            {
                // todo: efficiency: generate these once only
                Pattern[] pats = new Pattern[] { Controller.Instance.Z3.MkPattern(new Expr[] { Controller.Instance.Indices["j"] }) };
                if (this.Count == Counter.All)
                {
                    Expr[] bound = new Expr[] { Controller.Instance.Indices["j"] };
                    return Controller.Instance.Z3.MkForall(bound, this._environmentPredicate);
                }
                if (this.Count == Counter.AllButOne)
                {
                    Expr[] bound = new Expr[] { Controller.Instance.Indices["j"] };
                    return Controller.Instance.Z3.MkForall(bound, this._environmentPredicate); // todo: make nested quantifier
                }
                if (this.Count == Counter.None)
                {
                    Expr[] bound = new Expr[] { Controller.Instance.Indices["j"] };
                    return Controller.Instance.Z3.MkForall(bound, Controller.Instance.Z3.MkNot((BoolExpr)this._environmentPredicate));
                }
                // otherwise, it's between 1 and the cutoff, so generate the necessary number of quantifiers
                else
                {
                    uint tmp = this.Count.Value;
                    List<Expr> bound = new List<Expr>();
                    for (; tmp > 0; tmp--)
                    {
                        bound.Add(Controller.Instance.Indices["j"]); // todo: grab an appropriate index, need a list of all of them / a way to introduce fresh ones appropriately
                    }

                    return Controller.Instance.Z3.MkExists(bound.ToArray(), this._environmentPredicate); // todo: also need to make sure the environment predicate gets appropriately done, i.e., might have to replace internal indices based on the previous
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
