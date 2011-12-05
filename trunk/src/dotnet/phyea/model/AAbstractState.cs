using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using phyea.controller;

namespace phyea.model
{
    /**
     * A state of the abstract system
     *
     * The abstract states are tuples
     */
    public abstract class AAbstractState : ALocation, IDisposable
    {
        /**
         * flag used in garbage collection
         */
        private bool _dispose;

        /**
         * predicate describing the concrete states represented by this abstract state
         */
        private Term _concretization;

        /**
         * primed version of the predicate describing the concrete states represented by this abstract state
         */
        private Term _concretizationPrimed;

        /**
         * Control location of the reference process
         */
        private AConcreteLocation _stateRef;

        /**
         * Control location and predicate abstraction valuation of the environment process
         */
        private List<EnvironmentState> _stateEnv = new List<EnvironmentState>(); // how to link up the corresponding concrete states for easy access? e.g., given abstract tuple, get the concrete predicates being abstracted

        /**
         * 
         */
        public AAbstractState(AConcreteLocation rstate, List<EnvironmentState> estates)
            : base("", UInt32.MaxValue, false)
        {
            this._stateRef = rstate;
            this._stateEnv = estates;
            this._concretization = null;
        }

        /**
         * 
         */
        public AAbstractState(AConcreteLocation rstate, List<EnvironmentState> estates, List<ATransition> transitions)
            : base("", UInt32.MaxValue, false) {
		    this._stateRef = rstate;
		    this._stateEnv = estates;
            this.Transitions = transitions;
            this._concretization = null;
	    }
	
        /**
         * 
         */
	    public AConcreteLocation ReferenceState
        {
		    get { return this._stateRef; }
            set { this._stateRef = value; }
	    }
	
        /**
         * 
         */
	    public List<EnvironmentState> EnvironmentStates
        {
            get
            {
                if (this._stateEnv == null)
                {
                    this._stateEnv = new List<EnvironmentState>();
                }
                return this._stateEnv;
            }
            set { this._stateEnv = value; }
	    }

        /**
         * 
         */
	    public void addEnvironmentState(EnvironmentState e)
        {
            if (this._stateEnv == null)
            {
                this._stateEnv = new List<EnvironmentState>();
            }
		    this._stateEnv.Add(e);
	    }

        /**
         * 
         */
        public override String ToString()
        {
            String o = this._stateRef.ToString();

            foreach (EnvironmentState es in this._stateEnv)
            {
                o += es.Value.ToString() + ",";
            }
            return o;
        }

        /**
         * Given this abstract state, return the concretization formula
         */
        public Term Concretization()
        {
            if (this._concretization == null)
            {
                List<Term> c = new List<Term>();
                foreach (EnvironmentState e in this._stateEnv)
                {
                    c.Add(e.EnvironmentPredicate);
                }
                //c.Add(this._stateRef.StatePredicate);
                this._concretization = Controller.Instance.Z3.MkAnd(c.ToArray());
                //this._concretization = Controller.Instance.Z3.Simplify(this._concretization);
            }
            return this._concretization;
        }

        /**
         * Return a primed version of the concrete formula (for finding feasible transitions)
         */
        public Term ConcretizationPrimed()
        {
            if (this._concretizationPrimed == null)
            {
                this._concretizationPrimed = this._concretization;
                foreach (var pair in Controller.Instance.Q)
                {
                    Controller.Instance.Z3.replaceTerm(ref this._concretizationPrimed, this._concretizationPrimed, pair.Value, Controller.Instance.QPrimed[pair.Key], true);
                }
                foreach (var pair in Controller.Instance.IndexedVariables)
                {
                    Controller.Instance.Z3.replaceTerm(ref this._concretizationPrimed, this._concretizationPrimed, pair.Value, Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<String, String>(pair.Key.Key + "'", pair.Key.Value)], true);
                }
            }
            return this._concretizationPrimed;
        }

        /**
         * 
         */
        public void Dispose()
        {
            Dispose(true);
            GC.SuppressFinalize(this);
        }

        /**
         * 
         */
        private void Dispose(bool disposing)
        {
            // Check to see if Dispose has already been called.
            if (!this._dispose)
            {
                // If disposing equals true, dispose all managed and unmanaged resources.
                if (disposing)
                {
                    // Dispose managed resources.
                    this._label = null;
                    this._stateRef = null;
                    this._stateEnv = null;
                }
            }
            this._dispose = true;
        }

        ~AAbstractState()
        {
            this.Dispose(false);
        }
    }
}
