using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

namespace phyea.model
{
    /**
     * Location of a hybrid automaton
     */
    public abstract class ALocation : AState
    {
        Term _invariant;
        Term _stop;
        Term _flow;
        // todo: use this later, for now let's just have a single flow term
        IDictionary<AVariable, Term> _varRates;

        public ALocation()
            : base()
        {
        }

        public ALocation(String label, UInt32 value, Boolean initial)
            : base(label, value, initial)
        {

        }

        public ALocation(String label, UInt32 value, Boolean initial, List<ATransition> transitions)
            : base(label, value, initial, transitions)
        {

        }

        public Term Invariant
        {
            get { return this._invariant; }
            set { this._invariant = value; }
        }

        public Term Stop
        {
            get { return this._stop; }
            set { this._stop = value; }
        }

        public Term Flow
        {
            get { return this._flow; }
            set { this._flow = value; }
        }

        public IDictionary<AVariable, Term> VariableRates
        {
            get { return this._varRates; }
            set { this._varRates = value; }
        }

        public void setRateEqualForVar(AVariable var, Term rate)
        {
            if (this._varRates == null)
            {
                this._varRates = new Dictionary<AVariable, Term>();
            }

            // remove existing rate if already there
            if (this._varRates.ContainsKey(var))
            {
                this._varRates.Remove(var);
            }
            // add the newly specified rate
            this._varRates.Add(var, rate);
        }
    }
}
