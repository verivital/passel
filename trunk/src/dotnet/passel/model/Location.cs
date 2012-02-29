using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

namespace passel.model
{
    /**
     * Location of a hybrid automaton
     */
    public class Location : AState
    {
        Term _invariant;
        Term _stop;
        List<Flow> _flows = new List<Flow>();

        // todo: use this later, for now let's just have a single flow term
        IDictionary<Variable, Term> _varRates;

        public Location()
            : base()
        {
        }

        public Location(String label, UInt32 value, Boolean initial)
            : base(label, value, initial)
        {

        }

        public Location(String label, UInt32 value, Boolean initial, List<Transition> transitions)
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

        public List<Flow> Flows
        {
            get { return this._flows; }
            set { this._flows = value; }
        }

        public IDictionary<Variable, Term> VariableRates
        {
            get { return this._varRates; }
            set { this._varRates = value; }
        }

        public void setRateEqualForVar(Variable var, Term rate)
        {
            if (this._varRates == null)
            {
                this._varRates = new Dictionary<Variable, Term>();
            }

            // remove existing rate if already there
            if (this._varRates.ContainsKey(var))
            {
                this._varRates.Remove(var);
            }
            // add the newly specified rate
            this._varRates.Add(var, rate);
        }

        public override object Clone()
        {
            return null;
        }
    }
}
