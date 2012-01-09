using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using phyea.controller;

namespace phyea.model
{
    public class ConcreteLocation : Location
    {
        private Term _statePredicate;
        private Term _valueTerm;

        public ConcreteLocation()
            : base()
        {
        }

	    public ConcreteLocation(String label, UInt32 value, Boolean initial)
            : base(label, value, initial)
        {
            this._valueTerm = Controller.Instance.Z3.MkIntNumeral(value);
            this._statePredicate = Controller.Instance.Z3.MkEq(Controller.Instance.Q["i"], this._valueTerm);

            // add label to value map
            Controller.Instance.Locations.Add(label, this._valueTerm);
	    }

        public ConcreteLocation(String label, UInt32 value, Boolean initial, Term statePredicate)
            : base(label, value, initial)
        {
            this._statePredicate = statePredicate;
        }

        public ConcreteLocation(String label, UInt32 value, Boolean initial, Term statePredicate, List<Transition> transitions)
            : base(label, value, initial)
        {
            this.Transitions = transitions;
            this._statePredicate = statePredicate;
        }

        public Term StatePredicate
        {
            get { return this._statePredicate; }
            set { this._statePredicate = value; }
        }

        public Term StateValue
        {
            get { return this._valueTerm; }
            set { this._valueTerm = value; }
        }

        public override object Clone()
        {
            // deep copy the list
            List<Transition> newList = new List<Transition>(this.Transitions.Count);
            this.Transitions.ForEach((item) =>
            {
                newList.Add((Transition)item.Clone());
            });

            // reference the dictionary
            Location cl = new ConcreteLocation((String)this.Label.Clone(), this.Value, this.Initial);
            cl.VariableRates = this.VariableRates;

            return cl;
        }
    }
}
