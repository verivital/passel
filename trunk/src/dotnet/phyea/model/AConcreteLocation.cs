using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using phyea.controller;
using Microsoft.Z3;

namespace phyea.model
{
    public abstract class AConcreteLocation : ALocation {

        private Term _statePredicate;
        private Term _valueTerm;

        public AConcreteLocation()
            : base()
        {
        }

	    public AConcreteLocation(String label, UInt32 value, Boolean initial)
            : base(label, value, initial)
        {
            this._valueTerm = Controller.Instance.Z3.MkIntNumeral(value);
            this._statePredicate = Controller.Instance.Z3.MkEq(Controller.Instance.Q["i"], this._valueTerm);

            // add label to value map
            Controller.Instance.Locations.Add(label, this._valueTerm);
	    }

        public AConcreteLocation(String label, UInt32 value, Boolean initial, Term statePredicate)
            : base(label, value, initial)
        {
            this._statePredicate = statePredicate;
        }

        public AConcreteLocation(String label, UInt32 value, Boolean initial, Term statePredicate, List<ATransition> transitions)
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
    }
}
