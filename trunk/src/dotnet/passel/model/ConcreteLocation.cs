using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;

namespace passel.model
{
    // todo: refactor and remove this class, move to Location
    // create a new class for abstract locations if necessary once we start doing more work on abstractions
    public class ConcreteLocation : Location
    {
        public ConcreteLocation()
            : base()
        {
        }

	    public ConcreteLocation(AHybridAutomaton h, String label, UInt32 value, Boolean initial)
            : base(h, label, value, initial)
        {

	    }
        /*
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
        }*/
    }
}
