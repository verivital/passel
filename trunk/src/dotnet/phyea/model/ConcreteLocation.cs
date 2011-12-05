using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

namespace phyea.model
{
    public class ConcreteLocation : AConcreteLocation
    {
        public ConcreteLocation()
            : base()
        {
        }
        
        public ConcreteLocation(String label, UInt32 value, Boolean initial)
            : base(label, value, initial) {
	    }

        public override object Clone()
        {
            // deep copy the list
            List<ATransition> newList = new List<ATransition>(this.Transitions.Count);
            this.Transitions.ForEach((item) =>
            {
                newList.Add((ATransition)item.Clone());
            });

            // reference the dictionary
            ALocation cl = new ConcreteLocation((String)this.Label.Clone(), this.Value, this.Initial);
            cl.VariableRates = this.VariableRates;

            return cl;
        }
    }
}
