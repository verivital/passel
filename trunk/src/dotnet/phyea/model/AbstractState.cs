using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace phyea.model
{
    public class AbstractState : AAbstractState
    {
	    /**
	     * @param initial
	     */
	    public AbstractState(AConcreteLocation rstate, List<EnvironmentState> estates ) : base(rstate, estates) {
	    }

        /**
         * deep copy for pass by value
         */
        public override object Clone()
        {
            // deep copy the list
            List<EnvironmentState> newList = new List<EnvironmentState>(this.EnvironmentStates.Count);
            this.EnvironmentStates.ForEach((item) =>
            {
                newList.Add((EnvironmentState)item.Clone());
            });

            AbstractState aq = new AbstractState((AConcreteLocation)this.ReferenceState, newList);
            aq.VariableRates = this.VariableRates;

            // don't clone the reference state (not necessary to do so as we don't modify it, and if we do clone it, have to write a method to clone pointers for the concrete transition relation)
            return aq;
        }
    }
}
