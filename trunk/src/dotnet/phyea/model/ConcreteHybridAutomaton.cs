using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace phyea.model
{
    public class ConcreteHybridAutomaton : AConcreteHybridAutomaton {

        public ConcreteHybridAutomaton(AHolism parent)
            : base(parent)
        {
        }
    }
}
