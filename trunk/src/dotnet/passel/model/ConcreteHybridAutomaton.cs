using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace passel.model
{
    public class ConcreteHybridAutomaton : AHybridAutomaton {

        public ConcreteHybridAutomaton(Holism parent, String name)
            : base(parent, name)
        {
        }
    }
}
