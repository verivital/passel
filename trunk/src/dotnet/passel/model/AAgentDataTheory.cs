using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Z3;

namespace passel.model
{
    public abstract class AAgentDataTheory<T>
    {
        public Dictionary<String, T> IndexedVariableDecl;
        public Dictionary<String, T> IndexedVariableDeclPrimed;

        public Dictionary<String, T> VariableDecl;
        public Dictionary<String, T> VariableDeclPrimed; 
    }
}
