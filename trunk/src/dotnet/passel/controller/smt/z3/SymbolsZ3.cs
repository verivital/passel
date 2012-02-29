using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace passel.controller.smt.z3
{
    public class SymbolsZ3 : ISmtSymbols
    {
        public String NEGATION
        {
            get { return "not"; }
        }
        public String CONJUNCTION
        {
            get { return "and"; }
        }
        public String DISJUNCTION
        {
            get { return "or"; }
        }
        public String IMPLICATION
        {
            get { return "imply"; }
        }
        public String SEPARATOR_LEFT
        {
            get { return "("; }
        }
        public String SEPARATOR_RIGHT
        {
            get { return ")"; }
        }
    }
}
