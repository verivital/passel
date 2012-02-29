using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace passel.controller.smt
{
    public interface ISmtSymbols
    {
        String NEGATION
        {
            get;
        }
        String CONJUNCTION
        {
            get;
        }
        String DISJUNCTION
        {
            get;
        }
        String IMPLICATION
        {
            get;
        }
        String SEPARATOR_LEFT
        {
            get;
        }
        String SEPARATOR_RIGHT
        {
            get;
        }
    }
}
