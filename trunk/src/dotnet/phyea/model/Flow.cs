using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using phyea.controller;

namespace phyea.model
{
    /**
     * 
     */
    public class Flow
    {
        public DynamicsTypes DynamicsType;

        public enum DynamicsTypes
        {
            timed,
            rectangular,
            linear,
            affine,
            nonlinear
        }

        private Term[] _values;

        public Term Value;

        public Flow()
        {
        }

        public Flow(DynamicsTypes t, Term flow)
        {
            this.DynamicsType = t;
            this.Value = flow;
        }

    }
}
