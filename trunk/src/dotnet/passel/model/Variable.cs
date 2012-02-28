using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

namespace phyea.model
{
    /**
     * Non-finite variables
     */
    public class Variable
    {
       /**
         * Variable data types
         */
        public enum VarType { real, nnreal, posreal, nat, nnnat, posnat, integer, index };

        /**
         * Variable update types: continuuos flow with time, while discrete are only updated by actions
         */
        public enum VarUpdateType { continuous, discrete };

        private String _name;
        private String _rate;
        private VarType _type;
        private VarUpdateType _update_type;

        /**
         * function declarations for uninterpreted function models
         */
        private FuncDecl _value;
        private FuncDecl _valuePrimed;
        private FuncDecl _valueRate;

        /**
         * todo: refactor to remove value and valueA, quick hack to add array theory
         */
        private Term _valueA;
        private Term _valuePrimedA;
        private Term _valueRateA;

        public Variable()
        {
        }

        public Variable(String name, String rate, VarType type)
        {
            this._name = name;
            this._rate = rate;
            this._type = type;
        }

        public override String ToString()
        {
            return this._name;
        }

        public String Name
        {
            get { return this._name; }
            set { this._name = value; }
        }

        public FuncDecl Value
        {
            get { return this._value; }
            set { this._value = value; }
        }

        public FuncDecl ValuePrimed
        {
            get { return this._valuePrimed; }
            set { this._valuePrimed = value; }
        }

        public FuncDecl ValueRate
        {
            get { return this._valueRate; }
            set { this._valueRate = value; }
        }

        public Term ValueA
        {
            get { return this._valueA; }
            set { this._valueA = value; }
        }

        public Term ValuePrimedA
        {
            get { return this._valuePrimedA; }
            set { this._valuePrimedA = value; }
        }

        public Term ValueRateA
        {
            get { return this._valueRateA; }
            set { this._valueRateA = value; }
        }

        public VarType Type
        {
            get { return this._type; }
            set { this._type = value; }
        }

        public VarUpdateType UpdateType
        {
            get { return this._update_type; }
            set { this._update_type = value; }
        }

    }
}
