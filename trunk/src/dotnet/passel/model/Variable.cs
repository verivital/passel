using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using passel.controller;

using Microsoft.Z3;

namespace passel.model
{
    /**
     * Non-finite variables
     */
    public class Variable
    {
       /**
         * Variable data types
         */
        public enum VarType { location, real, nnreal, posreal, nat, nnnat, posnat, integer, index, boolean };

        /**
         * Variable update types: continuuos flow with time, while discrete are only updated by actions; constants are never updated
         */
        public enum VarUpdateType { continuous, discrete, constant };

        private String _name;
        public String NamePrimed;
        private String _rate;
        private VarType _type;
        private VarUpdateType _update_type;

        public Sort TypeSort;

        /**
         * function declarations for uninterpreted function models
         */
        private FuncDecl _value;
        private FuncDecl _valuePrimed;
        private FuncDecl _valueRate;

        /**
         * todo: refactor to remove value and valueA, quick hack to add array theory
         */
        private ArrayExpr _valueA;
        private ArrayExpr _valuePrimedA;
        private ArrayExpr _valueRateA;

        public String InitialString;
        public Expr Initially;

        /**
         * 
         */
        public Variable(String name, String rate, VarType type, VarUpdateType update_type, String initial)
        {
            switch (type)
            {
                case VarType.boolean:
                    this.TypeSort = Controller.Instance.Z3.BoolSort;
                    break;
                case VarType.index:
                    this.TypeSort = Controller.Instance.Z3.IntSort;
                    break;
                case VarType.real:
                case VarType.nnreal:
                case VarType.posreal:
                    this.TypeSort = Controller.Instance.Z3.RealSort;
                    break;
                case VarType.integer:
                case VarType.nat:
                case VarType.nnnat:
                case VarType.posnat:
                    this.TypeSort = Controller.Instance.Z3.IntSort;
                    break;
                case VarType.location:
                    this.TypeSort = Controller.Instance.LocType;
                    break;
                default:
                    throw new Exception("Bad sort");
            }
            this._name = name;
            this.NamePrimed = name + controller.Controller.PRIME_SUFFIX;
            this._rate = rate;
            this._type = type;
            this.InitialString = initial;
            this.UpdateType = update_type;
        }

        /**
         * Finish instantiating class objects --- needs to be called after subclass constructors (and is called by them accordingly)
         */
        protected void finishConstruction()
        {
            if (this.InitialString != null)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = passel.controller.parsing.math.Expression.Parse(this.InitialString);
                //passel.controller.parsing.math.Expression.FixTypes(ref tmptree);
                this.Initially = passel.controller.parsing.math.ast.LogicalExpression.CreateTerm(tmptree);
            }
        }

        public override bool Equals(object obj)
        {
            Variable othervar = (Variable)obj;
            //return base.Equals(obj);
            return this.Name == othervar.Name && this.Type == othervar.Type && this.UpdateType == othervar.UpdateType && this.Initially == othervar.Initially;
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

        public ArrayExpr ValueA
        {
            get { return this._valueA; }
            set { this._valueA = value; }
        }

        public ArrayExpr ValuePrimedA
        {
            get { return this._valuePrimedA; }
            set { this._valuePrimedA = value; }
        }

        public ArrayExpr ValueRateA
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
