using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;

namespace passel.model
{
    public class VariableGlobal : Variable
    {
        public VariableGlobal(string name, string rate, VarType type, VarUpdateType update_type, string initial)
            : base(name, rate, type, update_type, initial)
        {

            Expr globalVariable = null;
            Expr globalVariablePrime = null;
            //switch ((ParameterTypes)Enum.Parse(typeof(ParameterTypes), type, true))
            // todo: next blockcan likely be converted (for the most part) into a function call instead of switch (e.g., lots of repition)
            switch (type)
            {
                case Variable.VarType.boolean:
                    globalVariable = Controller.Instance.Z3.MkBoolConst(name);
                    this.Type = Variable.VarType.boolean;
                    globalVariablePrime = Controller.Instance.Z3.MkBoolConst(name + Controller.PRIME_SUFFIX);
                    break;
                case Variable.VarType.index:
                    globalVariable = Controller.Instance.Z3.MkIntConst(name); // todo: vs Controller.Instance.IndexType
                    this.Type = Variable.VarType.index;
                    globalVariablePrime = Controller.Instance.Z3.MkIntConst(name + Controller.PRIME_SUFFIX); // todo: vs Controller.Instance.IndexType
                    break;
                case Variable.VarType.integer:
                    globalVariable = Controller.Instance.Z3.MkIntConst(name);
                    this.Type = Variable.VarType.integer;
                    globalVariablePrime = Controller.Instance.Z3.MkIntConst(name + Controller.PRIME_SUFFIX);
                    break;
                case Variable.VarType.real:
                    globalVariable = Controller.Instance.Z3.MkRealConst(name);
                    this.Type = Variable.VarType.real;
                    globalVariablePrime = Controller.Instance.Z3.MkRealConst(name + Controller.PRIME_SUFFIX);
                    break;
                case Variable.VarType.nnreal:
                    globalVariable = Controller.Instance.Z3.MkRealConst(name);
                    this.Type = Variable.VarType.nnreal;
                    globalVariablePrime = Controller.Instance.Z3.MkRealConst(name + Controller.PRIME_SUFFIX);
                    break;
            }

            if (globalVariable != null && globalVariablePrime != null)
            {
                if (!Controller.Instance.GlobalVariables.ContainsKey(name))
                {
                    Controller.Instance.Sys.Variables.Add(this);
                    Controller.Instance.GlobalVariables.Add(name, globalVariable);
                    Controller.Instance.GlobalVariablesPrimed.Add(name, globalVariablePrime);
                }
            }
            else
            {
                throw new System.Exception("Parameter term not created.");
            }



            this.finishConstruction();
        }
    }
}
