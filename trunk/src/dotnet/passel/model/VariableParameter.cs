using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

using passel.controller;
using passel.controller.parsing;
using passel.controller.parsing.math;
using passel.controller.parsing.math.ast;

namespace passel.model
{
    public class VariableParameter : Variable
    {
        public VariableParameter(string name, VarType type, VarUpdateType update_type, string assumption)
            : base(name, "", type, update_type, assumption)
        {
            Expr param = null;
            // TODO: refactor all these switches in the constructors into common variable parent class
            switch (type)
            {
                case VarType.index:
                    param = Controller.Instance.Z3.MkIntConst(name); // todo: vs Controller.Instance.IndexType
                    break;
                case VarType.integer:
                    param = Controller.Instance.Z3.MkIntConst(name);
                    break;
                case VarType.real:
                    param = Controller.Instance.Z3.MkRealConst(name);
                    break;
            }

            if (param != null)
            {
                if (!Controller.Instance.Params.ContainsKey(name))
                {
                    Controller.Instance.Params.Add(name, param);
                }
            }
            else
            {
                throw new System.Exception("Parameter term not created.");
            }


            if (assumption != null && assumption.Length > 0)
            {
                Antlr.Runtime.Tree.CommonTree tmptree = passel.controller.parsing.math.Expression.Parse(assumption);
                //Expression.FixTypes(ref tmptree);
                Expr passump = LogicalExpression.CreateTerm(tmptree);
                if (!Controller.Instance.ParamsAssumps.ContainsKey(name))
                {
                    Controller.Instance.ParamsAssumps.Add(name, passump);
                    Controller.Instance.Z3.Assumptions.Add((BoolExpr)passump);
                }
            }
        }

        
    }
}
