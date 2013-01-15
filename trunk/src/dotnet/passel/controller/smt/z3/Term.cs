using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Z3;

namespace passel.controller.smt.z3
{
    class Term : Microsoft.Z3.Expr
    {
        public static Microsoft.Z3.Expr operator +(ArithExpr t1, ArithExpr t2)
        {
            return Controller.Instance.Z3.MkAdd(new ArithExpr[] { t1, t2 });
        }

        public static Microsoft.Z3.Expr operator -(ArithExpr t1, ArithExpr t2)
        {
            return Controller.Instance.Z3.MkSub(new ArithExpr[] { t1, t2 });
        }

        public static Microsoft.Z3.Expr operator >=(ArithExpr t1, ArithExpr t2)
        {
            return Controller.Instance.Z3.MkGe(t1, t2);
        }

        public static Microsoft.Z3.Expr operator <=(ArithExpr t1, ArithExpr t2)
        {
            return Controller.Instance.Z3.MkLe(t1, t2);
        }

        public static Microsoft.Z3.Expr operator >(ArithExpr t1, ArithExpr t2)
        {
            return Controller.Instance.Z3.MkGt(t1, t2);
        }

        public static Microsoft.Z3.Expr operator <(ArithExpr t1, ArithExpr t2)
        {
            return Controller.Instance.Z3.MkLt(t1, t2);
        }


    }
}
