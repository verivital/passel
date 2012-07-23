using System;
using System.Collections;
using System.Collections.Generic;
using System.Text;

using Antlr.Runtime.Tree;

using Microsoft.Z3;

using passel.controller;
using passel.controller.parsing.math;
using passel.model;

namespace passel.controller.parsing.math.ast
{
    public abstract class LogicalExpression
    {
        private static Context z3 = Controller.Instance.Z3;

        /**
         * Convert an untype AST to a tree of Microsoft Z3 terms
         */
        public static Microsoft.Z3.Expr CreateTerm(CommonTree ast)
        {
            if (ast == null)
            {
                throw new ArgumentNullException("No abstract syntax tree specified.");
            }

            switch (ast.Type)
            {
                // common functions to add:
                //z3.MkRem
                //z3.MkUnaryMinus
                //z3.MkDistinct

                case guardLexer.VARIABLE:
                    // todo: look up variable in an existing table instead of this (to get appropriate type, and to ensure proper scope)

                    // todo: continue searching other variable locations
                    if (Controller.Instance.Params.ContainsKey(ast.GetChild(0).Text))
                    {
                        return Controller.Instance.Params[ast.GetChild(0).Text];
                    }
                    else if (Controller.Instance.GlobalVariables.ContainsKey(ast.GetChild(0).Text))
                    {
                        return Controller.Instance.GlobalVariables[ast.GetChild(0).Text];
                    }
                    else if (Controller.Instance.Locations.ContainsKey(ast.GetChild(0).Text))
                    {
                        // search through all location names to see if this variable is actually a location label (makes things nice and readable)
                        return Controller.Instance.Locations[ast.GetChild(0).Text];
                    }
                    else if (Controller.Instance.Indices.ContainsKey(ast.GetChild(0).Text))
                    {
                        return Controller.Instance.Indices[ast.GetChild(0).Text];
                    }
                    else
                    {
                        //return z3.MkConst(ast.GetChild(0).Text, z3.MkRealSort());
                        throw new Exception("Parsing error: undefined variable: " + ast.GetChild(0).Text + ".");
                    }

                case guardLexer.QUANTIFIER_EXISTS:
                    {
                        // pull out list of bound variables
                        List<Expr> bound = new List<Expr>();

                        int i = 0;
                        List<Expr> indexConstraints = new List<Expr>();
                        while (ast.GetChild(i).Type == guardLexer.VARIABLE)
                        {
                            String name = ast.GetChild(i).GetChild(0).Text;
                            Expr t;
                            if (Controller.Instance.Indices.ContainsKey(name))
                            {
                                t = Controller.Instance.Indices[name];
                            }
                            else
                            {
                                t = z3.MkIntConst(name); // todo: vs Controller.Instance.IndexType
                                Controller.Instance.Indices.Add(name, t);
                            }

                            if (Controller.Instance.IndexOption == Controller.IndexOptionType.naturalOneToN)
                            {
                                // enforce index constraints
                                indexConstraints.Add(z3.MkGe((ArithExpr)t, (ArithExpr)Controller.Instance.IndexOne));
                                indexConstraints.Add(z3.MkLe((ArithExpr)t, (ArithExpr)Controller.Instance.Params["N"]));
                            }
                            bound.Add(t);
                            i++;
                        }

                        switch (Controller.Instance.IndexOption)
                        {
                            case Controller.IndexOptionType.enumeration:
                                switch (Controller.Instance.ExistsOption)
                                {
                                    case Controller.ExistsOptionType.and:
                                        if (bound.Count > 1)
                                        {
                                            return z3.MkExists(bound.ToArray(), z3.MkAnd((BoolExpr)z3.MkDistinct(bound.ToArray()), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(i))));
                                        }
                                        else
                                        {
                                            return z3.MkExists(bound.ToArray(), CreateTerm((CommonTree)ast.GetChild(i)));
                                        }
                                    case Controller.ExistsOptionType.implies:
                                    default:
                                        if (bound.Count > 1)
                                        {
                                            return z3.MkExists(bound.ToArray(), z3.MkImplies((BoolExpr)z3.MkDistinct(bound.ToArray()), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(i))));
                                        }
                                        else
                                        {
                                            return z3.MkExists(bound.ToArray(), CreateTerm((CommonTree)ast.GetChild(i)));
                                        }
                                }

                            case Controller.IndexOptionType.integer: // no constraint, use all integers
                                switch (Controller.Instance.ExistsOption)
                                {
                                    case Controller.ExistsOptionType.and:
                                        if (bound.Count > 1)
                                        {
                                            return z3.MkExists(bound.ToArray(), z3.MkAnd((BoolExpr)z3.MkDistinct(bound.ToArray()), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(i))));
                                        }
                                        else
                                        {
                                            return z3.MkExists(bound.ToArray(), CreateTerm((CommonTree)ast.GetChild(i)));
                                        }
                                    case Controller.ExistsOptionType.implies:
                                    default:
                                        if (bound.Count > 1)
                                        {
                                            return z3.MkExists(bound.ToArray(), z3.MkImplies((BoolExpr)z3.MkDistinct(bound.ToArray()), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(i))));
                                        }
                                        else
                                        {
                                            return z3.MkExists(bound.ToArray(), CreateTerm((CommonTree)ast.GetChild(i)));
                                        }
                                }

                            case Controller.IndexOptionType.naturalOneToN:
                            default:
                                switch (Controller.Instance.ExistsOption)
                                {
                                    case Controller.ExistsOptionType.and:
                                        if (bound.Count > 1)
                                        {
                                            indexConstraints.Add(z3.MkDistinct(bound.ToArray()));
                                            indexConstraints.Add(CreateTerm((CommonTree)ast.GetChild(i))); // recursion
                                            return z3.MkExists(bound.ToArray(), z3.MkAnd((BoolExpr[])indexConstraints.ToArray()));
                                        }
                                        else
                                        {
                                            indexConstraints.Add(CreateTerm((CommonTree)ast.GetChild(i))); // recursion
                                            return z3.MkExists(bound.ToArray(), z3.MkAnd((BoolExpr[])indexConstraints.ToArray()));
                                        }
                                    case Controller.ExistsOptionType.implies:
                                    default:
                                        if (bound.Count > 1)
                                        {
                                            indexConstraints.Add(z3.MkDistinct(bound.ToArray()));
                                            return z3.MkExists(bound.ToArray(), z3.MkImplies((BoolExpr)z3.MkAnd((BoolExpr[])indexConstraints.ToArray()), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(i))));
                                        }
                                        else
                                        {
                                            return z3.MkExists(bound.ToArray(), z3.MkImplies((BoolExpr)z3.MkAnd((BoolExpr[])indexConstraints.ToArray()), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(i))));
                                        }
                                }
                                //return z3.MkExists(0, bound.ToArray(), null, z3.MkAnd(z3.MkAnd(indexConstraints.ToArray()), CreateTerm((CommonTree)ast.GetChild(i))));
                        }
                    }


                case guardLexer.QUANTIFIER_FORALL:
                    {
                        // pull out list of bound variables
                        List<Expr> bound = new List<Expr>();

                        int i = 0;
                        List<BoolExpr> indexConstraints = new List<BoolExpr>();
                        while (ast.GetChild(i).Type == guardLexer.VARIABLE)
                        {
                            String name = ast.GetChild(i).GetChild(0).Text;
                            Expr t;
                            if (Controller.Instance.Indices.ContainsKey(name))
                            {
                                t = Controller.Instance.Indices[name];
                            }
                            else
                            {
                                t = z3.MkIntConst(name); // todo: vs Controller.Instance.IndexType
                                Controller.Instance.Indices.Add(name, t);
                            }

                            if (Controller.Instance.IndexOption == Controller.IndexOptionType.naturalOneToN)
                            {
                                // enforce index constraints
                                indexConstraints.Add(z3.MkGe((ArithExpr)t, (ArithExpr)Controller.Instance.IndexOne));
                                indexConstraints.Add(z3.MkLe((ArithExpr)t, (ArithExpr)Controller.Instance.Params["N"]));
                            }

                            bound.Add(t);
                            i++;
                        }

                        switch (Controller.Instance.IndexOption)
                        {
                            case Controller.IndexOptionType.enumeration:
                                if (bound.Count > 1)
                                {
                                    return z3.MkForall(bound.ToArray(), z3.MkImplies((BoolExpr)z3.MkDistinct(bound.ToArray()), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(i))));
                                }
                                else
                                {
                                    return z3.MkForall(bound.ToArray(), CreateTerm((CommonTree)ast.GetChild(i)));
                                }
                            case Controller.IndexOptionType.integer:
                                if (bound.Count > 1)
                                {
                                    return z3.MkForall(bound.ToArray(), CreateTerm((CommonTree)ast.GetChild(i)));
                                    //return z3.MkForall(bound.ToArray(), z3.MkImplies(z3.MkAnd(indexConstraints.ToArray()), CreateTerm((CommonTree)ast.GetChild(i))));
                                }
                                else
                                {
                                    return z3.MkForall(bound.ToArray(), CreateTerm((CommonTree)ast.GetChild(i)));
                                }
                            case Controller.IndexOptionType.naturalOneToN: // pass through
                            default:
                                if (bound.Count > 1)
                                {
                                    // no distinct
                                    return z3.MkForall(bound.ToArray(), z3.MkImplies(z3.MkAnd(indexConstraints.ToArray()), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(i))));

                                    // with distinct
                                    /*
                                    List<BoolExpr> andList = new List<BoolExpr>();
                                    andList.AddRange(indexConstraints.ToArray());
                                    andList.Add(z3.MkDistinct(bound.ToArray()));

                                    return z3.MkForall(bound.ToArray(), z3.MkImplies(z3.MkAnd(andList.ToArray()), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(i))));
                                     */
                                }
                                else
                                {
                                    return z3.MkForall(bound.ToArray(), z3.MkImplies(z3.MkAnd(indexConstraints.ToArray()), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(i))));
                                }
                                
                        }
                    }


                case guardLexer.INDEXED_VARIABLE:
                    // todo: find appropriate function for application and apply the index variable to it
                    if (Controller.Instance.IndexedVariables.ContainsKey(new KeyValuePair<String, String>(ast.GetChild(0).Text, ast.GetChild(1).Text)))
                    {
                        return Controller.Instance.IndexedVariables[new KeyValuePair<String, String>(ast.GetChild(0).Text, ast.GetChild(1).Text)];
                    }
                    else if (ast.GetChild(0).Text.Equals("q") && ast.GetChild(1).Type != guardLexer.INDEXED_VARIABLE)
                    {
                        if (!Controller.Instance.Q.ContainsKey(ast.GetChild(1).Text))
                        {
                            // global variable index, e.g., q[ last ] where last is an id
                            if (ast.GetChild(1).Type == guardLexer.ID)
                            {
                                return z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl["q"], CreateTerm((CommonTree)ast.GetChild(1)));
                            }
                            // create the index if it hasn't been used before
                            else if (!Controller.Instance.Indices.ContainsKey(ast.GetChild(1).Text))
                            {
                                //Controller.Instance.Indices.Add(ast.GetChild(1).Text, z3.MkConst(ast.GetChild(1).Text, Controller.Instance.IndexType)); // create the index
                                // TODO: switch based on index type: want integers to be interpreted if we are not using an enumerated index set (i.e., make as integer if possible, else make as uninterpreted)
                                Controller.Instance.Indices.Add(ast.GetChild(1).Text, z3.MkInt(ast.GetChild(1).Text)); // create the index
                            }

                            switch (Controller.Instance.DataOption)
                            {
                                case Controller.DataOptionType.array:
                                    {
                                        if (!Controller.Instance.Q.ContainsKey(ast.GetChild(1).Text))
                                        {
                                            // todo next: probably don't want this as a store, may need to create this as a store, select, etc., then depending upon usage, pick the correct one, i.e., have several lists Q and QPrimed, such as QStore, QSelect, etc.
                                            Controller.Instance.Q.Add(ast.GetChild(1).Text, z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[ast.GetChild(0).Text], Controller.Instance.Indices[ast.GetChild(1).Text])); // create the indexed variable (i.e., function application with the just created index)
                                            Controller.Instance.QPrimed.Add(ast.GetChild(1).Text, z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[ast.GetChild(0).Text], Controller.Instance.Indices[ast.GetChild(1).Text]));
                                        }
                                        break;
                                    }
                                case Controller.DataOptionType.uninterpreted_function:
                                default:
                                    {
                                        if (!Controller.Instance.Q.ContainsKey(ast.GetChild(1).Text))
                                        {
                                            Controller.Instance.Q.Add(ast.GetChild(1).Text, z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[ast.GetChild(0).Text], Controller.Instance.Indices[ast.GetChild(1).Text])); // create the indexed variable (i.e., function application with the just created index)
                                            Controller.Instance.QPrimed.Add(ast.GetChild(1).Text, z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[ast.GetChild(0).Text], Controller.Instance.Indices[ast.GetChild(1).Text]));
                                        }
                                        break;
                                    }
                            }
                        }
                        return Controller.Instance.Q[ast.GetChild(1).Text];
                    }
                    // nested index pointer variable (e.g., q[ p[i] ]
                    else if (ast.GetChild(1).Type == guardLexer.INDEXED_VARIABLE)
                    {
                        // very nasty, generalize later
                        switch (Controller.Instance.DataOption)
                        {
                            case Controller.DataOptionType.array:
                                {
                                    return z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[ast.GetChild(0).Text], getIndexedVariable(ast.GetChild(1).GetChild(0).Text, ast.GetChild(1).GetChild(1).Text));
                                }
                            case Controller.DataOptionType.uninterpreted_function:
                            default:
                                {
                                    return z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[ast.GetChild(0).Text], getIndexedVariable(ast.GetChild(1).GetChild(0).Text, ast.GetChild(1).GetChild(1).Text));
                                }
                        }
                    }
                    else
                    {
                        if (!Controller.Instance.Indices.ContainsKey(ast.GetChild(1).Text))
                        {
                            //Controller.Instance.Indices.Add(ast.GetChild(1).Text, z3.MkConst(ast.GetChild(1).Text, Controller.Instance.IndexType)); // create the index
                            Controller.Instance.Indices.Add(ast.GetChild(1).Text, z3.MkIntConst(ast.GetChild(1).Text)); // create the index
                        }
                        if (!Controller.Instance.IndexedVariables.ContainsKey(new KeyValuePair<string,string>(ast.GetChild(0).Text, ast.GetChild(1).Text)))
                        {
                            switch (Controller.Instance.DataOption)
                            {
                                case Controller.DataOptionType.array:
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<string, string>(ast.GetChild(0).Text, ast.GetChild(1).Text), z3.MkSelect(Controller.Instance.DataA.IndexedVariableDecl[ast.GetChild(0).Text], Controller.Instance.Indices[ast.GetChild(1).Text])); // create the indexed variable (i.e., function application with the just created index)
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<string, string>(ast.GetChild(0).Text, ast.GetChild(1).Text), z3.MkSelect(Controller.Instance.DataA.IndexedVariableDeclPrimed[ast.GetChild(0).Text], Controller.Instance.Indices[ast.GetChild(1).Text]));
                                        break;
                                    }
                                case Controller.DataOptionType.uninterpreted_function:
                                default:
                                    {
                                        Controller.Instance.IndexedVariables.Add(new KeyValuePair<string, string>(ast.GetChild(0).Text, ast.GetChild(1).Text), z3.MkApp(Controller.Instance.DataU.IndexedVariableDecl[ast.GetChild(0).Text], Controller.Instance.Indices[ast.GetChild(1).Text])); // create the indexed variable (i.e., function application with the just created index)
                                        Controller.Instance.IndexedVariablesPrimed.Add(new KeyValuePair<string, string>(ast.GetChild(0).Text, ast.GetChild(1).Text), z3.MkApp(Controller.Instance.DataU.IndexedVariableDeclPrimed[ast.GetChild(0).Text], Controller.Instance.Indices[ast.GetChild(1).Text]));
                                        break;
                                    }
                            }
                        }
                        return Controller.Instance.IndexedVariables[new KeyValuePair<String, String>(ast.GetChild(0).Text, ast.GetChild(1).Text)];
                        //throw new Exception("Problem parsing indexed variable declaration.");
                    }

                case guardLexer.RESET_VARIABLE:
                    //return z3.MkConst(CreateTerm((CommonTree)ast.GetChild(0)) + "'", z3.MkRealSort());
                    //return CreateTerm((CommonTree)ast.GetChild(0));
                    //todo next:
                    //return z3.MkConst(ast.GetChild(0).Text + '[' + ast.GetChild(1).Text + ']', z3.MkRealSort());

                    // todo next: grab primed variable from global dictionary: so create primed terms for all global variables

                    if (Controller.Instance.GlobalVariablesPrimed.ContainsKey(ast.GetChild(0).GetChild(0).Text))
                    {
                        return Controller.Instance.GlobalVariablesPrimed[ast.GetChild(0).GetChild(0).Text];
                    }
                    else
                    {
                        throw new Exception("Problem parsing global variable reset.");
                        //return z3.MkConst(ast.GetChild(0).GetChild(0).Text, Controller.Instance.IntType);
                    }

                case guardLexer.RESET_INDEXED_VARIABLE:
                    // todo: keep / remove the prime?
                    String varNamePrime = ast.GetChild(0).GetChild(0).Text + "'";
                    String index = ast.GetChild(0).GetChild(1).Text;
                    if (Controller.Instance.IndexedVariablesPrimed.ContainsKey(new KeyValuePair<String, String>(varNamePrime, index)))
                    {
                        return Controller.Instance.IndexedVariablesPrimed[new KeyValuePair<String, String>(varNamePrime, index)];
                    }
                    else if (ast.GetChild(0).GetChild(0).Text.Equals("q") && Controller.Instance.QPrimed.ContainsKey(index)) // todo: add a way to discuss different discrete locations
                    {
                        return Controller.Instance.QPrimed[index];
                    }
                    else
                    {
                        throw new Exception("Problem parsing reset of " + varNamePrime + ".");
                    }
                    

                case guardLexer.DYNAMICS_VARIABLE:
                    // todo: add the prime for derivative?
                    //return z3.MkConst(CreateTerm((CommonTree)ast.GetChild(0)) + "'", z3.MkRealSort());
                    return CreateTerm((CommonTree)ast.GetChild(0));

                case guardLexer.DYNAMICS_INDEXED_VARIABLE:

                    //direct return: return getIndexedVariable(ast.GetChild(0).GetChild(0).Text, ast.GetChild(0).GetChild(1).Text);

                    return getIndexedVariable(ast.GetChild(0).GetChild(0).Text, ast.GetChild(0).GetChild(1).Text);

                case guardLexer.INTEGER:
                    // todo: z3 gives an error if we use integers here... probably saying a real is related to an integer is problematic due to different sorts?
                    try
                    {
                        return z3.MkInt(ast.Text);
                    }
                    catch
                    {
                        return z3.MkReal(ast.Text);
                    }

                case guardLexer.BOOLEAN:
                    switch (Boolean.Parse(ast.Text))
                    {
                        case true:
                            {
                                return z3.MkTrue();
                            }
                        default:
                            {
                                return z3.MkFalse();
                            }
                    }

                case guardLexer.FLOAT:
                    return z3.MkReal((int)float.Parse(ast.Text)); // todo: check if this is okay

                case guardLexer.NOT:
                    return z3.MkNot((BoolExpr)CreateTerm((CommonTree)ast.GetChild(0)));

                case guardLexer.UNARY_MINUS:
                    return z3.MkUnaryMinus((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)));

                case guardLexer.TOREAL:
                    return z3.MkInt2Real((IntExpr)CreateTerm((CommonTree)ast.GetChild(0)));

                case guardLexer.TOINT:
                    return z3.MkReal2Int((RealExpr)CreateTerm((CommonTree)ast.GetChild(0)));

                case guardLexer.MULT:
                    try
                    {
                        return z3.MkMul((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), (ArithExpr)CreateTerm((CommonTree)ast.GetChild(1)));
                    }
                    catch
                    {
                        try
                        {
                            return z3.MkMul(z3.MkInt2Real((IntExpr)CreateTerm((CommonTree)ast.GetChild(0))), (ArithExpr)CreateTerm((CommonTree)ast.GetChild(1)));
                        }
                        catch
                        {
                            try
                            {
                                return z3.MkMul((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), z3.MkInt2Real((IntExpr)CreateTerm((CommonTree)ast.GetChild(1))));
                            }
                            catch
                            {
                                return z3.MkMul(z3.MkInt2Real((IntExpr)CreateTerm((CommonTree)ast.GetChild(0))), z3.MkInt2Real((IntExpr)CreateTerm((CommonTree)ast.GetChild(1))));
                            }
                        }
                    }

                case guardLexer.POW:
                    // todo: assume power raising to is an integer for now as z3 doesn't have exponentiation support
                    // this will be needed for representing nonlinear dynamics
                    //return z3.ex(CreateTerm((CommonTree)ast.GetChild(0)), CreateTerm((CommonTree)ast.GetChild(1)));
                    //return new BinaryExpresssion(BinaryExpressionType.Pow, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));
                    return z3.MkPower((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), (ArithExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.DIV:
                    return z3.MkDiv((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), (ArithExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.MOD:
                    return z3.MkMod((IntExpr)CreateTerm((CommonTree)ast.GetChild(0)), (IntExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.PLUS:
                    return z3.MkAdd((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), (ArithExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.MINUS:
                    return z3.MkSub((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), (ArithExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.LT:
                    return z3.MkLt((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), (ArithExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.LTEQ:
                    return z3.MkLe((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), (ArithExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.GT:
                    return z3.MkGt((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), (ArithExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.GTEQ:
                    try
                    {
                        return z3.MkGe((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), (ArithExpr)CreateTerm((CommonTree)ast.GetChild(1)));
                    }
                    catch
                    {
                        return z3.MkGe((ArithExpr)CreateTerm((CommonTree)ast.GetChild(0)), (ArithExpr)z3.MkInt2Real((IntExpr)CreateTerm((CommonTree)ast.GetChild(1))));
                    }

                case guardLexer.EQUALS:
                    try
                    {
                        return z3.MkEq(CreateTerm((CommonTree)ast.GetChild(0)), CreateTerm((CommonTree)ast.GetChild(1)));
                    }
                    catch
                    {
                        return z3.MkEq(CreateTerm((CommonTree)ast.GetChild(0)), z3.MkInt2Real((IntExpr)CreateTerm((CommonTree)ast.GetChild(1))));
                    }

                case guardLexer.NEQUALS:
                    return z3.MkNot(z3.MkEq(CreateTerm((CommonTree)ast.GetChild(0)), CreateTerm((CommonTree)ast.GetChild(1))));

                case guardLexer.AND:
                    return z3.MkAnd((BoolExpr)CreateTerm((CommonTree)ast.GetChild(0)), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.OR:
                    return z3.MkOr((BoolExpr)CreateTerm((CommonTree)ast.GetChild(0)), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.IMPLY:
                    return z3.MkImplies((BoolExpr)CreateTerm((CommonTree)ast.GetChild(0)), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(1)));
                    //return !CreateTerm((CommonTree)ast.GetChild(0)) | (CreateTerm((CommonTree)ast.GetChild(0)) & CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.IFF:
                    return z3.MkIff((BoolExpr)CreateTerm((CommonTree)ast.GetChild(0)), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.XOR:
                    return z3.MkXor((BoolExpr)CreateTerm((CommonTree)ast.GetChild(0)), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(1)));

                case guardLexer.ITE: // if then else
                    return z3.MkITE((BoolExpr)CreateTerm((CommonTree)ast.GetChild(0)), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(1)), (BoolExpr)CreateTerm((CommonTree)ast.GetChild(2)));

                case guardLexer.ID:
                    Expr[] expressions = new Expr[ast.ChildCount];

                    for (int i = 0; i < ast.ChildCount; i++)
                    {
                        expressions[i] = z3.MkInt2Real((IntExpr)CreateTerm((CommonTree)ast.GetChild(i)));
                    }

                    if (Controller.Instance.GlobalVariables.ContainsKey(ast.Text))
                    {
                        return Controller.Instance.GlobalVariables[ast.Text];
                    }
                    else // function delcaration like sin(x)
                    {
                        FuncDecl f;
                        if (Controller.Instance.Functions.ContainsKey(ast.Text))
                        {
                            f = Controller.Instance.Functions[ast.Text];
                        }
                        else
                        {
                            f = z3.MkFuncDecl(ast.Text, Controller.Instance.RealType, Controller.Instance.RealType);
                            Controller.Instance.Functions.Add(ast.Text, f); // TODO: add "function" declarations, like the variable declarations including domain/range types, like we do for globals and index variables
                        }

                        // TODO: double check: get a reference to the function, which we will assume has already been declared (e.g., sin(x) would locate a reference called sin in a table...?)
                        return z3.MkApp(f, expressions);
                    }

                default:
                    {
                        return z3.MkTrue(); // TODO: throw error, should be unreachable
                    }
            }
        }

        /**
         * Return a string list of all the variables in an expression 
         */
        public static List<String> findAllVars(CommonTree ast)
        {
            List<String> vars = new List<String>();
            if (ast != null)
            {
                switch (ast.Type)
                {
                    case guardLexer.VARIABLE:
                    case guardLexer.INDEXED_VARIABLE:
                        {
                            String name = ast.GetChild(0).Text;
                            vars.Add(name);
                            break;
                        }
                    default:
                        {
                            for (int i = 0; i < ast.ChildCount; i++)
                            {
                                List<String> toAdd = findAllVars((CommonTree)ast.GetChild(i));
                                foreach (var v in toAdd)
                                {
                                    if (!vars.Contains(v)) // unique only
                                    {
                                        vars.Add(v);
                                    }
                                }
                            }
                            return vars;
                        }
                }
            }
            return vars;
        }

        /**
         * Return a string list of all the variables in an expression 
         */
        public static List<String> findAllRealConstants(CommonTree ast)
        {
            List<String> vars = new List<String>();
            if (ast != null)
            {
                switch (ast.Type)
                {
                    //case guardLexer.INTEGER:
                    case guardLexer.FLOAT:
                        {
                            String name = ast.Text;
                            vars.Add(name);
                            break;
                        }
                    default:
                        {
                            for (int i = 0; i < ast.ChildCount; i++)
                            {
                                vars.AddRange(findAllRealConstants((CommonTree)ast.GetChild(i))); // not unique
                            }
                            return vars;
                        }
                }
            }
            return vars;
        }

        /**
         * Return a string list of all the continuous variables in an expression 
         */
        public static List<String> findContinuousVars(CommonTree ast)
        {
            List<String> vars = findAllVars(ast);

            for (int i = 0; i < vars.Count; i++)
            {
                switch (Controller.Instance.DataOption)
                {
                    case Controller.DataOptionType.array:
                        {
                            if (!Controller.Instance.DataA.IndexedVariableDecl.ContainsKey(vars[i]) && !Controller.Instance.DataA.VariableDecl.ContainsKey(vars[i]) && !Controller.Instance.GlobalVariables.ContainsKey(vars[i]))
                            {
                                vars.RemoveAt(i);
                                i--;
                            }
                            break;
                        }
                    case Controller.DataOptionType.uninterpreted_function:
                    default:
                        {
                            if (!Controller.Instance.DataU.IndexedVariableDecl.ContainsKey(vars[i]) && !Controller.Instance.DataU.VariableDecl.ContainsKey(vars[i]) && !Controller.Instance.GlobalVariables.ContainsKey(vars[i]))
                            {
                                vars.RemoveAt(i);
                                i--;
                            }
                            break;
                        }
                }
            }
            return vars;
        }

        /**
         * Return a string list of all the parameters in an expression 
         */
        public static List<String> findParams(CommonTree ast)
        {
            List<String> vars = findAllVars(ast);

            for (int i = 0; i < vars.Count; i++)
            {
                if (!Controller.Instance.Params.ContainsKey(vars[i]))
                {
                    vars.RemoveAt(i);
                    i--;
                }
            }
            return vars;
        }

        /**
         * Return a (typed) tree given an (untyped) abstract syntax tree
         */
        public static LogicalExpression Create(CommonTree ast)
        {
            if (ast == null)
            {
                throw new ArgumentNullException("No abstract syntax tree specified.");
            }

            switch (ast.Type)
            {
                case guardLexer.VARIABLE:
                    return new Value(ast.Text, ValueType.Variable);

                case guardLexer.INTEGER:
                    return new Value(ast.Text, ValueType.Integer);

                case guardLexer.BOOLEAN:
                    return new Value(ast.Text, ValueType.Boolean);

                case guardLexer.FLOAT:
                    return new Value(ast.Text, ValueType.Float);

                case guardLexer.NOT:
                    return new UnaryExpression(UnaryExpressionType.Not, Create((CommonTree)ast.GetChild(0)));

                case guardLexer.UNARY_MINUS:
                    return new UnaryExpression(UnaryExpressionType.Negate, Create((CommonTree)ast.GetChild(0)));

                case guardLexer.MULT:
                    return new BinaryExpresssion(BinaryExpressionType.Times, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.POW:
                    return new BinaryExpresssion(BinaryExpressionType.Pow, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.DIV:
                    return new BinaryExpresssion(BinaryExpressionType.Div, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.MOD:
                    return new BinaryExpresssion(BinaryExpressionType.Modulo, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.PLUS:
                    return new BinaryExpresssion(BinaryExpressionType.Plus, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.MINUS:
                    return new BinaryExpresssion(BinaryExpressionType.Minus, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.LT:
                    return new BinaryExpresssion(BinaryExpressionType.Lesser, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.LTEQ:
                    return new BinaryExpresssion(BinaryExpressionType.LesserOrEqual, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.GT:
                    return new BinaryExpresssion(BinaryExpressionType.Greater, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.GTEQ:
                    return new BinaryExpresssion(BinaryExpressionType.GreaterOrEqual, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.EQUALS:
                    return new BinaryExpresssion(BinaryExpressionType.Equal, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.NEQUALS:
                    return new BinaryExpresssion(BinaryExpressionType.NotEqual, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.AND:
                    return new BinaryExpresssion(BinaryExpressionType.And, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.OR:
                    return new BinaryExpresssion(BinaryExpressionType.Or, Create((CommonTree)ast.GetChild(0)), Create((CommonTree)ast.GetChild(1)));

                case guardLexer.ID:
                    LogicalExpression[] expressions = new LogicalExpression[ast.ChildCount];

                    for (int i = 0; i < ast.ChildCount; i++)
                    {
                        expressions[i] = LogicalExpression.Create((CommonTree)ast.GetChild(i));
                    }

                    return new Function(ast.Text, expressions);

                default:
                    return null;
            }
        }

        private static Expr getIndexedVariable(String varname, String index)
        {
            // todo: find appropriate function for application and apply the index variable to it
            if (Controller.Instance.IndexedVariables.ContainsKey(new KeyValuePair<String, String>(varname, index)))
            {
                return Controller.Instance.IndexedVariables[new KeyValuePair<String, String>(varname, index)];
            }
            else if (varname.Equals("q") && Controller.Instance.Q.ContainsKey(index))
            {
                return Controller.Instance.Q[index];
            }
            return null;
        }

        public virtual void Accept(LogicalExpressionVisitor visitor)
        {
            visitor.Visit(this);
        }
    }
}
