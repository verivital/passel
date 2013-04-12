using System;
using System.Collections;
using System.Text;
using Antlr;
using Antlr.Runtime;
using Antlr.Runtime.Tree;

using passel.controller.parsing.math.ast;

namespace passel.controller.parsing.math
{
    public class Expression
    {
        protected string expression;

        public Expression(string expression)
        {
            if (expression == null || expression == String.Empty)
            {
                throw new ArgumentException("Expression can't be empty", "expression");
            }
            this.expression = expression;
        }

        /**
         * Parse a math expression string and return the corresponding AST
         */
        public static CommonTree Parse(string expression)
        {
            guardLexer lexer = new guardLexer(new ANTLRStringStream(expression));
            guardParser parser = new guardParser(new CommonTokenStream(lexer));

            try
            {
                AstParserRuleReturnScope<CommonTree, CommonToken> rule = parser.getExpression();
                if (parser.HasError)
                {
                    throw new Exception(parser.ErrorMessage + " " + parser.ErrorPosition);
                }
                return rule.Tree as CommonTree;
            }
            catch (NoViableAltException)
            {
                throw;
            }
            catch (Exception)
            {
                throw;
                //throw new EvaluationException(e.Message, e);
            }



        }


        public static CommonTree copyTree(CommonTree original, CommonTree modnode, int type)
        {
            if (original == modnode)
            {
                original.Token.Type = type;
            }
            CommonTree copy = new CommonTree(original.Token);
            copyTreeRecursive(copy, original, modnode, type);
            return copy;
        }

        /**
         * Recursively copy tree
         */
        private static void copyTreeRecursive(CommonTree copy, CommonTree original, CommonTree modnode, int type)
        {
            if (original.Children != null)
            {
                foreach (var o in original.Children)
                {
                    CommonTree originalChild = (CommonTree)o;

                    // get the token from the original child node
                    CommonToken oTok = (CommonToken)originalChild.Token;

                    // create a new token with the same type & text as 'oTok' 
                    //CommonToken cTok = new CommonToken(oTok.Type, oTok.Text);
                    CommonToken cTok;
                    if (o.Equals(modnode))
                    {
                        cTok = new CommonToken(type, oTok.Text);
                    }
                    else
                    {
                        cTok = new CommonToken(oTok.Type, oTok.Text);
                    }

                    // copy all attributes from 'oTok' to 'cTok'  
                    cTok.Line = oTok.Line;
                    cTok.CharPositionInLine = oTok.CharPositionInLine;
                    cTok.Channel = oTok.Channel;
                    cTok.StartIndex = oTok.StartIndex;
                    cTok.StopIndex = oTok.StopIndex;
                    cTok.TokenIndex = oTok.TokenIndex;

                    // create a new tree node with the 'cTok' as token
                    CommonTree copyChild = new CommonTree(cTok);

                    // set the parent node of the child node
                    copyChild.Parent = copy;

                    // add the child to the parent node
                    copy.AddChild(copyChild);

                    // make a recursive call to copy deeper
                    copyTreeRecursive(copyChild, originalChild, modnode, type);
                }
            }
        }



        /**
         * Fix constants in a given AST
         * Example: convert relations over real constants (listed as integers) and real variables to floats
         */
        public static void FixTypes(ref CommonTree ast)
        {
            if (ast != null)
            {
                switch (ast.Type)
                {
                    case guardLexer.FLOAT:
                        {
                            // get lowest parent with at least one other child
                            CommonTree p = (CommonTree)ast.Parent;
                            while (p.ChildCount < 2)
                            {
                                p = (CommonTree)p.Parent;
                            }
                            // get first child on other side of parent
                            int i = 0;
                            CommonTree otherC = (CommonTree)p.Children[i];
                            while (otherC == ast)
                            {
                                otherC = (CommonTree)p.Children[++i];
                            }
                            String var = otherC.Children[0].Text; // TODO: CASE CHECKS
                            if (Controller.Instance.GlobalVariables.ContainsKey(var) && Controller.Instance.GlobalVariables[var].Sort != Controller.Instance.RealType ||
                                Controller.Instance.UndefinedVariables.ContainsKey(var) && Controller.Instance.UndefinedVariables[var].Sort != Controller.Instance.RealType)
                                // TODO: ADD OTHER CASES
                            {
                                if (Controller.Instance.GlobalVariables.ContainsKey(var) && Controller.Instance.GlobalVariables[var].Sort != Controller.Instance.IntType)
                                { // bitvector / boolean
                                    ast = copyTree(ast, ast, guardLexer.BOOLEAN);
                                }
                                else
                                {

                                    //ast.Type = guardLexer.INTEGER; // no settor...simplest method actually apears to just do a (non-recursive) copy, where you CAN modify the type of the token, e.g., ast.Token.Type, which is rather annoying
                                    ast = copyTree(ast, ast, guardLexer.INTEGER);
                                }
                                // TODO: STRIP ALL DECIMAL POINTS???
                            }
                            break;
                        }
                    default:
                        {
                            for (int i = 0; i < ast.ChildCount; i++)
                            {
                                CommonTree tmp = (CommonTree)ast.Children[i];
                                FixTypes(ref tmp);
                                ast.SetChild(i, tmp);
                            }
                            break;
                        }
                }
            }
        }
    }
}
