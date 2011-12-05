using System;
using System.Collections;
using System.Text;
using Antlr;
using Antlr.Runtime;
using Antlr.Runtime.Tree;

using phyea.controller.parsing.math.ast;

namespace phyea.controller.parsing.math
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
            catch (Exception)
            {
                throw;
                //throw new EvaluationException(e.Message, e);
            }
        }
    }
}
