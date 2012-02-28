using Antlr.Runtime;
using Antlr.Runtime.Tree;

namespace phyea.controller.parsing.math
{
    partial class guardParser
    {
        public AstParserRuleReturnScope<CommonTree, CommonToken> getExpression()
        {
            return this.expression();
        }
    }
}
