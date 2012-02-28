using phyea.controller.parsing.math;

namespace phyea.controller.parsing.math.ast
{
    public abstract class LogicalExpressionVisitor
    {
        public abstract void Visit(LogicalExpression expression);
        public abstract void Visit(BinaryExpresssion expression);
        public abstract void Visit(UnaryExpression expression);
	    public abstract void Visit(Value expression);
        public abstract void Visit(Function function);
    }
}
