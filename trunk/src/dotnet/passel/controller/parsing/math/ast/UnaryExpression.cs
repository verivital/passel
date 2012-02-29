using System;
using passel.controller.parsing.math;

namespace passel.controller.parsing.math.ast
{
	public class UnaryExpression : LogicalExpression
    {
		public UnaryExpression(UnaryExpressionType type, LogicalExpression expression)
		{
            this.type = type;
            this.expression = expression;
		}

		private LogicalExpression expression;
		public LogicalExpression Expression
		{
			get { return expression; }
			set { expression = value; }
		}

		private UnaryExpressionType type;
		public UnaryExpressionType Type
		{
			get { return type; }
			set { type = value; }
		}
	}

	public enum UnaryExpressionType
	{
		Not,
        Negate
	}
}
