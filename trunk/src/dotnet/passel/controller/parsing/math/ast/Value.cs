using System;
using passel.controller.parsing.math;

namespace passel.controller.parsing.math.ast
{
	public class Value : LogicalExpression
	{
        public Value(string text, ValueType type)
        {
            this.text = text;
            this.type = type;
        }

		private string text;
		
		public string Text
		{
			get { return text; }
			set { text = value; }
		}

        private ValueType type;

        public ValueType Type
		{
			get { return type; }
			set { type = value; }
		}
    }

	public enum ValueType
	{
		Integer,
		Float,
		Boolean,
        Variable,
        Bitvector
	}
}
