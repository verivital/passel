using System;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace passel_test
{
    [TestClass]
    public class ParseTest
    {
        [TestMethod]
        public void TestParseODE_Timed()
        {
            CommonTree ast = null; // TODO: Initialize to an appropriate value
            bool treeHasRealVars = false; // TODO: Initialize to an appropriate value
            Expr expected = null; // TODO: Initialize to an appropriate value
            Expr actual;
            actual = LogicalExpression.CreateTerm(ast, treeHasRealVars);
            Assert.AreEqual(expected, actual);
            Assert.Inconclusive("Verify the correctness of this test method.");
        }
    }
}
