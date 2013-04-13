using System;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Microsoft.Z3;
using passel.controller.parsing.math.ast;
using System.Xml;
using System.IO;
using passel.controller;
using passel.controller.parsing;
using passel.model;

namespace passel_test
{
    [TestClass]
    public class ParseTest
    {
        [ClassInitialize()]
        public static void InitializePassel(TestContext testContext)
        {
            // query Controller.Instance to initialize it
            if (Controller.Instance == null)
            {
                throw new NullReferenceException("Controller not initialized.");
            }
        }



        [TestMethod]
        public void TestParseODE_Timed()
        {
            /*
            String ast = null; // TODO: Initialize to an appropriate value
            bool treeHasRealVars = false; // TODO: Initialize to an appropriate value
            Expr expected = null; // TODO: Initialize to an appropriate value
            Expr actual;
            actual = LogicalExpression.CreateTerm(ast, treeHasRealVars);
            Assert.AreEqual(expected, actual);
            Assert.Inconclusive("Verify the correctness of this test method.");
             */
        }

        [TestMethod]
        public void TestParseVariable_Parameter()
        {
            StringReader tr = new StringReader("<parameter name='N' type='index' comment='number of processes in the system' />");
            XmlTextReader reader = new XmlTextReader(tr);
            reader.Read(); // read into block
            Variable actual = ParseHyXML.ParseVariableParameter(reader);
            Variable expected = new VariableParameter("N", Variable.VarType.index, Variable.VarUpdateType.constant, "");
            Assert.AreEqual(expected, actual);

            tr = new StringReader("<parameter name='abcd' type='real' comment='' />");
            reader = new XmlTextReader(tr);
            reader.Read(); // read into block
            actual = ParseHyXML.ParseVariableParameter(reader);
            expected = new VariableParameter("abcd", Variable.VarType.real, Variable.VarUpdateType.constant, "");
            Assert.AreEqual(expected, actual);

            tr = new StringReader("<parameter name='r1234' type='integer' comment='' />");
            reader = new XmlTextReader(tr);
            reader.Read(); // read into block
            actual = ParseHyXML.ParseVariableParameter(reader);
            expected = new VariableParameter("r1234", Variable.VarType.integer, Variable.VarUpdateType.constant, "");
            Assert.AreEqual(expected, actual);
        }
    }
}
