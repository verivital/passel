using Microsoft.VisualStudio.TestTools.UnitTesting;
using System;
using Microsoft.Z3;
using passel.model;
using passel.controller;
using passel.controller.parsing;
using passel.controller.parsing.math;
using passel.controller.parsing.math.ast;
using System.Collections.Generic;
using System.IO;
using System.Xml;

namespace passel_test
{
    
    
    /// <summary>
    ///This is a test class for SymmetricStateTest and is intended
    ///to contain all SymmetricStateTest Unit Tests
    ///</summary>
    [TestClass()]
    public class SymmetricStateTest
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

        private TestContext testContextInstance;

        /// <summary>
        ///Gets or sets the test context which provides
        ///information about and functionality for the current test run.
        ///</summary>
        public TestContext TestContext
        {
            get
            {
                return testContextInstance;
            }
            set
            {
                testContextInstance = value;
            }
        }

        #region Additional test attributes
        // 
        //You can use the following additional attributes as you write your tests:
        //
        //Use ClassInitialize to run code before running the first test in the class
        //[ClassInitialize()]
        //public static void MyClassInitialize(TestContext testContext)
        //{
        //}
        //
        //Use ClassCleanup to run code after all tests in a class have run
        //[ClassCleanup()]
        //public static void MyClassCleanup()
        //{
        //}
        //
        //Use TestInitialize to run code before running each test
        //[TestInitialize()]
        //public void MyTestInitialize()
        //{
        //}
        //
        //Use TestCleanup to run code after each test has run
        //[TestCleanup()]
        //public void MyTestCleanup()
        //{
        //}
        //
        #endregion


        /// <summary>
        ///A test for SameTypes
        ///</summary>
        [TestMethod()]
        public void SameTypesTest()
        {
            uint N = 0; // TODO: Initialize to an appropriate value
            SymmetricType[] types = null; // TODO: Initialize to an appropriate value
            SymmetricState target = new SymmetricState(N, types); // TODO: Initialize to an appropriate value
            SymmetricState compare = null; // TODO: Initialize to an appropriate value
            bool expected = false; // TODO: Initialize to an appropriate value
            bool actual;
            actual = target.SameTypes(compare);
            Assert.AreEqual(expected, actual);
            Assert.Inconclusive("Verify the correctness of this test method.");
        }

        /// <summary>
        ///A test for CheckTypeSum
        ///</summary>
        [TestMethod()]
        public void CheckTypeSumTest()
        {
            uint N = 0; // TODO: Initialize to an appropriate value
            SymmetricType[] types = null; // TODO: Initialize to an appropriate value
            SymmetricState target = new SymmetricState(N, types); // TODO: Initialize to an appropriate value
            uint N1 = 0; // TODO: Initialize to an appropriate value
            bool expected = false; // TODO: Initialize to an appropriate value
            bool actual;
            actual = target.CheckTypeSum(N1);
            Assert.AreEqual(expected, actual);
            Assert.Inconclusive("Verify the correctness of this test method.");
        }

        /// <summary>
        ///A test for ToConcrete
        ///</summary>
        [TestMethod()]
        public void ToConcreteTest()
        {
            uint N;
            uint TN;
            N = 0;
            TN = 0;
            List<SymmetricType> types = new List<SymmetricType>();
            types.Add(new SymmetricType(TN, Controller.Instance.Z3.MkTrue()));
            SymmetricState target = new SymmetricState(N, types.ToArray());
            Expr expected = null;
            Expr actual;
            actual = target.ToConcrete();
            //Assert.AreEqual(expected, actual);

            N = 1;
            TN = 1;
            types = new List<SymmetricType>();


            Holism sys = new Holism();
            ConcreteHybridAutomaton h = new ConcreteHybridAutomaton(sys, "test");
            ConcreteLocation aloc;
            ConcreteLocation bloc;

            StringReader tr;
            XmlTextReader reader;

            tr = new StringReader("<holism><mode id='0' name='aloc' initial='True'></mode><mode id='0' name='bloc' initial='False'></mode></holism>");
            reader = new XmlTextReader(tr);
            reader.Read();
            reader.Read();
            aloc = ParseHyXML.ParseLocation(reader, h);
            reader.Read();
            ParseHyXML.ParseLocationEnd(reader, h, aloc);
            reader.Read();
            bloc = ParseHyXML.ParseLocation(reader, h);
            reader.Read();
            ParseHyXML.ParseLocationEnd(reader, h, bloc);

            expected = LogicalExpression.CreateTerm("q[1] == aloc");
            types.Add(new SymmetricType(TN, LogicalExpression.CreateTerm("q[i] == aloc")));
            target = new SymmetricState(N, types.ToArray());
            actual = target.ToConcrete();
            //expected = expected.Substitute(Controller.Instance.Indices["i"], Controller.Instance.Z3.MkInt(1));
            //Assert.AreEqual(expected, actual);
            Assert.IsTrue(Controller.Instance.Z3.ProveEqual(actual, expected));

            expected = LogicalExpression.CreateTerm("q[1] == aloc and q[2] == aloc");
            types = new List<SymmetricType>();
            types.Add(new SymmetricType(2, LogicalExpression.CreateTerm("q[i] == aloc")));
            target = new SymmetricState(2, types.ToArray());
            actual = target.ToConcrete();
            Assert.IsTrue(Controller.Instance.Z3.ProveEqual(actual, expected));

            expected = LogicalExpression.CreateTerm("q[1] == aloc and q[2] == aloc and q[3] == aloc");
            types = new List<SymmetricType>();
            types.Add(new SymmetricType(3, LogicalExpression.CreateTerm("q[i] == aloc")));
            target = new SymmetricState(3, types.ToArray());
            actual = target.ToConcrete();
            Assert.IsTrue(Controller.Instance.Z3.ProveEqual(actual, expected));


            //target.visit(0, 3);
            

            List<uint> ids = new List<uint>();
            ids.Add(1);
            ids.Add(2);
            ids.Add(3);
            ids.Add(4);

            var perms = SymHelp.Permutations(ids);

            //ids.Add(5);
            //ids.Add(6);
            /*
            IEnumerable<uint> t1 = SymmetricState.Combinations(ids, 1);
            String s = "";
            foreach (var v in t1)
            {
                s += v + ", ";
            }
            IEnumerable<uint> t2 = SymmetricState.Combinations(ids, 2);
            foreach (var v in t2)
            {
                s += v + ", ";
            }
            IEnumerable<uint> t3 = SymmetricState.Combinations(ids, 3);
            foreach (var v in t3)
            {
                s += v + ", ";
            }
            IEnumerable<uint> t4 = SymmetricState.Combinations(ids, 4);
            foreach (var v in t4)
            {
                s += v + ", ";
            }*/

            /*
            uint T1 = 2;
            uint T2 = 2;
            uint T3 = (uint)(ids.Count - (T1 + T2));
            var ids_t1 = SymHelp.Combinations(ids, (int)T1);
            //s = "";
            string s = "";
            foreach (var v in ids_t1)
            {
                List<uint> vt = new List<uint>(v);
                var ids_t2 = SymHelp.Combinations(ids.FindAll(id => !vt.Contains(id)), (int)T2);

             
                //foreach (var stmp in v)
                //{
              //      s += stmp;
              //  }
              //  s += ", ";

                foreach (var v2 in ids_t2)
                {
                    List<uint> vt2 = new List<uint>(v2);
                    var ids_t3 = SymHelp.Combinations(ids.FindAll(id => !vt.Contains(id) && !vt2.Contains(id)), (int)T3);

                    foreach (var v3 in ids_t3)
                    {
                        List<uint> idset = new List<uint>(v);
                        idset.AddRange(v2);
                        idset.AddRange(v3);

                        foreach (var stmp in idset)
                        {
                            s += stmp;
                        }
                        s += ", ";
                    }
                }
            }*/
            //IEnumerable<uint> combinations = ;


            expected = LogicalExpression.CreateTerm("(q[1] == aloc and q[2] == bloc) or (q[1] == bloc and q[2] == aloc)");
            types = new List<SymmetricType>();
            types.Add(new SymmetricType(1, LogicalExpression.CreateTerm("q[i] == aloc")));
            types.Add(new SymmetricType(1, LogicalExpression.CreateTerm("q[i] == bloc")));
            target = new SymmetricState(2, types.ToArray());
            actual = target.ToConcrete();
            Assert.IsTrue(Controller.Instance.Z3.ProveEqual(actual, expected));
        }

        /// <summary>
        ///A test for ToString
        ///</summary>
        [TestMethod()]
        public void ToStringTest()
        {
            uint N = 0; // TODO: Initialize to an appropriate value
            SymmetricType[] types = null; // TODO: Initialize to an appropriate value
            SymmetricState target = new SymmetricState(N, types); // TODO: Initialize to an appropriate value
            string expected = string.Empty; // TODO: Initialize to an appropriate value
            string actual;
            actual = target.ToString();
            Assert.AreEqual(expected, actual);
            Assert.Inconclusive("Verify the correctness of this test method.");
        }

        /// <summary>
        ///A test for SymmetricState Constructor
        ///</summary>
        [TestMethod()]
        public void SymmetricStateConstructorTest()
        {
            uint N = 0; // TODO: Initialize to an appropriate value
            SymmetricType[] types = null; // TODO: Initialize to an appropriate value
            SymmetricState target = new SymmetricState(N, types);
            Assert.Inconclusive("TODO: Implement code to verify target");
        }
    }
}
