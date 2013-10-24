using passel.model;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System;
using passel.controller;

namespace passel_test
{
    
    
    /// <summary>
    ///This is a test class for ReachSymmetricTest and is intended
    ///to contain all ReachSymmetricTest Unit Tests
    ///</summary>
    [TestClass()]
    public class ReachSymmetricTest
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
        ///A test for ReachSymmetric Constructor
        ///</summary>
        [TestMethod()]
        public void ReachSymmetricConstructorTest()
        {
            //ReachSymmetric target = new ReachSymmetric();
            Assert.Inconclusive("TODO: Implement code to verify target");
        }

        /// <summary>
        ///A test for ComputeReach
        ///</summary>
        [TestMethod()]
        public void ComputeReachTest()
        {
            //ReachSymmetric target = new ReachSymmetric(); // TODO: Initialize to an appropriate value
            Holism sys = null; // TODO: Initialize to an appropriate value
            uint N = 0; // TODO: Initialize to an appropriate value
            ReachSymmetric.ComputeReach(sys, N);
            Assert.Inconclusive("A method that does not return a value cannot be verified.");
        }



    }
}
