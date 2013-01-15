using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;

using VixCOM;

/**
 * Source: http://tranxcoder.wordpress.com/2008/05/14/using-the-vixcom-library/
 */
namespace passel.controller
{
    class VixWrapper
    {
        VixCOM.IVixLib vixLib = null;

        ulong m_vixError;
        VixCOM.IHost m_hostHandle = null;
        VixCOM.IVM m_vmHandle = null;

        public ulong GetError()
        {
            return m_vixError;
        }

        public VixWrapper()
        {
            try
            {
                vixLib = new VixCOM.VixLibClass();
            }
            catch (COMException comExc)
            {
                System.Diagnostics.Trace.WriteLine(comExc.Message + "\n");
                throw;
            }
        }

        /// <summary>
        /// Creates a host handle
        /// </summary>
        /// <returns>true if succeeded, otherwise false</returns>
        public bool Connect(string hostName, string userName, string password)
        {
            int hostType = string.IsNullOrEmpty(hostName) ?
                VixCOM.Constants.VIX_SERVICEPROVIDER_VMWARE_WORKSTATION :
                VixCOM.Constants.VIX_SERVICEPROVIDER_VMWARE_SERVER;

            int vixVersion = VixCOM.Constants.VIX_API_VERSION;

            vixVersion = 1; // Bugfix: http://communities.vmware.com/message/649925#649925

            //VixCOM.IJob jobHandle = vixLib.Connect(vixVersion, hostType, hostName, 0, userName, password, 0, null,  null);

            // for use with player: http://www.vmware.com/pdf/vix180_player_technote.pdf
            VixCOM.IJob jobHandle = vixLib.Connect(VixCOM.Constants.VIX_API_VERSION, VixCOM.Constants.VIX_SERVICEPROVIDER_VMWARE_PLAYER, null, 0, null, null, VixCOM.Constants.VIX_INVALID_HANDLE, null, null);

            int[] propertyIds = new int[1] { VixCOM.Constants.VIX_PROPERTY_JOB_RESULT_HANDLE };
            object results = new object();

            m_vixError = jobHandle.Wait(propertyIds, ref results);

            if (m_vixError == VixCOM.Constants.VIX_OK)
            {
                object[] objectArray = (object[])results;
                m_hostHandle = (VixCOM.IHost)objectArray[0];
                return true;
            }
            return false;
        }

        /// <summary>
        /// Opens the virtual machine specified in vmxFilePath
        /// </summary>
        /// <param name=”vmxFilePath”>The virtual machine vmx file to open</param>
        /// <returns>true if succeeded, otherwise false</returns>
        public bool Open(string vmxFilePath)
        {
            IJob jobHandle = m_hostHandle.OpenVM(vmxFilePath, null);

            int[] propertyIds = new int[1] { VixCOM.Constants.VIX_PROPERTY_JOB_RESULT_HANDLE };
            object results = new object();

            m_vixError = jobHandle.Wait(propertyIds, ref results);

            if (m_vixError == VixCOM.Constants.VIX_OK)
            {
                object[] objectArray = (object[])results;
                m_vmHandle = (VixCOM.IVM)objectArray[0];
                return true;
            }
            return false;
        }

        /// <summary>
        /// Power on the virtual machine
        /// </summary>
        /// <returns>true if succeeded, otherwise false</returns>
        public bool PowerOn()
        {
            IJob jobHandle = m_vmHandle.PowerOn(VixCOM.Constants.VIX_VMPOWEROP_LAUNCH_GUI, null, null);
            m_vixError = jobHandle.WaitWithoutResults();

            if (m_vixError == VixCOM.Constants.VIX_OK)
            {
                //
                // Wait until guest is completely booted.
                //
                jobHandle = m_vmHandle.WaitForToolsInGuest(300, null);

                m_vixError = jobHandle.WaitWithoutResults();
            }

            return (m_vixError == VixCOM.Constants.VIX_OK);
        }

        /// <summary>
        /// Starts a snapshot of a virtual machine
        /// </summary>
        /// <param name=”snapshot_name”>The name of the snapshot to start</param>
        /// <returns>true if succeeded, otherwise false</returns>
        public bool RevertToLastSnapshot()
        {
            ISnapshot snapshot = null;
            m_vixError = m_vmHandle.GetRootSnapshot(0, out snapshot);

            if (m_vixError == VixCOM.Constants.VIX_OK)
            {
                IJob jobHandle = m_vmHandle.RevertToSnapshot(snapshot, 0, null, null);

                m_vixError = jobHandle.WaitWithoutResults();
            }

            return (m_vixError == VixCOM.Constants.VIX_OK);
        }

        /// <summary>
        /// Login to the virtual machine
        /// </summary>
        /// <returns>true if succeeded, otherwise false</returns>
        public bool LogIn(string username, string password)
        {
            IJob jobHandle = m_vmHandle.LoginInGuest(username, password, 0, null);
            m_vixError = jobHandle.WaitWithoutResults();

            return (m_vixError == VixCOM.Constants.VIX_OK);
        }

        /// <summary>
        /// Creates the directory in the Virtual Machine
        /// </summary>
        /// <param name=”pathName”></param>
        /// <returns></returns>
        public bool CreateDirectoryInVm(string pathName)
        {
            IJob jobHandle = m_vmHandle.CreateDirectoryInGuest(pathName, null, null);
            m_vixError = jobHandle.WaitWithoutResults();

            return (m_vixError == VixCOM.Constants.VIX_OK);
        }

        /// <summary>
        /// Copies a file from the host machine to the virtual machine
        /// </summary>
        /// <param name=”sourceFile”>The source file on the host machine</param>
        /// <param name=”destinationFile”>The destination on the VM</param>
        /// <returns>true if succeeded, otherwise false</returns>
        public bool CopyFileToVm(string sourceFile, string destinationFile)
        {
            //
            // Copy files from host to guest
            //
            IJob jobHandle = m_vmHandle.CopyFileFromHostToGuest(sourceFile, destinationFile,
                0, null, null);
            m_vixError = jobHandle.WaitWithoutResults();

            return (m_vixError == VixCOM.Constants.VIX_OK);
        }

        /// <summary>
        /// Copies a file from the virtual machine to the host machine
        /// </summary>
        /// <param name=”sourceFile”>The source file on the virtual machine</param>
        /// <param name=”destinationFile”>The destination on the host machine</param>
        /// <returns>true if succeeded, otherwise false</returns>
        public bool CopyFileFromVm(string sourceFile, string destinationFile)
        {
            //
            // Copy files from host to guest
            //
            IJob jobHandle = m_vmHandle.CopyFileFromGuestToHost(sourceFile, destinationFile,
                0, null, null);
            m_vixError = jobHandle.WaitWithoutResults();

            return (m_vixError == VixCOM.Constants.VIX_OK);
        }

        /// <summary>
        /// Runs a program on the virtual machine
        /// </summary>
        /// <param name=”exePath”>The path of the program on the virtual machine</param>
        /// <param name=”parameters”>The parameters to pass to the executable</param>
        /// <param name=”resultCode”>The result code returned from the program that ran on the VM</param>
        /// <returns>true if succeeded, otherwise false</returns>
        public bool RunProgram(string exePath, string parameters, out int resultCode)
        {
            resultCode = -1;

            IJob jobHandle = m_vmHandle.RunProgramInGuest(exePath, parameters, VixCOM.Constants.VIX_RUNPROGRAM_ACTIVATE_WINDOW, null, null); // clientData

            int[] propertyIds = new int[1] { VixCOM.Constants.VIX_PROPERTY_JOB_RESULT_GUEST_PROGRAM_EXIT_CODE };
            object results = new object();
            m_vixError = jobHandle.Wait(propertyIds, ref results);

            if (m_vixError == VixCOM.Constants.VIX_OK)
            {
                object[] objectArray = (object[])results;
                resultCode = (int)objectArray[0];
                return true;
            }

            return false;
        }

        /// <summary>
        /// Power off the virtual machine
        /// </summary>
        /// <returns>true if succeeded, otherwise false</returns>
        public bool PowerOff()
        {
            IJob jobHandle = m_vmHandle.PowerOff(VixCOM.Constants.VIX_VMPOWEROP_NORMAL, null);
            m_vixError = jobHandle.WaitWithoutResults();

            return (m_vixError == VixCOM.Constants.VIX_OK);
        }
    }
}