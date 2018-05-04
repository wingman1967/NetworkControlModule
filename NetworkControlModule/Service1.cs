using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Diagnostics;
using System.Linq;
using System.ServiceProcess;
using System.Text;
using System.Net;
using System.Net.Sockets;
using System.Timers;
using System.Threading;
using System.IO;
using System.Net.NetworkInformation;
using System.Data.SqlClient;
using System.Reflection;

namespace NetworkControlModule
{
    public partial class NCMService : ServiceBase
    {
        //Network Control Module (NCM) Service
        //Author:  John Hines, The Gorman-Rupp Co.
        //January 2013
        //Service monitors port 1433 for SQL server, primary host.  If the SQL host becomes unavailable, service engages failover redirection
        //so that any running SQL applications can continue to write records to database.  Once connectivity to the primary host
        //has been re-established, failover redirection is reversed and then any records that were written to the failover host are
        //copied to the primary host and then removed from the failover host.

        //Service communicates with companion applications via socket on port 3232 and accepts requests/commands on port 3230.
        //A Telnet server interface operates on port 3000 enabling a means of monitoring the service and current-state.

        //The hosts file manipulation performed by this service triggers a false-positive from Sophos.  Each time service is installed
        //or re-installed, it must be registered with Sophos.  Steps to do so are:
        //1.  Rename hosts to hosts_HOSTBACK
        //2.  COPY hosts_NCM to hosts
        //3.  Start the NCM service.  It will fail immediately twice.  Each time, access Sophos Quarantine and authorize.
        //4.  hosts should now be ok.  Delete hosts_HOSTBACK
                
        bool ssl = false;
        int maxWaitMillisec = 20000;
        int port = 1433;
        bool success;
        System.Timers.Timer timer1 = new System.Timers.Timer();
        string host;
        int noFinditerator;
        string primaryHost = "grcpslsql0"; 
        string failoverHost = "localhost"; //normally this would be localhost (test with grcdslsql0)
        string testprimaryHost = "grcbi";
        int successful;
        int failOverState = 1; //default to failover, to be cleared on the first successful primary connection
        const int servicePort = 3232; //the DAQ+ service port
        int socketConnectAttempts;
        string savehost = "";
        static int nuke = 0;
        Thread socketListenerThread = new System.Threading.Thread(new ThreadStart(incomingSocket));
        Thread TelnetListenerThread = new System.Threading.Thread(new ThreadStart(telnetServer));
        static string outMessage;
        const int NCMServicePort = 3230;
        const int TelnetPort = 3231;
        static TcpListener tcpPrimaryListener;
        static Thread listenThread;
        static DateTime uptimeStart;
        static DateTime uptimeNow;
        static int failoverCount = 0;
        static int daqUpdates = 0;
        static int telnetConnections = 0;
        static int fullOutages = 0;
        static int recoveries = 0;
        static int totalSocketReceive = 0;
        static int totalSocketTransmit = 0;
        static string lastTelnetIP;
        static string lastTelnetTime;
        static string currentState;
        static int RecoveryInProgress = 0;
        int firstTimeIn = 1;
        int primaryGood;
        int cycleRunning = 0;
        static int goodFailoverConnect = 0;
        bool TotalFailure = false;
        bool Processing = false;
               
        //Commands:  CONNECT, UPDATE, STATUS, TIME, QUIT

        public NCMService()
        {
            InitializeComponent();

            if (!System.Diagnostics.EventLog.SourceExists("NCMService"))
            {
                System.Diagnostics.EventLog.CreateEventSource(
                    "NCMService", "Application");
            }
            eventLog1.Source = "NCMService";
            eventLog1.Log = "Application";

        }

        protected override void OnStart(string[] args)
        {
            eventLog1.WriteEntry("NCM Service Starting");

            //Before starting any processing, reconcile the host file.  If hosts_HOSTBACK exists, a failover was in progress that wasn't
            //finished, possibly due to a crash or reboot of the system, as completion of a failover and start of a recovery causes that
            //file to be renamed to hosts (the original hosts file on the system).  hosts_NCM is always copied, NOT renamed to hosts.
            CheckHosts();

            //Start the thread for the incomingsocket listener:
            //Thread socketListenerThread = new System.Threading.Thread(new ThreadStart(incomingSocket));
            uptimeStart = System.DateTime.Now;
            
            socketListenerThread.Start();
            TelnetListenerThread.Start();
            
            timer1.Elapsed += new ElapsedEventHandler(timer1_Elapsed);
            //timer1.Interval = 30000;      //30-second poll of SQL server port
            timer1.Interval = 60000;        //one-minute interval poll of SQL server port
            timer1.Enabled = true;
            timer1.Start();
        }

        protected override void OnStop()
        {
            eventLog1.WriteEntry("NCM Service Shutting Down");

            //Instruct the TCP socket and socketlistener thread to shutdown:
            nuke = 1;
            socketListenerThread.Abort();
        }

        private void checkConnection()
        {
            if (Processing == true)
            {
                return;
            }
            else
            {
                Processing = true;
            }
            
            //check our primary host for connectivity on port 1433 (MS SQL Server) first:
            successful = 0;
            int foundone = 0;
            
            if (failOverState == 1)
                eventLog1.WriteEntry("Obtaining IP address for: " + primaryHost);

            checkPrimary();

            Socket s = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);
            //eventLog1.WriteEntry("Ping return");
            if (primaryGood == 1)
            {
                TotalFailure = false;
                IPAddress[] IPs = Dns.GetHostAddresses(primaryHost);
                //Check for any IP addresses registered for the host:
                foreach (IPAddress ip in IPs)
                {
                    if (failOverState == 1)
                        eventLog1.WriteEntry("Primary Host IP: " + Convert.ToString(ip));

                }
                
                //Socket s = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);

                //See if we have a valid IPv4 address from the host:
                foundone = 0; //indicates we have found a valid IPv4 address for the host.  This indicates DNS is at least functioning.

                foreach (IPAddress ip in IPs)
                {
                    if (ip.AddressFamily != AddressFamily.InterNetwork)
                        continue;

                    foundone = 1;

                    //Attempt connection to the IPv4 address:
                    try
                    {
                        s.Connect(ip, port);
                        successful = 1;
                        totalSocketTransmit += 1;

                        if (failOverState == 1) //This would still be 1 if we are recovering from a former failover state. If 0, no need to restate:
                        {
                            eventLog1.WriteEntry("Connected successfully to primary endpoint: " + primaryHost + " (" + Convert.ToString(ip) + ")");

                            //If failovercount is 0, we have really just started up and currentstate is primary/normal, else we are recovering:
                            if (failoverCount == 0)
                            {
                                currentState = "Primary (Normal)";
                                if (firstTimeIn == 1)
                                {
                                    FailoverRecovery();     //in case a previous recovery was interrupted or not carried out
                                    firstTimeIn = 0;
                                }
                            }
                            else
                            {
                                currentState = "Primary (Recovery)";
                                s.Shutdown(SocketShutdown.Both);
                                s.Close();      //close socket so we aren't holding it open for the next cycle
                                FailoverRecovery();
                                currentState = "Primary (Normal)";
                            }
                        }

                        try
                        {
                            s.Shutdown(SocketShutdown.Both);
                            s.Close();      //close socket so we aren't holding it open for the next cycle
                        }
                        catch
                        {
                            //fallthru
                        }
                                                
                        failOverState = 0;
                        host = primaryHost;
                        //currentState = "Primary (Normal)";

                        if (failoverCount > 0)
                        {
                            recoveries += 1;
                        }

                    }
                    catch
                    {
                        eventLog1.WriteEntry("Could not connect to primary endpoint: " + primaryHost + "(" + Convert.ToString(ip) + ")");
                    }

                }

                if (foundone == 0)
                    eventLog1.WriteEntry("No IPv4 address found for primary host: " + primaryHost);
            }
            else
            {
                //Since successful is still 0 and we have no response from the primary, we can just go on with checking the failover
            }
            
            if (successful == 0 || primaryGood != 1)
            {
                //Attempt a connection to the failover server:
                IPAddress[] failoverIPs = Dns.GetHostAddresses(failoverHost);
                failOverState = 1;

                foreach (IPAddress ip in failoverIPs)
                {
                    if (ip.AddressFamily != AddressFamily.InterNetwork)
                        continue;

                    foundone = 1;

                    //Attempt connection to the IPv4 address:
                    try
                    {
                        s.Connect(ip, port);
                        successful = 1;
                        TotalFailure = false;
                        totalSocketTransmit += 1;

                        //If the host has not changed, we have already logged this, do not re-state or take other action:
                        if (savehost != host)
                        {
                            eventLog1.WriteEntry("Connected successfully to failover endpoint: " + failoverHost + " (" + Convert.ToString(ip) + ")");
                            failoverCount += 1;
                            
                        }

                        engageFailoverRedirection();
                        host = failoverHost;
                        currentState = "FAILOVER";
                    }
                    catch
                    {
                        eventLog1.WriteEntry("Could not connect to failover endpoint");
                        TotalFailure = true;
                        
                        //Only increment outage if outages and recoveries are equal, as that indicates this is a new outage:
                        if (fullOutages == recoveries)
                        {
                            fullOutages += 1;
                        }
                                                
                        currentState = "OUTAGE";
                        Processing = false;                             //ahead of time
                        outMessage = "Connect:" + "nohost" + ":" + "1"; //indicate nohost due to total failure & failstate
                    }

                }

                s.Shutdown(SocketShutdown.Both);
                s.Close();      //close socket so we aren't holding it open over the next cycle

                if (foundone == 0)
                    eventLog1.WriteEntry("No IPv4 address found for failover host: " + failoverHost);
            }
            
            noFinditerator = 0;

            if (successful == 1)

                outMessage = "Connect:" + host + ":" + failOverState;

                if (savehost != host) //Only update the socket if the host has changed (occurs on a failover or recovery)
                {
                    //eventLog1.WriteEntry("Sending socket update");
                    updateSocket("connect", host, failOverState);
                    savehost = host;
                }
                
                //just to be safe, try closing the socket again here just in case we somehow missed it
                try
                {
                    s.Shutdown(SocketShutdown.Both);
                    s.Close();      //close socket so we aren't holding it open over the next cycle
                }
                catch
                {
                    //fallthru (we will hit this if the socket was already closed and trying to re-close throws an exception)
                }

            //if (TotalFailure == true && failOverState == 1)
            //{
            //    failOverState = 0;      //No failover since neither the primary nor the failover host is available;
            //    failoverstate is only otherwise cleared after a failover - recovery has been done
            //}

            //If we are NOT in a total failure and failoverstate is NOT 1, we are running on the primary.  This
            //check is required to override any erroneous current-state setting above:
            if (TotalFailure == false && failOverState != 1)
            {
                currentState = "Primary (Normal)";
            }

            //if we have a TotalFailure, force the state to indicate a 1 as the <outMessage> may not have updated
            if (TotalFailure == true)
            {
                outMessage = "Connect:" + host + ":" + "1";
            }

            cycleRunning = 0;
            Processing = false;
        }

        private void timer1_Elapsed(object sender, EventArgs e)
        {
            //poll servers to see which are still responding:
            
            //noFinditerator += 1;
            
            if (noFinditerator >= 2) //if we are 2 or higher, we are stuck on the dns search meaning this is an invalid host
            {
                eventLog1.WriteEntry("Unable to reach primary or failover endpoints");
                noFinditerator = 0; //reset for another cycle
            }
            else
            {
                if (cycleRunning == 0 || 1 == 1)      //only cycle anew if we are currently not already busy
                {
                    cycleRunning = 1;
                    
                    //eventLog1.WriteEntry("Cycle running");            //enable when debugging
                    checkConnection();
                    cycleRunning = 0;
                    
                    //eventLog1.WriteEntry("Cycle done");               //enable when debugging
                }
                
            }

        }

        private void updateSocket(string command, string host, int failOverIndicator)
        {
            if (socketConnectAttempts > 1)
            {
                eventLog1.WriteEntry("DAQ+ tcp server is not running");
                socketConnectAttempts = 0;
                return;
            }

            //socketConnectAttempts += 1;

            //send command to localhost socket, port 3232 consisting of:  command, the connection host, and failover status
            //commands:  connect, down, update
            TcpClient NCMtcpclient = new TcpClient();
            eventLog1.WriteEntry("Connecting to the DAQ+ service socket...");

            //Check the DAQ+ port to see if anything is listening.  If there is, connect; otherwise, flag server not running and return.
            
            trythis();

            if (goodFailoverConnect == 0)
            {
                eventLog1.WriteEntry("DAQ+ tcp server is not running");
                return;
            }
            eventLog1.WriteEntry("Attempting connection...");
            //Connect to the DAQ+ tcp socket server:
            NCMtcpclient.Connect("127.0.0.1", servicePort);
            eventLog1.WriteEntry("Connected to DAQ+ tcp socket");
            //setup NetworkStream object to send and/or receive some data
            NetworkStream ourStream = NCMtcpclient.GetStream();
            
            //Set up the command to be sent
            byte[] data = Encoding.ASCII.GetBytes(command + ":" + host + ":" + failOverIndicator);

            eventLog1.WriteEntry("Sending command to DAQ+");

            try
            {
                //Send connection command to DAQ+
                ourStream.Write(data, 0, data.Length);
                eventLog1.WriteEntry("Sent command to DAQ+ : " + command + ", " + host + ", " + failOverIndicator);
                //outMessage = command + ":" + host + ":" + failOverIndicator;
                socketConnectAttempts = 0;
                totalSocketTransmit += 1;
            }
            catch
            {
                eventLog1.WriteEntry("DAQ+ tcp server is not running");
                socketConnectAttempts = 0;
            }

        }

        static void incomingSocket()
        {
            string incomingCommand;
            
            // local IP address
            System.Net.IPAddress serverAddress = System.Net.IPAddress.Parse("127.0.0.1"); 

            System.Diagnostics.EventLog EventLog2 = new System.Diagnostics.EventLog();
            if (!System.Diagnostics.EventLog.SourceExists("NCMService"))
            {
                System.Diagnostics.EventLog.CreateEventSource(
                    "NCMService", "Application");
            }
            EventLog2.Source = "NCMService";
            EventLog2.Log = "Application";

            // Start listening for connections on our IP address + Our Port number 
            TcpListener listener = new TcpListener(serverAddress, NCMServicePort);
            listener.Start();

            EventLog2.WriteEntry("NCM Service-Port (3230) Listener started");

            while (nuke == 0)
            {
                // Continue this listening loop until nuke is set to a non-zero value

                // watch for incoming command
                TcpClient ourTCP_Client = listener.AcceptTcpClient();
                EventLog2.WriteEntry("Incoming message on port 3230");
                totalSocketReceive += 1;

                daqUpdates += 1;

                //Create buffer for network stream
                NetworkStream ourStream = ourTCP_Client.GetStream();
                byte[] data = new byte[ourTCP_Client.ReceiveBufferSize];

                // read the incoming data stream
                int bytesRead = ourStream.Read(data, 0, System.Convert.ToInt32(ourTCP_Client.ReceiveBufferSize));
                // echo the data we got to the console until the newline, and delay closing our window.
                incomingCommand = Encoding.ASCII.GetString(data, 0, bytesRead);

                EventLog2.WriteEntry(incomingCommand);
                
                TcpClient NCMtcpclient = new TcpClient();
                
                //Connect to the DAQ+ tcp socket server:
                NCMtcpclient.Connect("127.0.0.1", servicePort);
                EventLog2.WriteEntry("Connected to DAQ+. Ready to send response: " + outMessage);
                //setup NetworkStream object to send and/or receive some data
                NetworkStream ourStream2 = NCMtcpclient.GetStream();
                EventLog2.WriteEntry("Stream set up.  Sending response on port 3232 (DAQ+)...");
                if (incomingCommand == "UPDATE" || incomingCommand == "U")
                {
                    //Set up the command to be sent
                    byte[] data2 = Encoding.ASCII.GetBytes(outMessage);
                    ourStream2.Write(data2, 0, data2.Length);
                    totalSocketTransmit += 1;
                }
                
            }

            listener.Stop();
                                    
        }

        static void telnetServer()
        {
            //Telnet server interface running on port 3000

            string incomingMessage;
            string buildMessage = "";
            char ctrln = (char)0x0D;
            string outputMessage = "";
            Byte[] myBytes13 = { 13 };
            string myStr13 = System.Text.Encoding.ASCII.GetString(myBytes13);

            System.Diagnostics.EventLog EventLog3 = new System.Diagnostics.EventLog();
            if (!System.Diagnostics.EventLog.SourceExists("NCMService"))
            {
                System.Diagnostics.EventLog.CreateEventSource(
                    "NCMService", "Application");
            }
            EventLog3.Source = "NCMService";
            EventLog3.Log = "Application";
            
            tcpPrimaryListener = new TcpListener(IPAddress.Any, 3000);
            listenThread = new Thread(new ThreadStart(ListenForClients));
            listenThread.Start();

            EventLog3.WriteEntry("Telnet service-port (3000) listener started.");
                     
        }

        static void ListenForClients()
        {
            System.Diagnostics.EventLog EventLog5 = new System.Diagnostics.EventLog();
            if (!System.Diagnostics.EventLog.SourceExists("NCMService"))
            {
                System.Diagnostics.EventLog.CreateEventSource(
                    "NCMService", "Application");
            }
            EventLog5.Source = "NCMService";
            EventLog5.Log = "Application";
                        
            tcpPrimaryListener.Start();

            while (true)
            {
                //blocks until a client has connected to the server
                TcpClient client = tcpPrimaryListener.AcceptTcpClient();
                                
                EventLog5.WriteEntry("A Telnet client is connecting...");

                telnetConnections += 1;

                //create a thread to handle communication 
                //with connected client
                Thread clientThread = new Thread(new ParameterizedThreadStart(HandleClientComm));
                clientThread.Start(client);
            }
        }

        static void HandleClientComm(object client)
        {
            TcpClient tcpClient = (TcpClient)client;
            NetworkStream clientStream = tcpClient.GetStream();
            string incomingMessage = "";
            string outputMessage = "";
            string remoteClientIP = ((IPEndPoint)tcpClient.Client.RemoteEndPoint).Address.ToString();
            
            System.Diagnostics.EventLog EventLog4 = new System.Diagnostics.EventLog();
            if (!System.Diagnostics.EventLog.SourceExists("NCMService"))
            {
                System.Diagnostics.EventLog.CreateEventSource(
                    "NCMService", "Application");
            }
            EventLog4.Source = "NCMService";
            EventLog4.Log = "Application";

            EventLog4.WriteEntry("Telnet client connected: " + remoteClientIP);
            
            byte[] message = new byte[4096];
            int bytesRead;

            //Get our starting time:
            DateTime connecTime = DateTime.Now;
            //lastTelnetTime = Convert.ToString(connecTime);

            //Retrieve assembly version
            string AssemblyVersion = Assembly.GetExecutingAssembly().GetName().Version.ToString();

            //Display welcome message from the telnet server:
            ASCIIEncoding Pencoder = new ASCIIEncoding();
            outputMessage = "Network Control Module (v" + AssemblyVersion + ") - " + System.Environment.MachineName + " (From: " + remoteClientIP + ")" + Environment.NewLine + "Endpoint Time: " + connecTime + Environment.NewLine + Environment.NewLine + "?-> ";
            byte[] Pbuffer = Pencoder.GetBytes(outputMessage);

            clientStream.Write(Pbuffer, 0, Pbuffer.Length);
            clientStream.Flush();
            totalSocketTransmit += 1;

            while (true)
            {
                bytesRead = 0;

                try
                {
                    //blocks until a client sends a message
                    bytesRead = clientStream.Read(message, 0, 4096);
                }
                catch
                {
                    //a socket error has occured
                    EventLog4.WriteEntry("Telnet client " + remoteClientIP + " has disconnected");
                    lastTelnetTime = Convert.ToString(connecTime);
                    lastTelnetIP = remoteClientIP;
                    break;
                }

                if (bytesRead == 0)
                {
                    //the client has disconnected from the server
                    EventLog4.WriteEntry("Telnet client " + remoteClientIP + " has disconnected");
                    lastTelnetTime = Convert.ToString(connecTime);
                    lastTelnetIP = remoteClientIP;
                    break;
                }

                //message has successfully been received
                ASCIIEncoding encoder = new ASCIIEncoding();
                System.Diagnostics.Debug.WriteLine(encoder.GetString(message, 0, bytesRead));
                incomingMessage = encoder.GetString(message, 0, bytesRead);
                //incomingMessage = incomingMessage.ToUpper();
                EventLog4.WriteEntry("Incoming command: " + incomingMessage);
                totalSocketReceive += 1;

                //match output message to the same case we came in with
                string matchCaseOutputMessage = "";

                if (incomingMessage.ToUpper() == "U")
                {
                    if(incomingMessage == "u")
                    {
                        matchCaseOutputMessage = "pdate";
                    }
                    else
                    {
                        matchCaseOutputMessage = "PDATE";
                    }

                    //Update
                    outputMessage = matchCaseOutputMessage + Environment.NewLine + outMessage + Environment.NewLine + Environment.NewLine + "?-> ";
                }
                else if (incomingMessage.ToUpper() == "S")
                {
                    if (incomingMessage == "s")
                    {
                        matchCaseOutputMessage = "tatus";
                    }
                    else
                    {
                        matchCaseOutputMessage = "TATUS";
                    }

                    //status
                    uptimeNow = System.DateTime.Now;
                    TimeSpan totalUpTime = DateTime.Parse(Convert.ToString(uptimeNow)).Subtract(DateTime.Parse(Convert.ToString(uptimeStart)));

                    outputMessage = matchCaseOutputMessage + Environment.NewLine + "CURRENT STATE: " + currentState + Environment.NewLine + "Service Uptime: " + totalUpTime + Environment.NewLine + "Failovers: " + failoverCount + Environment.NewLine + "Recoveries: " + recoveries + Environment.NewLine + "Complete Outages: " + fullOutages + Environment.NewLine + "DAQ Update Requests: " + daqUpdates + Environment.NewLine + "Telnet Connections: " + telnetConnections + "  (Last From: " + lastTelnetIP + " On: " + lastTelnetTime + ")" + Environment.NewLine + "Socket Packets Received: " + totalSocketReceive + Environment.NewLine + "Socket Packets Sent: " + totalSocketTransmit + Environment.NewLine + Environment.NewLine + "?-> ";
                }
                else if (incomingMessage.ToUpper() == "T")
                {
                    if (incomingMessage == "t")
                    {
                        matchCaseOutputMessage = "ime";
                    }
                    else
                    {
                        matchCaseOutputMessage = "IME";
                    }

                    //Update display of server time
                    outputMessage = matchCaseOutputMessage + Environment.NewLine + "Endpoint time: " + System.DateTime.Now + Environment.NewLine + Environment.NewLine + "?-> ";
                }
                else if (incomingMessage.ToUpper() == "Q")
                {
                    if (incomingMessage == "q")
                    {
                        matchCaseOutputMessage = "uit";
                    }
                    else
                    {
                        matchCaseOutputMessage = "UIT";
                    }
                    
                    //quit
                    DateTime endTime = DateTime.Now;
                    TimeSpan totalTime = DateTime.Parse(Convert.ToString(endTime)).Subtract(DateTime.Parse(Convert.ToString(connecTime)));
                                        
                    //DateTime ConvertTime = Convert.ToDateTime(totalTime);
                   //string DisplayTime = ConvertTime.ToString("hh:mm");

                    outputMessage = matchCaseOutputMessage + Environment.NewLine + "Closing terminal session.  Session duration: " + totalTime + Environment.NewLine;
                    
                }
                else if (incomingMessage.ToUpper() == "C")
                {
                    if (incomingMessage == "c")
                    {
                        matchCaseOutputMessage = "lear stats";
                    }
                    else
                    {
                        matchCaseOutputMessage = "LEAR STATS";
                    }

                    //clear counters and display message indicating same
                    failoverCount = 0;
                    recoveries = 0;
                    fullOutages = 0;
                    daqUpdates = 0;
                    telnetConnections = 0;
                    totalSocketReceive = 0;
                    totalSocketTransmit = 0;
                    lastTelnetIP = "";
                    lastTelnetTime = "";
                    outputMessage = matchCaseOutputMessage + Environment.NewLine + "Stats cleared" + Environment.NewLine + Environment.NewLine + "?-> ";
                }
                else
                {
                    outputMessage = Environment.NewLine + "Valid commands:  U (Update), S (Status), T (Time), C (Clear Stats), Q (Quit)" + Environment.NewLine + Environment.NewLine + "?-> ";
                    
                }
                                

                //ASCIIEncoding Outencoder = new ASCIIEncoding();
                byte[] buffer = encoder.GetBytes(outputMessage);

                clientStream.Write(buffer, 0, buffer.Length);
                clientStream.Flush();
                totalSocketTransmit += 1;

                if (incomingMessage.ToUpper() == "Q")
                {
                    EventLog4.WriteEntry("Telnet client " + remoteClientIP + " has disconnected");
                    lastTelnetTime = Convert.ToString(connecTime);
                    lastTelnetIP = remoteClientIP;
                    break;
                }

            }

            tcpClient.Close();
        }

        private void FailoverRecovery()
        {
            System.Diagnostics.EventLog EventLogf = new System.Diagnostics.EventLog();
            if (!System.Diagnostics.EventLog.SourceExists("NCMService"))
            {
                System.Diagnostics.EventLog.CreateEventSource(
                    "NCMService", "Application");
            }
            EventLogf.Source = "NCMService";
            EventLogf.Log = "Application";
            
            //Recovery from a failover state.  We are called anytime we recover connectivity to the primary connection after a failover has
            //occurred.  We are also called when the service first starts up, to see if there are any records sitting on the failover server
            //that still need to be copied.  This step is necessary in case something happens to either this service or this machine while
            //a recovery is underway.  Our call at startup occurs IF we have established our initial primary connection.
            //
            //First step is to check counts on the test tables on the failover server to see if they are > 0.  If they are = 0, there is
            //nothing to do.  Otherwise, we need to do the following:
            //1.  Check for existence of the record on the primary server and copy record ONLY if it isn't on the primary
            //2.  Remove the record from failover host.
            //3.  Repeat the above for each subsequent record.
            //4.  Return to the caller.
            //
            //Reverse our redirection (copy hosts_HOSTBACK back to hosts):
                       
            string WindowsHostFile = System.Environment.SystemDirectory + "\\Drivers\\etc\\hosts";
            string hostFile = System.Environment.SystemDirectory + "\\Drivers\\etc\\hosts_HOSTBACK";
            int recordCountHC = 0;
            int recordCountTT = 0;
            int recordCountPT = 0;

            if (!File.Exists(hostFile))
            {
                return;     //No failover state exists, nothing to recover from, return to caller
            }
            
            File.Copy(hostFile, WindowsHostFile, true);
            //Now delete the backup file:
            File.Delete(hostFile);

            EventLogf.WriteEntry("Failover Redirection Reversed");

            //Now check the failover server for record counts:
            string conString = "Initial Catalog = DAQ;Data Source = " + failoverHost + ";Integrated Security = False;User ID = daquser;Password = daq";
            string conStringPrimary = "Initial Catalog = DAQ;Data Source = " + primaryHost + ";Integrated Security = False;User ID = daquser;Password = daq";

            EventLogf.WriteEntry("About to attempt connection with connection string: " + conString);
            
            //Create a connection object to the failover host we will be copying FROM:
            SqlConnection cnRecovery = new SqlConnection(conString);
            cnRecovery.Open();

            //Create a connection object to the recovered primary host will be copying TO:
            SqlConnection cnPrimary = new SqlConnection(conString);
            cnPrimary.Open();

            EventLogf.WriteEntry("Primary recovery connection open");

            SqlCommand command = new SqlCommand("Select Count(testnumber) As cnt From HeadCapTest", cnRecovery);
            SqlDataReader reader = command.ExecuteReader();
            reader.Read();
            EventLogf.WriteEntry("Records in HeadCapTest: " + reader["cnt"]);
            recordCountHC = Convert.ToInt16(reader["cnt"]);
            reader.Close();

            SqlCommand command2 = new SqlCommand("Select Count(testnumber) As cnt From PrimingTest", cnRecovery);
            SqlDataReader reader2 = command2.ExecuteReader();
            reader2.Read();
            EventLogf.WriteEntry("Records in PrimingTest: " + reader2["cnt"]);
            recordCountPT = Convert.ToInt16(reader2["cnt"]);
            reader2.Close();

            SqlCommand command3 = new SqlCommand("Select Count(testnumber) As cnt From TemperatureTest", cnRecovery);
            SqlDataReader reader3 = command3.ExecuteReader();
            reader3.Read();
            EventLogf.WriteEntry("Records in TemperatureTest: " + reader3["cnt"]);
            recordCountTT = Convert.ToInt16(reader3["cnt"]);
            reader3.Close();
           
            //If we have record counts higher than 0, we have records that need to be copied from the failover host to GRCBI. Begin with HeadCapTest
            //*** The copy commands can be tested by replacing primaryhost with testprimary host below.

            //Process HeadCapTest records
            if (recordCountHC > 0)
            {
                EventLogf.WriteEntry("Copying " + recordCountHC + " HEADCAPTEST records from failover host to primary host");
                SqlCommand commandHC = new SqlCommand("Insert into " + primaryHost + ".daq.dbo.headcaptest (Pressure, Vacuum, GageCorr, VH, TDH, Flow, RPM, PowerFactor, Torque, TestNumber, Timestamp, TestStand, L1_L2_Volts, L2_L3_Volts, L3_L1_Volts, AverageL_L_Volts, L1_Current, L2_Current, L3_Current, AverageCurrent, L1_KW, L2_KW, L3_KW, TotalKW, L1_PF, L2_PF, L3_PF, TruePF, Temp1, Temp2, Temp3, Temp4, Temp5, Temp6, Pressure1, Pressure2, Pressure3, HP, Efficiency, Barometer, Sound, NPSHR, Comment) Select Pressure, Vacuum, GageCorr, VH, TDH, Flow, RPM, PowerFactor, Torque, TestNumber, Timestamp, TestStand, L1_L2_Volts, L2_L3_Volts, L3_L1_Volts, AverageL_L_Volts, L1_Current, L2_Current, L3_Current, AverageCurrent, L1_KW, L2_KW, L3_KW, TotalKW, L1_PF, L2_PF, L3_PF, TruePF, Temp1, Temp2, Temp3, Temp4, Temp5, Temp6, Pressure1, Pressure2, Pressure3, HP, Efficiency, Barometer, Sound, NPSHR, Comment from " + failoverHost + ".daq.dbo.headcaptest", cnPrimary);
                commandHC.ExecuteNonQuery();
                commandHC.Dispose();

                EventLogf.WriteEntry("Removing HEADCAPTEST records from failover host");
                SqlCommand commandHCD = new SqlCommand("Delete from " + failoverHost + ".daq.dbo.headcaptest", cnPrimary);
                commandHCD.ExecuteNonQuery();
                commandHCD.Dispose();
            }

            //Process PrimingTest records
            if (recordCountPT > 0)
            {
                EventLogf.WriteEntry("Copying " + recordCountPT + " PRIMINGTEST records from failover host to primary host");
                SqlCommand commandPT = new SqlCommand("Insert into " + primaryHost + ".daq.dbo.primingtest (TestNumber, PrimeLevel1, PrimeTime1, PrimeLevel2, PrimeTime2, PrimeLevel3, PrimeTime3, PrimeLevel4, PrimeTime4, PrimeLevel5, PrimeTime5, PrimeLevel6, PrimeTime6, PrimeLevel7, PrimeTime7, PrimeLevel8, PrimeTime8, PrimeLevel9, PrimeTime9, PrimeLevel10, PrimeTime10, PrimeLevel11, PrimeTime11, PrimeLevel12, PrimeTime12, PrimeLevel13, PrimeTime13, PrimeLevel14, Primetime14, PrimeLevel15, PrimeTime15, PrimeLevel16, PrimeTime16, Timestamp, TestStand, LiquidLevelCasing, MaxLift, MaxVacuum, StaticLift, RPM, FlowAtDelivery, DeliveryTime) Select TestNumber, PrimeLevel1, PrimeTime1, PrimeLevel2, PrimeTime2, PrimeLevel3, PrimeTime3, PrimeLevel4, PrimeTime4, PrimeLevel5, PrimeTime5, PrimeLevel6, PrimeTime6, PrimeLevel7, PrimeTime7, PrimeLevel8, PrimeTime8, PrimeLevel9, PrimeTime9, PrimeLevel10, PrimeTime10, PrimeLevel11, PrimeTime11, PrimeLevel12, PrimeTime12, PrimeLevel13, PrimeTime13, PrimeLevel14, Primetime14, PrimeLevel15, PrimeTime15, PrimeLevel16, PrimeTime16, Timestamp, TestStand, LiquidLevelCasing, MaxLift, MaxVacuum, StaticLift, RPM, FlowAtDelivery, DeliveryTime from " + failoverHost + ".daq.dbo.primingtest", cnPrimary);
                commandPT.ExecuteNonQuery();
                commandPT.Dispose();

                EventLogf.WriteEntry("Removing PRIMINGTEST records from failover host");
                SqlCommand commandPTD = new SqlCommand("Delete from " + failoverHost + ".daq.dbo.primingtest", cnPrimary);
                commandPTD.ExecuteNonQuery();
                commandPTD.Dispose();
            }

            //Process TemperatureTest records
            if (recordCountTT > 0)
            {
                EventLogf.WriteEntry("Copying " + recordCountTT + " TEMPERATURETEST records from failover host to primary host");
                SqlCommand commandTT = new SqlCommand("Insert into " + primaryHost + ".daq.dbo.TEMPERATUREtest (Temp1, Temp2, Temp3, Temp4, Temp5, Temp6, Temp7, Temp8, TestNumber, TimeStamp, TestStand) Select Temp1, Temp2, Temp3, Temp4, Temp5, Temp6, Temp7, Temp8, TestNumber, TimeStamp, TestStand from " + failoverHost + ".daq.dbo.temperaturetest", cnPrimary);
                commandTT.ExecuteNonQuery();
                commandTT.Dispose();

                EventLogf.WriteEntry("Removing TEMPERATURETEST records from failover host");
                SqlCommand commandTTD = new SqlCommand("Delete from " + failoverHost + ".daq.dbo.TEMPERATUREtest", cnPrimary);
                commandTTD.ExecuteNonQuery();
                commandTTD.Dispose();
            }

            EventLogf.WriteEntry("Recovery processing completed"); 
            
            cnRecovery.Close();
            cnPrimary.Close();

        }

        private void checkPrimary()
        {

            try
            {
                IPHostEntry ipHost = Dns.Resolve(primaryHost);
                primaryGood = 1;
            }
            catch (SocketException se)
            {
                primaryGood = 0;
            }

        }
               
        private void trythis()
        {
            //Try connection to the failover host which will typically (for now) be localhost

            TcpClient tcpClient = new TcpClient();
            try
            {
                tcpClient.Connect("127.0.0.1", 3232);
                goodFailoverConnect = 1;
            }
            catch (Exception)
            {

                goodFailoverConnect = 0;
            }
        }

        private void CheckHosts()
        {
            //If hosts_HOSTBACK exists, rename it to hosts.  If a failover state still exists, it will be changed back to the failover
            //version by the service when that determination has been made.

            string hostFile = System.Environment.SystemDirectory + "\\Drivers\\etc\\hosts_HOSTBACK";
            string originalhostFile = System.Environment.SystemDirectory + "\\Drivers\\etc\\hosts";

            if (File.Exists(hostFile))
            {
                File.Copy(hostFile, originalhostFile, true);
                File.Delete(hostFile);
                
            }
        }

        private void engageFailoverRedirection()
        {
            //Set up redirection machine-wide by manipulating the hosts file so that any calls to the primary host will redirect to the failover host
            
            System.Diagnostics.EventLog EventLogr = new System.Diagnostics.EventLog();
            if (!System.Diagnostics.EventLog.SourceExists("NCMService"))
            {
                System.Diagnostics.EventLog.CreateEventSource(
                    "NCMService", "Application");
            }
            EventLogr.Source = "NCMService";
            EventLogr.Log = "Application";
            
            string WindowsHostFile = System.Environment.SystemDirectory + "\\Drivers\\etc\\hosts";
            string NCMHostFile = System.Environment.SystemDirectory + "\\Drivers\\etc\\hosts_NCM";

            string hostFile = System.Environment.SystemDirectory + "\\Drivers\\etc\\hosts_HOSTBACK";
            string originalhostFile = System.Environment.SystemDirectory + "\\Drivers\\etc\\hosts";
            
            if (File.Exists(hostFile))
            {
                //the host file was already backed up; do nothing but simply continue
            }
            else
            {
                //backup the host file:
                File.Move(WindowsHostFile, hostFile);

                //Copy the NCM version of the host file to hosts, to achieve failover redirection:
                File.Copy(NCMHostFile, WindowsHostFile, true);

                EventLogr.WriteEntry("Failover Redirection Active");

            }
        }
                
    }
}
