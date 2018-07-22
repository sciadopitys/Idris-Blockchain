module BlockchainMain

%default total

||| record used to represent a node of a blockchain
record Node where
       constructor CreateNode
       node : Nat
       nonce : Integer
       dataField : String
       prevHash : Bits 128
       hash : Bits 128

Show Node where --implementation of show interface for node record
  show (CreateNode node nonce dataField prevHash hash) = "\nNode #: " ++ show node ++ "\nNonce: " ++ show nonce ++ "\nData: " ++ show dataField ++ "\nPrevious Hash: " ++ show prevHash ++ "\nHash: " ++ show hash

||| record used to represent a blockchain
record Blockchain where
       constructor CreateChain
       size : Nat
       act : Vect size Node

||| Obtain an Integer value given a list of chars
getIntRep : List Char -> (acc : Int) -> Integer
getIntRep [] acc = the Integer (cast acc)
getIntRep (x :: xs) acc = getIntRep xs (acc + (ord x))

||| Given the node #, datum, and previous hash fields of a node, obtains a nonce and hash as per the desired level of difficulty
partial --cannot be total as it cannot be guaranteed to terminate
findNonceAndHash : (nodeNumBits : Bits 128) -> (datumBits : Bits 128) -> (curNonce : Integer) -> (prev: Bits 128) -> (Integer, Bits 128)
findNonceAndHash nodeNumBits datumBits curNonce prev = let nonceBits =  the (Bits 128) (intToBits curNonce) --convert current nonce (Integer) to Bits 128
                                                           message = the (Vect 4 (Bits 128)) [nodeNumBits, nonceBits, datumBits, prev] --create bit vector of relevant fields for input into hash function
                                                           curHash = hashMessage dummyMD5 message --obtain hash of relevant fields
                                                       in case ((bitsToInt curHash) <= 99999999999) of --determine if obtained hash satisfies difficulty requirement
                                                               False => findNonceAndHash nodeNumBits datumBits (curNonce + 1) prev --if not, try next nonce value
                                                               True => (curNonce, curHash) --if so, return nonce and obtained hash

||| Adds a node containing the input string to the input blockchain, returning a pair of the new blockchain and the added node
||| @chain the original blockchain
||| @newStr the desired datum to be added to the blockchain
||| @start the the nonce to start at for the mining function
partial --cannot be total due to use of findNonceAndHash
addNodeAlt : (chain : Blockchain) -> (newStr : String) -> (start : Integer) -> (Blockchain, Node)
addNodeAlt (CreateChain size chain) newStr start = let foundPair1 = addToChain chain start
                                                   in ((CreateChain (S size) (fst foundPair1)), (snd foundPair1)) where
                                                       partial --cannot be total due to use of findNonceAndHash
                                                       addToChain : (Vect n Node) -> Integer -> ((Vect (S n) Node), Node) --function to obtain the Node Vector representing the new blockchain
                                                       addToChain [] y = let genNumBits = the (Bits 128) (intToBits 1) -- if blockchain is currently empty (should never happen), add genesis block
                                                                             genStrToInt = getIntRep (unpack "Genesis Block") 0
                                                                             genStrBits =  the (Bits 128) (intToBits genStrToInt)
                                                                             foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
                                                                             genNode = CreateNode 1 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)
                                                                         in ([genNode], genNode)
                                                       addToChain [last] y = let curNumBits = the (Bits 128) (intToBits (toIntegerNat (S size))) --otherwise, convert number field of new node to Bits 128
                                                                                 newStrCharList = unpack newStr --convert desired string to Bits 128
                                                                                 newStrToInt = getIntRep newStrCharList 0
                                                                                 newStrBits =  the (Bits 128) (intToBits newStrToInt)
                                                                                 foundPair = findNonceAndHash curNumBits newStrBits y (hash last) --obtain nonce and hash fields
                                                                                 newNode = CreateNode (S size) (fst foundPair) newStr (hash last) (snd foundPair) --obtain new node
                                                                              in ((last :: [newNode]), newNode) --add new node to end of blockchain
                                                       addToChain (x :: xs) y = ((x :: (fst (addToChain xs y))), (snd (addToChain xs y))) --traverse down blockchain

||| Adds a node containing the input string to the input blockchain, returning the new blockchain
||| @chain the original blockchain
||| @newStr the desired datum to be added to the blockchain
partial --cannot be total due to use of findNonceAndHash
addNode : (chain : Blockchain) -> (newStr : String) -> Blockchain
addNode chain newStr = fst (addNodeAlt chain newStr 1) --simply call addNodeAlt function (starting with a nonce of 1), returning desired element of returned pair

||| Obtains a string representation of a blockchain, used for displaying a blockchain to the console
display : Blockchain -> String
display (CreateChain size chain) = displayChain chain where
    displayChain : Vect size1 Node -> String
    displayChain [] = "\n"
    displayChain (x :: xs) = show x ++ "\n" ++ displayChain xs

||| Function to ensure that a specified message is successfully sent over a socket
partial --cannot be total due to potential for infinite recursion
sendCont : Socket -> SocketAddress -> Port -> String -> IO ()
sendCont sock addr port str = do success <- sendTo sock addr port str
                                 case success of
                                      Left l => sendCont sock addr port str
                                      Right r => pure ()


||| Sends a message to all elements of a UDPAddrInfo Vector, returning an IO Bool
||| @str the message to be sent
||| @sock the current process's socket
||| @addrs a UDPAddrInfo Vector, where UDPAddrInfo is a record with address and port fields
partial --cannot be total due to sendCont
sendToProcs : (str : String) -> (sock : Socket) -> (addrs : Vect n UDPAddrInfo) -> (IO Bool)
sendToProcs str sock [] = pure True --all messages have been sent; return success
sendToProcs str sock (x :: xs) = do sendCont sock (remote_addr x) (remote_port x) str --send message to current port
                                    sendToProcs str sock xs

||| Waits for confirmation of a node addition from all collaborating processes, returning an IO Bool
||| @sock the current process's socket
||| @addrs a UDPAddrInfo Vector, where UDPAddrInfo is a record with address and port fields
||| @success keeps track of whether a denial has been received or an error has occurred (then returns failure)
recvConf : (sock : Socket) -> (addrs : Vect n UDPAddrInfo) -> (success: Bool) -> (IO Bool)
recvConf sock [] s = pure s --all confirmations/denials have been received; return success or failure
recvConf sock (x :: xs) s = do received <- recvFrom sock 2048 --wait for message
                               case received of
                                    Left l => do putStrLn "Receive failed"
                                                 recvConf sock xs False --error with received message; will return failure
                                    Right r => case (fst (snd r)) of --check whether received message was confirmation or not
                                                    "yes" => do putStrLn "Acceptance received" --if a confirmation was received
                                                                recvConf sock xs s
                                                    _ => do putStrLn "Denial received" --if a denial was received, will return failure
                                                            recvConf sock xs False
||| Obtains the last element of a Vector of nodes
getLastNode : Vect n Node -> Maybe (Node)
getLastNode [] = Nothing
getLastNode [x] = Just x
getLastNode (x :: xs) = getLastNode xs

||| Determines if a datum in the blockchain represents a RPS play; if so, also returns an int corresponding to the play
isPlay : String -> IO (Bool, Int)
isPlay "11111101010011011101111011111110111111111111111111111111111111101111110101001101110111101111111011111111111111111111111111111110" = pure (True, 0) --hashed string for "rock"
isPlay "11101101000110010111010101111101111111111111111111111111111111101110110100011001011101010111110111111111111111111111111111111110" = pure (True, 1) --hashed string for "paper"
isPlay "11111111100111111110111111101111111111111111111111111111111111101111111110011111111011111110111111111111111111111111111111111110" = pure (True, 2) --hashed string for "scissors"
isPlay _ = pure (False, -1)

||| Determines the winner of a RPS game, with plays represented as Ints
||| @p1 the play of the first Player
||| @p2 the play of the second player
getWinner : (p1 : Int) -> (p2 : Int) -> Int
getWinner 0 0 = 0 --rock/rock = tie
getWinner 0 1 = 2 --rock/paper = p2 wins
getWinner 0 2 = 1 --rock/scissors = p1 wins
getWinner 1 0 = 1 --paper/rock = p1 wins
getWinner 1 1 = 0 --paper/paper = tie
getWinner 1 2 = 2 --paper/scissors = p2 wins
getWinner 2 0 = 2 --scissors/rock = p2 wins
getWinner 2 1 = 1 --scissors/paper = p1 wins
getWinner 2 2 = 0 --scissors/scissors = tie
getWinner _ _ = -1

||| Function to ensure that a message is received on a socket
partial --cannot be total due to potential for infinite recursion
recvCont : Socket -> ByteLength -> IO (UDPAddrInfo, String, ResultCode)
recvCont sock len = do success <- recvFrom sock len
                       case success of
                            Left l => recvCont sock len
                            Right r => pure r

||| executes a desired command on a blockchain; used for single blockchain simulation
||| @chain the current blockchain
||| @command the desired command
||| @newStr the string to be added to the blockchain; relevant for the "add" command
partial
executeCommand : (chain : Blockchain) -> (command : String) -> (newStr : String) -> Maybe (String, Blockchain)
executeCommand chain "add" newStr = Just ("Added new node\n", addNode chain (strTail(newStr))) --add a node to end of the blockchian
executeCommand chain "display" "" = Just ((display chain), chain) --display current blockchain to console
executeCommand chain "quit" "" = Nothing --exit replWith loop
executeCommand chain _ _ = Just ("Invalid command\n", chain) --all other commands are invalid

||| executes a desired command on a blockchain; used for distributed blockchain simulation
||| @chain the current blockchain
||| @command the desired command
||| @newStr the string to be added to the blockchain; relevant for the "add" command
||| @sock the current process's socket
||| @addrs a UDPAddrInfo Vector, where UDPAddrInfo is a record with address and port fields
||| @port the port the current process is bound to
partial
executeCommandAlt : (chain : Blockchain) -> (command : String) -> (newStr : String) -> (sock : Socket) -> (addrs : Vect n UDPAddrInfo) -> (port : Int) -> IO (Maybe (String, Blockchain))
executeCommandAlt {n} chain "add" newStr sock addrs _ = let newStrAct = strTail(newStr)
                                                            newChainPair = addNodeAlt chain newStrAct 1 --obtain new blockchain with added node
                                                            newChain = fst newChainPair
                                                            newNode = snd newChainPair
                                                            sendStr = newStrAct ++ "+" ++ (show (node newNode)) ++ "+" ++ (show (nonce newNode)) ++ "+" ++ (bitsToStr (prevHash newNode)) ++ "+" ++ (bitsToStr (hash newNode)) --send message about added node to other processes
                                                        in do success <- sendToProcs sendStr sock addrs
                                                              case success of
                                                                   False => pure (Just ("Unable to send message; did not add node\n", chain)) --if unable to send message, revert to original blockchain
                                                                   True => do consensus <- recvConf sock addrs True --otherwise, attempt to obtain consensus from other nodes
                                                                              case consensus of
                                                                                   False => do sendToProcs "do not add" sock addrs --consensus not reached; send message about reverting to original blockchain
                                                                                               pure (Just ("Consensus not reached; did not add node\n", chain))
                                                                                   True => do sendToProcs "add" sock addrs --consensus reached; send message about switching to new blockchain
                                                                                              pure (Just ("Consensus reached; added node\n", newChain))
--to initiate consensus protocol
executeCommandAlt chain "receive" "" sock addrs _ = do received <- recvCont sock 2048 --receive message
                                                       let recvStr = fst (snd received) --bind info from received message to names
                                                       let senderInfo = fst received
                                                       let senderAddr = remote_addr senderInfo
                                                       let senderPort = remote_port senderInfo
                                                       case split (== '+') recvStr of
                                                            [newStr, nodeNumStr, nonceStr, rightPHash, rightHash] => let nonceParse = parseInteger nonceStr
                                                                                                                     in case nonceParse of
                                                                                                                             Nothing => do sendCont sock senderAddr senderPort "no" --message received was in wrong format; send denial to sender
                                                                                                                                           received2 <- recvFrom sock 2048
                                                                                                                                           pure (Just ("Incorrect format of message\n", chain)) -- revert to original blockchain
                                                                                                                             Just rightNonce => let newChainPair = addNodeAlt chain newStr rightNonce --obtain resultant blockchain from adding desired string and new added node
                                                                                                                                                    newNode = snd newChainPair
                                                                                                                                                --confirm that all fields of new node are identical to those of corresponding node in sender's blockchain
                                                                                                                                                in do case ((rightHash == (bitsToStr (hash newNode))) && ((rightPHash == (bitsToStr (prevHash newNode))) && ((rightNonce == (nonce newNode)) && (nodeNumStr == (show (node newNode)))))) of
                                                                                                                                                           False => do sendCont sock senderAddr senderPort "no" --if not, send denial to sender
                                                                                                                                                                       putStrLn ("Denying change")
                                                                                                                                                           True => do sendCont sock senderAddr senderPort "yes" --otherwise, send confirmation
                                                                                                                                                                      putStrLn ("Accepting change")
                                                                                                                                                      received1 <- recvCont sock 2048 --receive another message from original sender
                                                                                                                                                      let recvStr = fst (snd received1)
                                                                                                                                                      case recvStr of
                                                                                                                                                           "add" => pure (Just ("Implementing change\n", (fst newChainPair))) --if message was "add", switch to new blockchain
                                                                                                                                                           _ => pure (Just ("Discarding proposed change\n", chain)) --otherwise, revert to original blockchain
                                                            _ => do sendCont sock senderAddr senderPort "no" --message received was in wrong format; send denial to sender
                                                                    received3 <- recvFrom sock 2048
                                                                    pure (Just ("Incorrect format of message\n", chain)) -- revert to original blockchain
executeCommandAlt chain "rock" "" sock addrs port = let lastNode = getLastNode (act chain) --obtain last block of current chain
                                                    in do case lastNode of
                                                               Nothing => pure (Just ("Genesis block not found", addNode chain "Genesis Block" )) --chain is currently empty (should never happen); add genesis block
                                                               Just x => let lastStr = dataField x --otherwise, get datum field of last block
                                                                         in do case split (== '*') lastStr of
                                                                                    [player, hashedPlay] => case (player == (show port)) of --last string has format of a RPS play, determine if current process made last play
                                                                                                                 True => pure (Just ("Cannot play both sides of a game\n", chain)) --if so, disregared new play
                                                                                                                 False => do play <- isPlay hashedPlay --if not, confirm that last string does represent a RPS play
                                                                                                                             case (fst play) of
                                                                                                                                  --last string added doesn't represent a RPS play, add specified play to blobkchain
                                                                                                                                  False => let playToInt = getIntRep (unpack "rock") 0 --perform cryptographic hash of the specified string
                                                                                                                                               playBits =  the (Bits 128) (intToBits playToInt)
                                                                                                                                               playHash = hashMessage dummyMD5 [playBits]
                                                                                                                                               playHashStr = bitsToStr playHash --convert bits back into string
                                                                                                                                           in do --putStrLn playHashStr
                                                                                                                                                 executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ playHashStr) sock addrs port --add port number and hashed string to blockchain
                                                                                                                                  True => let winner = getWinner (snd play) 0 --a game was played, determine winner
                                                                                                                                          in case winner of
                                                                                                                                                  0 => executeCommandAlt chain "add" (" Players (" ++ player ++ ", " ++ (show port) ++ ") Tied") sock addrs port
                                                                                                                                                  1 => executeCommandAlt chain "add" (" Player 1 (" ++ player ++ ") Won") sock addrs port
                                                                                                                                                  2 => executeCommandAlt chain "add" (" Player 2 (" ++ (show port) ++ ") Won") sock addrs port
                                                                                                                                                  _ => pure (Just ("Unable to determine winner\n", chain))
                                                                                    _ => let playToInt = getIntRep (unpack "rock") 0 --perform cryptographic hash of the specified string
                                                                                             playBits =  the (Bits 128) (intToBits playToInt)
                                                                                             playHash = hashMessage dummyMD5 [playBits]
                                                                                             playHashStr = bitsToStr playHash --convert bits back into string
                                                                                         in do --putStrLn playHashStr
                                                                                               executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ playHashStr) sock addrs port --add port number and hashed string to blockchain
executeCommandAlt chain "paper" "" sock addrs port = let lastNode = getLastNode (act chain) --obtain last block of current chain
                                                     in do case lastNode of
                                                                Nothing => pure (Just ("Genesis block not found", addNode chain "Genesis Block" )) --chain is currently empty (should never happen); add genesis block
                                                                Just x => let lastStr = dataField x --otherwise, get datum field of last block
                                                                          in do case split (== '*') lastStr of
                                                                                     [player, hashedPlay] => case (player == (show port)) of --last string has format of a RPS play, determine if current process made last play
                                                                                                                  True => pure (Just ("Cannot play both sides of a game\n", chain)) --if so, disregared new play
                                                                                                                  False => do play <- isPlay hashedPlay --if not, confirm that last string does represent a RPS play
                                                                                                                              case (fst play) of
                                                                                                                                   --last string added doesn't represent a RPS play, add specified play to blobkchain
                                                                                                                                   False => let playToInt = getIntRep (unpack "paper") 0 --perform cryptographic hash of the specified string
                                                                                                                                                playBits =  the (Bits 128) (intToBits playToInt)
                                                                                                                                                playHash = hashMessage dummyMD5 [playBits]
                                                                                                                                                playHashStr = bitsToStr playHash --convert bits back into string
                                                                                                                                            in do --putStrLn playHashStr
                                                                                                                                                  executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ playHashStr) sock addrs port --add port number and hashed string to blockchain
                                                                                                                                   True => let winner = getWinner (snd play) 1 --a game was played, determine winner
                                                                                                                                           in case winner of
                                                                                                                                                   0 => executeCommandAlt chain "add" (" Players (" ++ player ++ ", " ++ (show port) ++ ") Tied") sock addrs port
                                                                                                                                                   1 => executeCommandAlt chain "add" (" Player 1 (" ++ player ++ ") Won") sock addrs port
                                                                                                                                                   2 => executeCommandAlt chain "add" (" Player 2 (" ++ (show port) ++ ") Won") sock addrs port
                                                                                                                                                   _ => pure (Just ("Unable to determine winner\n", chain))
                                                                                     _ => let playToInt = getIntRep (unpack "paper") 0 --perform cryptographic hash of the specified string
                                                                                              playBits =  the (Bits 128) (intToBits playToInt)
                                                                                              playHash = hashMessage dummyMD5 [playBits]
                                                                                              playHashStr = bitsToStr playHash --convert bits back into string
                                                                                          in do --putStrLn playHashStr
                                                                                                executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ playHashStr) sock addrs port --add port number and hashed string to blockchain
executeCommandAlt chain "scissors" "" sock addrs port = let lastNode = getLastNode (act chain) --obtain last block of current chain
                                                        in do case lastNode of
                                                                   Nothing => pure (Just ("Genesis block not found", addNode chain "Genesis Block" )) --chain is currently empty (should never happen); add genesis block
                                                                   Just x => let lastStr = dataField x --otherwise, get datum field of last block
                                                                             in do case split (== '*') lastStr of
                                                                                        [player, hashedPlay] => case (player == (show port)) of --last string has format of a RPS play, determine if current process made last play
                                                                                                                     True => pure (Just ("Cannot play both sides of a game\n", chain)) --if so, disregared new play
                                                                                                                     False => do play <- isPlay hashedPlay --if not, confirm that last string does represent a RPS play
                                                                                                                                 case (fst play) of
                                                                                                                                      --last string added doesn't represent a RPS play, add specified play to blobkchain
                                                                                                                                      False => let playToInt = getIntRep (unpack "scissors") 0 --perform cryptographic hash of the specified string
                                                                                                                                                   playBits =  the (Bits 128) (intToBits playToInt)
                                                                                                                                                   playHash = hashMessage dummyMD5 [playBits]
                                                                                                                                                   playHashStr = bitsToStr playHash --convert bits back into string
                                                                                                                                               in do --putStrLn playHashStr
                                                                                                                                                     executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ playHashStr) sock addrs port --add port number and hashed string to blockchain
                                                                                                                                      True => let winner = getWinner (snd play) 2 --a game was played, determine winner
                                                                                                                                              in case winner of
                                                                                                                                                      0 => executeCommandAlt chain "add" (" Players (" ++ player ++ ", " ++ (show port) ++ ") Tied") sock addrs port
                                                                                                                                                      1 => executeCommandAlt chain "add" (" Player 1 (" ++ player ++ ") Won") sock addrs port
                                                                                                                                                      2 => executeCommandAlt chain "add" (" Player 2 (" ++ (show port) ++ ") Won") sock addrs port
                                                                                                                                                      _ => pure (Just ("Unable to determine winner\n", chain))
                                                                                        _ => let playToInt = getIntRep (unpack "scissors") 0 --perform cryptographic hash of the specified string
                                                                                                 playBits =  the (Bits 128) (intToBits playToInt)
                                                                                                 playHash = hashMessage dummyMD5 [playBits]
                                                                                                 playHashStr = bitsToStr playHash --convert bits back into string
                                                                                             in do --putStrLn playHashStr
                                                                                                   executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ playHashStr) sock addrs port --add port number and hashed string to blockchain
executeCommandAlt chain command newStr _ _ _ = pure (executeCommand chain command newStr) -- all other commands executed by calling executeCommand

||| processes user input by calling executeCommand; used for single blockchain simulation
||| @chain the current blockchain
||| @input the user input string
partial
processInput : (chain : Blockchain) -> (input : String) -> Maybe (String, Blockchain)
processInput chain input = case span (/= ' ') input of --split input into two strings if possible
                                (command, newStr) => executeCommand chain command newStr

||| processes user input by calling executeCommand; used for distributed blockchain simulation
||| @chain the current blockchain
||| @input the user input string
||| @sock the current process's socket
||| @addrs a UDPAddrInfo Vector, where UDPAddrInfo is a record with address and port fields
||| @port the port the current process is bound to
partial
processInputAlt : (chain : Blockchain) -> (input : String) -> (sock : Socket) -> (addrs : Vect n UDPAddrInfo) -> (port : Int) -> IO (Maybe (String, Blockchain))
processInputAlt chain input sock addrs port = case span (/= ' ') input of
                                                   (command, newStr) => executeCommandAlt chain command newStr sock addrs port

||| creates a Vector of UDPAddrInfo given a Vector of port numbers (Ints)
||| @ ports a Vector of ints representing port numbers
createAddrs : (ports : Vect n Int) -> Vect n UDPAddrInfo
createAddrs [] = []
createAddrs (x :: xs) = let curAddr = IPv4Addr 127 0 0 1 --create localhost IPv4 addr
                        in (MkUDPAddrInfo curAddr x) :: createAddrs xs --create UDPAddrInfo record given created addr and current port number and add to output Vector

||| Process that simulates replWith loop; used for distributed blockchain simulation
||| @sock the current process's socket
||| @addrs a UDPAddrInfo Vector, where UDPAddrInfo is a record with address and port fields
||| @chain the current blockchain
||| @port the port the current process is bound to
partial
processInputLoop : (sock : Socket) -> (addrs : Vect n UDPAddrInfo) -> (chain : Blockchain) -> (port : Int) -> (Process ProcessLib.clientType () NoRequest NoRequest)
processInputLoop sock addrs chain port = do Action (putStr "Command: ") --prompt user for input
                                            command <- Action (getLine) --obtain input
                                            pInput <- Action (processInputAlt chain command sock addrs port) --process input by calling processInputAlt
                                            case pInput of
                                                 Nothing => RespondToEnd (\msg => Pure ()) --if user has specified "quit" command, respond to main Process to end program
                                                 Just x => do Action (putStr (fst x)) --otherwise, call new iteration of process
                                                              LoopNoReq (processInputLoop sock addrs (snd x) port)

||| Main process; performs initialization of necessary variables and blockchain itself (adds genesis block)
||| @ ports a Vector of ints representing port numbers
partial
procMain : (ports : Vect n Int) -> (Process NoRecv () NoRequest NoRequest)
procMain [] = let genNumBits = the (Bits 128) (intToBits 1) --create genesis block
                  genStrToInt = getIntRep (unpack "Genesis Block") 0
                  genStrBits =  the (Bits 128) (intToBits genStrToInt)
                  foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
              in Action (replWith (CreateChain 1 [CreateNode 1 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)]) "Command: " processInput) --single blockchain simulation using replWith
procMain [x] = Action (putStrLn "Must specify more than 1 port number") --ports Vector must have more than 1 element (or none)
procMain (x :: xs) = let myAddr = IPv4Addr 127 0 0 1 --create localhost IPv4 addr for this process
                         udpAddrVect = createAddrs xs --obtain UDPAddrInfo Vector based on specified Vector of port numbers
                         genNumBits = the (Bits 128) (intToBits 1) --create constructs needed to create genesis block
                         genStrToInt = getIntRep (unpack "Genesis Block") 0
                         genStrBits =  the (Bits 128) (intToBits genStrToInt)
                         foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
                     in do sock <- Action (socket AF_INET Datagram 0) -- initialize UDP socket
                           case sock of
                                Left l => Action (putStrLn "socket failed") --if socket creation was unsuccessful
                                Right r => do bindRet <- Action (bind r (Just myAddr) x) --otherwise, bind socket to this process's addr and port
                                              if (bindRet == 0)
                                                 then do Just loopPID <- SpawnClient (processInputLoop r udpAddrVect (CreateChain 1 [CreateNode 1 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)]) x) --spawn processInputLoop process, passing bound socket (distributed blockchain simulation)
                                                              | Nothing => Action (putStrLn "spawn failed") --if unable to spawn new process
                                                         RequestToWait loopPID 1 --wait for looping process to respond and finish
                                                 else Action (putStrLn "bind failed") --if bind failed
