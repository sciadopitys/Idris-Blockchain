module BlockchainMain

import Data.Vect
import Data.Bits
import ProcessLib
import Data.Fin
import System.Concurrency.Channels
import Network.Socket
import Data.Crypto.Hash.MD5
import Data.Crypto.Hash

%default total

||| record used to represent a block of a blockchain
record Block where
       constructor CreateBlock
       block : Nat
       nonce : Integer
       dataField : String
       prevHash : Bits 128
       hash : Bits 128

Show Block where --implementation of show interface for block record
  show (CreateBlock block nonce dataField prevHash hash) = "\nBlock #: " ++ show block ++ "\nNonce: " ++ show nonce ++ "\nData: " ++ show dataField ++ "\nPrevious Hash: " ++ show prevHash ++ "\nHash: " ++ show hash

data VectSameOrInc : Type -> Type where
     Same : (len : Nat) -> Vect len a -> VectSameOrInc a
     Inc : (len : Nat) -> Vect (S len) a -> VectSameOrInc a

||| Obtain an Integer value given a list of chars
getIntRep : List Char -> (acc : Int) -> Integer
getIntRep [] acc = the Integer (cast acc)
getIntRep (x :: xs) acc = getIntRep xs (acc + (ord x))

||| Given the block #, datum, and previous hash fields of a block, obtains a nonce and hash as per the desired level of difficulty
partial --cannot be total as it cannot be guaranteed to terminate
findNonceAndHash : (blockNumBits : Bits 128) -> (datumBits : Bits 128) -> (curNonce : Integer) -> (prev: Bits 128) -> (Integer, Bits 128)
findNonceAndHash blockNumBits datumBits curNonce prev = let nonceBits =  the (Bits 128) (intToBits curNonce) --convert current nonce (Integer) to Bits 128
                                                            message = the (Vect 4 (Bits 128)) [blockNumBits, nonceBits, datumBits, prev] --create bit vector of relevant fields for input into hash function
                                                            curHash = hashMessage dummyMD5 message --obtain hash of relevant fields
                                                        in case ((bitsToInt curHash) <= 99999999999) of --determine if obtained hash satisfies difficulty requirement
                                                                False => findNonceAndHash blockNumBits datumBits (curNonce + 1) prev --if not, try next nonce value
                                                                True => (curNonce, curHash) --if so, return nonce and obtained hash

||| Adds a block containing the input string to the input blockchain, returning a pair of the new blockchain and the added block
||| @chain the original blockchain
||| @newStr the desired datum to be added to the blockchain
||| @start the the nonce to start at for the mining function
partial --cannot be total due to use of findNonceAndHash
addBlockAlt : (chain : Vect n Block) -> (newStr : String) -> (start : Integer) -> (size : Nat) -> (Vect (S n) Block, Block)
addBlockAlt [] _ _ _ = let genNumBits = the (Bits 128) (intToBits 0) -- if blockchain is currently empty (should never happen), add genesis block
                           genStrToInt = getIntRep (unpack "Genesis Block") 0
                           genStrBits =  the (Bits 128) (intToBits genStrToInt)
                           foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
                           genBlock = CreateBlock 0 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)
                       in ([genBlock], genBlock)
addBlockAlt [last] newStr start size = let curNumBits = the (Bits 128) (intToBits (toIntegerNat size)) --otherwise, convert number field of new block to Bits 128
                                           newStrCharList = unpack newStr --convert desired string to Bits 128
                                           newStrToInt = getIntRep newStrCharList 0
                                           newStrBits =  the (Bits 128) (intToBits newStrToInt)
                                           foundPair = findNonceAndHash curNumBits newStrBits start (hash last) --obtain nonce and hash fields
                                           newBlock = CreateBlock size (fst foundPair) newStr (hash last) (snd foundPair) --obtain new block
                                       in ((last :: [newBlock]), newBlock) --add new block to end of blockchain
addBlockAlt (x :: xs) newStr start size = let final = addBlockAlt xs newStr start size
                                          in ((x :: (fst final)), (snd final)) --traverse down blockchain

||| Adds a block containing the input string to the input blockchain, returning the new blockchain
||| @chain the original blockchain
||| @newStr the desired datum to be added to the blockchain
partial --cannot be total due to use of findNonceAndHash
addBlock : (chain : Vect n Block) -> (newStr : String) -> (size : Nat) -> Vect (S n) Block
addBlock chain newStr size = fst (addBlockAlt chain newStr 1 size) --simply call addBlockAlt function (starting with a nonce of 1), returning desired element of returned pair

||| Obtains a string representation of a blockchain, used for displaying a blockchain to the console
display : Vect n Block -> String
display [] = "\n"
display (x :: xs) = show x ++ "\n" ++ display xs

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

||| Waits for confirmation of a block addition from all collaborating processes, returning an IO Bool
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
||| Obtains the last element of a Vector of blocks
getLastBlock : Vect n Block -> Maybe (Block)
getLastBlock [] = Nothing
getLastBlock [x] = Just x
getLastBlock (x :: xs) = getLastBlock xs

||| Determines if a datum in the blockchain represents a RPS play; if so, also returns an int corresponding to the play
||| @datum a datum stored in the Blockchain
||| @commit string that should represent and integer value used to obfuscate an RPS play
isPlay : (datum : String) -> (commit : String)-> IO (Bool, Int)
isPlay datum commit = let parseCommit = parseInteger commit --determine if input commit string represents an integer value
                      in case parseCommit of
                              Nothing => pure (False, 0) --if not, datum doesn't represent an RPS play
                              Just commitInt => let commitBits = the (Bits 128) (intToBits commitInt) --otherwise, datum should represent an RPS play; determine play
                                                    rockBits = the (Bits 128) (intToBits (getIntRep (unpack "rock") 0))
                                                in case (datum == (bitsToStr (hashMessage dummyMD5 [rockBits, commitBits]))) of --determine if play is "rock"
                                                        False => let paperBits = the (Bits 128) (intToBits (getIntRep (unpack "paper") 0))
                                                                 in case (datum == (bitsToStr (hashMessage dummyMD5 [paperBits, commitBits]))) of --determine if play is "paper"
                                                                         False => let scBits = the (Bits 128) (intToBits (getIntRep (unpack "scissors") 0))
                                                                                  in case (datum == (bitsToStr (hashMessage dummyMD5 [scBits, commitBits]))) of --determine if play is "scissors"
                                                                                          False => pure (False, 0) --datum doesn't match any RPS plays
                                                                                          True => pure (True, 2) --play is "scissors"
                                                                         True => pure (True, 1) --play is "paper"
                                                        True => pure (True, 0) --play is "rock"



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
executeCommand : (chain : Vect m Block) -> (command : String) -> (newStr : String) -> Maybe (String, VectSameOrInc Block)
executeCommand {m} chain "add" newStr = let newChain = addBlock chain (strTail(newStr)) m
                                        in Just ("Added new block\n", (Inc m newChain)) --add a block to end of the blockchian
executeCommand {m} chain "display" "" = Just ((display chain), (Same m chain)) --display current blockchain to console
executeCommand {m} chain "quit" "" = Nothing --exit replWith loop
executeCommand {m} chain _ _ = Just ("Invalid command\n", (Same m chain)) --all other commands are invalid

||| executes a desired command on a blockchain; used for distributed blockchain simulation
||| @chain the current blockchain
||| @command the desired command
||| @newStr second string argument; for "add" command it is the new string to be added and for smart contracts it represents an integer value used to obfuscate RPS plays
||| @sock the current process's socket
||| @addrs a UDPAddrInfo Vector, where UDPAddrInfo is a record with address and port fields
||| @port the port the current process is bound to
partial
executeCommandAlt : (chain : Vect m Block) -> (command : String) -> (newStr : String) -> (sock : Socket) -> (addrs : Vect n UDPAddrInfo) -> (port : Int) -> IO (Maybe (String, VectSameOrInc Block))
executeCommandAlt {m} {n} chain "add" newStr sock addrs _ = let newStrAct = strTail(newStr)
                                                                newChainPair = addBlockAlt chain newStrAct 1 m--obtain new blockchain with added block
                                                                newChain = fst newChainPair
                                                                newBlock = snd newChainPair
                                                                sendStr = newStrAct ++ "+" ++ (show (block newBlock)) ++ "+" ++ (show (nonce newBlock)) ++ "+" ++ (bitsToStr (prevHash newBlock)) ++ "+" ++ (bitsToStr (hash newBlock)) --send message about added block to other processes
                                                            in do success <- sendToProcs sendStr sock addrs
                                                                  case success of
                                                                       False => pure (Just ("Unable to send message; did not add block\n", (Same m chain))) --if unable to send message, revert to original blockchain
                                                                       True => do consensus <- recvConf sock addrs True --otherwise, attempt to obtain consensus from other blocks
                                                                                  case consensus of
                                                                                       False => do sendToProcs "do not add" sock addrs --consensus not reached; send message about reverting to original blockchain
                                                                                                   pure (Just ("Consensus not reached; did not add block\n", (Same m chain)))
                                                                                       True => do sendToProcs "add" sock addrs --consensus reached; send message about switching to new blockchain
                                                                                                  pure (Just ("Consensus reached; added block\n", (Inc m newChain)))
--to initiate consensus protocol
executeCommandAlt {m} chain "receive" "" sock addrs _ = do received <- recvCont sock 2048 --receive message
                                                           let recvStr = fst (snd received) --bind info from received message to names
                                                           let senderInfo = fst received
                                                           let senderAddr = remote_addr senderInfo
                                                           let senderPort = remote_port senderInfo
                                                           case split (== '+') recvStr of
                                                                [newStr, blockNumStr, nonceStr, rightPHash, rightHash] => let nonceParse = parseInteger nonceStr
                                                                                                                          in case nonceParse of
                                                                                                                                  Nothing => do sendCont sock senderAddr senderPort "no" --message received was in wrong format; send denial to sender
                                                                                                                                                received2 <- recvFrom sock 2048
                                                                                                                                                pure (Just ("Incorrect format of message\n", (Same m chain))) -- revert to original blockchain
                                                                                                                                  Just rightNonce => let newChainPair = addBlockAlt chain newStr rightNonce m --obtain resultant blockchain from adding desired string and new added block
                                                                                                                                                         newBlock = snd newChainPair
                                                                                                                                                 --confirm that all fields of new block are identical to those of corresponding block in sender's blockchain
                                                                                                                                                 in do case ((rightHash == (bitsToStr (hash newBlock))) && ((rightPHash == (bitsToStr (prevHash newBlock))) && ((rightNonce == (nonce newBlock)) && (blockNumStr == (show (block newBlock)))))) of
                                                                                                                                                            False => do sendCont sock senderAddr senderPort "no" --if not, send denial to sender
                                                                                                                                                                        putStrLn ("Denying change")
                                                                                                                                                            True => do sendCont sock senderAddr senderPort "yes" --otherwise, send confirmation
                                                                                                                                                                       putStrLn ("Accepting change")
                                                                                                                                                       received1 <- recvCont sock 2048 --receive another message from original sender
                                                                                                                                                       let recvStr = fst (snd received1)
                                                                                                                                                       case recvStr of
                                                                                                                                                            "add" => pure (Just ("Implementing change\n", (Inc m (fst newChainPair)))) --if message was "add", switch to new blockchain
                                                                                                                                                            _ => pure (Just ("Discarding proposed change\n", (Same m chain))) --otherwise, revert to original blockchain
                                                                _ => do sendCont sock senderAddr senderPort "no" --message received was in wrong format; send denial to sender
                                                                        received3 <- recvFrom sock 2048
                                                                        pure (Just ("Incorrect format of message\n", (Same m chain))) -- revert to original blockchain
executeCommandAlt {m} chain "rock" commit sock addrs port = let lastBlock = getLastBlock chain --obtain last block of current chain
                                                            in do case lastBlock of
                                                                       Nothing => let genChain = addBlock chain "Genesis Block" m --chain is currently empty (should never happen); add genesis block
                                                                                  in pure (Just ("Genesis block not found", (Inc m genChain)))
                                                                       Just x => let lastStr = dataField x --otherwise, get datum field of last block
                                                                                 in do case split (== '*') lastStr of
                                                                                            [player, lastCommit, hashedPlay] => case (player == (show port)) of --last string has format of a RPS play, determine if current process made last play
                                                                                                                                     True => pure (Just ("Cannot play both sides of a game\n", (Same m chain))) --if so, disregared new play
                                                                                                                                     False => do play <- isPlay hashedPlay lastCommit --if not, confirm that last string does represent a RPS play
                                                                                                                                                 case (fst play) of
                                                                                                                                                      --last string added doesn't represent a RPS play, add specified play to blobkchain
                                                                                                                                                      False => let commitParse = parseInteger commit --determine if commit string represents an integer
                                                                                                                                                               in case commitParse of
                                                                                                                                                                       Nothing => pure (Just ("Commit value not an integer\n", (Same m chain))) --if not, revert to original blockchain
                                                                                                                                                                       Just commitInt => let playToInt = getIntRep (unpack "rock") 0 --otherwise, perform cryptographic hash of the specified string along with given commit value
                                                                                                                                                                                             playBits =  the (Bits 128) (intToBits playToInt)
                                                                                                                                                                                             commitBits = the (Bits 128) (intToBits commitInt)
                                                                                                                                                                                             playHash = hashMessage dummyMD5 [playBits, commitBits]
                                                                                                                                                                                             playHashStr = bitsToStr playHash --convert output bits back into string
                                                                                                                                                                                         in executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ commit ++ "*" ++ playHashStr) sock addrs port --add port number, commit value, and hashed string to blockchain
                                                                                                                                                      True => let winner = getWinner (snd play) 0 --a game was played, determine winner
                                                                                                                                                              in case winner of
                                                                                                                                                                      0 => executeCommandAlt chain "add" (" Players (" ++ player ++ ", " ++ (show port) ++ ") Tied") sock addrs port
                                                                                                                                                                      1 => executeCommandAlt chain "add" (" Player 1 (" ++ player ++ ") Won") sock addrs port
                                                                                                                                                                      2 => executeCommandAlt chain "add" (" Player 2 (" ++ (show port) ++ ") Won") sock addrs port
                                                                                                                                                                      _ => pure (Just ("Unable to determine winner\n", (Same m chain)))
                                                                                            _ => let commitParse = parseInteger commit
                                                                                                 in case commitParse of
                                                                                                         Nothing => pure (Just ("Commit value not an integer\n", (Same m chain)))
                                                                                                         Just commitInt => let playToInt = getIntRep (unpack "rock") 0
                                                                                                                               playBits =  the (Bits 128) (intToBits playToInt)
                                                                                                                               commitBits = the (Bits 128) (intToBits commitInt)
                                                                                                                               playHash = hashMessage dummyMD5 [playBits, commitBits]
                                                                                                                               playHashStr = bitsToStr playHash
                                                                                                                           in executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ commit ++ "*" ++ playHashStr) sock addrs port
executeCommandAlt {m} chain "paper" commit sock addrs port = let lastBlock = getLastBlock chain
                                                             in do case lastBlock of
                                                                        Nothing => let genChain = addBlock chain "Genesis Block" m --chain is currently empty (should never happen); add genesis block
                                                                                   in pure (Just ("Genesis block not found", (Inc m genChain)))
                                                                        Just x => let lastStr = dataField x
                                                                                  in do case split (== '*') lastStr of
                                                                                             [player, lastCommit, hashedPlay] => case (player == (show port)) of
                                                                                                                                      True => pure (Just ("Cannot play both sides of a game\n", (Same m chain)))
                                                                                                                                      False => do play <- isPlay hashedPlay lastCommit
                                                                                                                                                  case (fst play) of
                                                                                                                                                       False => let commitParse = parseInteger commit
                                                                                                                                                                in case commitParse of
                                                                                                                                                                        Nothing => pure (Just ("Commit value not an integer\n", (Same m chain)))
                                                                                                                                                                        Just commitInt => let playToInt = getIntRep (unpack "paper") 0
                                                                                                                                                                                              playBits =  the (Bits 128) (intToBits playToInt)
                                                                                                                                                                                              commitBits = the (Bits 128) (intToBits commitInt)
                                                                                                                                                                                              playHash = hashMessage dummyMD5 [playBits, commitBits]
                                                                                                                                                                                              playHashStr = bitsToStr playHash
                                                                                                                                                                                          in executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ commit ++ "*" ++ playHashStr) sock addrs port
                                                                                                                                                       True => let winner = getWinner (snd play) 1
                                                                                                                                                               in case winner of
                                                                                                                                                                       0 => executeCommandAlt chain "add" (" Players (" ++ player ++ ", " ++ (show port) ++ ") Tied") sock addrs port
                                                                                                                                                                       1 => executeCommandAlt chain "add" (" Player 1 (" ++ player ++ ") Won") sock addrs port
                                                                                                                                                                       2 => executeCommandAlt chain "add" (" Player 2 (" ++ (show port) ++ ") Won") sock addrs port
                                                                                                                                                                       _ => pure (Just ("Unable to determine winner\n", (Same m chain)))
                                                                                             _ => let commitParse = parseInteger commit
                                                                                                  in case commitParse of
                                                                                                          Nothing => pure (Just ("Commit value not an integer\n", (Same m chain)))
                                                                                                          Just commitInt => let playToInt = getIntRep (unpack "paper") 0
                                                                                                                                playBits =  the (Bits 128) (intToBits playToInt)
                                                                                                                                commitBits = the (Bits 128) (intToBits commitInt)
                                                                                                                                playHash = hashMessage dummyMD5 [playBits, commitBits]
                                                                                                                                playHashStr = bitsToStr playHash
                                                                                                                            in executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ commit ++ "*" ++ playHashStr) sock addrs port
executeCommandAlt {m} chain "scissors" commit sock addrs port = let lastBlock = getLastBlock chain
                                                                in do case lastBlock of
                                                                           Nothing => let genChain = addBlock chain "Genesis Block" m --chain is currently empty (should never happen); add genesis block
                                                                                      in pure (Just ("Genesis block not found", (Inc m genChain)))
                                                                           Just x => let lastStr = dataField x
                                                                                     in do case split (== '*') lastStr of
                                                                                                [player, lastCommit, hashedPlay] => case (player == (show port)) of
                                                                                                                                         True => pure (Just ("Cannot play both sides of a game\n", (Same m chain)))
                                                                                                                                         False => do play <- isPlay hashedPlay lastCommit
                                                                                                                                                     case (fst play) of
                                                                                                                                                          False => let commitParse = parseInteger commit
                                                                                                                                                                   in case commitParse of
                                                                                                                                                                           Nothing => pure (Just ("Commit value not an integer\n", (Same m chain)))
                                                                                                                                                                           Just commitInt => let playToInt = getIntRep (unpack "scissors") 0
                                                                                                                                                                                                 playBits =  the (Bits 128) (intToBits playToInt)
                                                                                                                                                                                                 commitBits = the (Bits 128) (intToBits commitInt)
                                                                                                                                                                                                 playHash = hashMessage dummyMD5 [playBits, commitBits]
                                                                                                                                                                                                 playHashStr = bitsToStr playHash
                                                                                                                                                                                             in executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ commit ++ "*" ++ playHashStr) sock addrs port
                                                                                                                                                          True => let winner = getWinner (snd play) 2
                                                                                                                                                                  in case winner of
                                                                                                                                                                          0 => executeCommandAlt chain "add" (" Players (" ++ player ++ ", " ++ (show port) ++ ") Tied") sock addrs port
                                                                                                                                                                          1 => executeCommandAlt chain "add" (" Player 1 (" ++ player ++ ") Won") sock addrs port
                                                                                                                                                                          2 => executeCommandAlt chain "add" (" Player 2 (" ++ (show port) ++ ") Won") sock addrs port
                                                                                                                                                                          _ => pure (Just ("Unable to determine winner\n", (Same m chain)))
                                                                                                _ => let commitParse = parseInteger commit
                                                                                                     in case commitParse of
                                                                                                             Nothing => pure (Just ("Commit value not an integer\n", (Same m chain)))
                                                                                                             Just commitInt => let playToInt = getIntRep (unpack "scissors") 0
                                                                                                                                   playBits =  the (Bits 128) (intToBits playToInt)
                                                                                                                                   commitBits = the (Bits 128) (intToBits commitInt)
                                                                                                                                   playHash = hashMessage dummyMD5 [playBits, commitBits]
                                                                                                                                   playHashStr = bitsToStr playHash
                                                                                                                               in executeCommandAlt chain "add" (" " ++ (show port) ++ "*" ++ commit ++ "*" ++ playHashStr) sock addrs port
executeCommandAlt chain command newStr _ _ _ = pure (executeCommand chain command newStr) -- all other commands executed by calling executeCommand

||| processes user input by calling executeCommand; used for single blockchain simulation
||| @chain the current blockchain
||| @input the user input string
partial
processInput : (chain : Vect m Block) -> (input : String) -> Maybe (String, VectSameOrInc Block)
processInput {m} chain input = case span (/= ' ') input of
                                    (command, newStr) => executeCommand chain command newStr

||| processes user input by calling executeCommand; used for distributed blockchain simulation
||| @chain the current blockchain
||| @input the user input string
||| @sock the current process's socket
||| @addrs a UDPAddrInfo Vector, where UDPAddrInfo is a record with address and port fields
||| @port the port the current process is bound to
partial
processInputAlt : (chain : Vect m Block) -> (input : String) -> (sock : Socket) -> (addrs : Vect n UDPAddrInfo) -> (port : Int) -> IO (Maybe (String, VectSameOrInc Block))
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
processInputLoop : (sock : Socket) -> (addrs : Vect m UDPAddrInfo) -> (chain : Vect n Block) -> (port : Int) -> (Process ProcessLib.clientType () NoRequest NoRequest)
processInputLoop {n} sock addrs chain port = do Action (putStr "Command: ") --prompt user for input
                                                command <- Action (getLine) --obtain input
                                                pInput <- Action (processInputAlt chain command sock addrs port) --process input by calling processInputAlt
                                                case pInput of
                                                     Nothing => RespondToEnd (\msg => Pure ()) --if user has specified "quit" command, respond to main Process to end program
                                                     Just x => do Action (putStr (fst x)) --otherwise, call new iteration of process
                                                                  case (snd x) of --obtain vector from VectSameOrInc
                                                                       (Same n vect) => LoopNoReq (processInputLoop sock addrs vect port) --if chain remained the same
                                                                       (Inc n vect) => LoopNoReq (processInputLoop sock addrs vect port) --if a new block was added
                                                                       _ => RespondToEnd (\msg => Pure ()) --an unexpected deletion of a block has occurred, end program

||| Process that simulates replWith loop; used for simple blockchain simulation
||| @chain the current blockchain
partial
processInputLoopSimp : (chain : Vect n Block) -> (Process ProcessLib.clientType () NoRequest NoRequest)
processInputLoopSimp {n} chain = do Action (putStr "Command: ")
                                    command <- Action (getLine)
                                    let pInput = processInput chain command --process input by calling processInput
                                    case pInput of
                                         Nothing => RespondToEnd (\msg => Pure ())
                                         Just x => do Action (putStr (fst x))
                                                      case (snd x) of
                                                           (Same n vect) => LoopNoReq (processInputLoopSimp vect)
                                                           (Inc n vect) => LoopNoReq (processInputLoopSimp vect)
                                                           _ => RespondToEnd (\msg => Pure ())

||| Main process; performs initialization of necessary variables and blockchain itself (adds genesis block)
||| @ ports a Vector of ints representing port numbers
partial
procMain : (ports : Vect n Int) -> (Process NoRecv () NoRequest NoRequest)
procMain [] = let genNumBits = the (Bits 128) (intToBits 0) --create
                  genStrToInt = getIntRep (unpack "Genesis Block") 0
                  genStrBits =  the (Bits 128) (intToBits genStrToInt)
                  foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
              in do Just loopPID <- SpawnClient (processInputLoopSimp [CreateBlock 0 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)]) --spawn processInputLoopSimp process (simple blockchain simulation)
                         | Nothing => Action (putStrLn "spawn failed") --if unable to spawn new process
                    RequestToWait loopPID 1 --wait for looping process to respond and finish
procMain [x] = Action (putStrLn "Must specify more than 1 port number") --ports Vector must have more than 1 element (or none)
procMain (x :: xs) = let myAddr = IPv4Addr 127 0 0 1 --create localhost IPv4 addr for this process
                         udpAddrVect = createAddrs xs --obtain UDPAddrInfo Vector based on specified Vector of port numbers
                         genNumBits = the (Bits 128) (intToBits 0) --create constructs needed to create genesis block
                         genStrToInt = getIntRep (unpack "Genesis Block") 0
                         genStrBits =  the (Bits 128) (intToBits genStrToInt)
                         foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
                     in do sock <- Action (socket AF_INET Datagram 0) -- initialize UDP socket
                           case sock of
                                Left l => Action (putStrLn "socket failed") --if socket creation was unsuccessful
                                Right r => do bindRet <- Action (bind r (Just myAddr) x) --otherwise, bind socket to this process's addr and port
                                              if (bindRet == 0)
                                                 then do Just loopPID <- SpawnClient (processInputLoop r udpAddrVect [CreateBlock 0 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)] x) --spawn processInputLoop process, passing bound socket (distributed blockchain simulation)
                                                              | Nothing => Action (putStrLn "spawn failed") --if unable to spawn new process
                                                         RequestToWait loopPID 1 --wait for looping process to respond and finish
                                                 else Action (putStrLn "bind failed") --if bind failed
