module BlockchainMain

import Data.Vect
import Data.Bits
import ProcessLib
import Data.Fin
import System.Concurrency.Channels
import Network.Socket
import Data.Crypto.Hash.MD5
import Data.Crypto.Hash

record Node where
       constructor CreateNode
       node : Nat
       nonce : Integer
       dataField : String
       prevHash : Bits 128
       hash : Bits 128

Show Node where
  show (CreateNode node nonce dataField prevHash hash) = "Node #: " ++ show node ++ "\nNonce: " ++ show nonce ++ "\nData: " ++ show dataField ++ "\n" ++ "\nPrevious Hash: " ++ show prevHash ++ "\nHash: " ++ show hash

record Blockchain where
       constructor CreateChain
       size : Nat
       chain : Vect size Node

getIntRep : List Char -> (acc : Int) -> Integer
getIntRep [] acc = the Integer (cast acc)
getIntRep (x :: xs) acc = getIntRep xs (acc + (ord x))

findNonceAndHash : (nodeNumBits : Bits 128) -> (datumBits : Bits 128) -> (curNonce : Integer) -> (prev: Bits 128) -> (Integer, Bits 128)
findNonceAndHash nodeNumBits datumBits curNonce prev = let nonceBits =  the (Bits 128) (intToBits curNonce)
                                                           message = the (Vect 4 (Bits 128)) [nodeNumBits, nonceBits, datumBits, prev]
                                                           curHash = hashMessage dummyMD5 message
                                                       in case ((bitsToInt curHash) <= 99999999999) of
                                                               False => findNonceAndHash nodeNumBits datumBits (curNonce + 1) prev
                                                               True => (curNonce, curHash)

addNodeAlt : Blockchain -> (newStr : String) -> (Blockchain, Bits 128)
addNodeAlt (CreateChain size chain) newStr = let foundPair1 = addToChain chain
                                             in ((CreateChain (S size) (fst foundPair1)), (snd foundPair1)) where
    addToChain : Vect curSize Node -> ((Vect (S curSize) Node), Bits 128)
    addToChain [x] = let curNumBits = the (Bits 128) (intToBits (toIntegerNat (S size)))
                         newStrCharList = unpack newStr
                         newStrToInt = getIntRep newStrCharList 0
                         newStrBits =  the (Bits 128) (intToBits newStrToInt)
                         foundPair = findNonceAndHash curNumBits newStrBits 1 (hash x)
                         newHash = snd foundPair
                     in ((x :: [CreateNode (S size) (fst foundPair) newStr (hash x) newHash]), newHash)
    addToChain (x :: xs) = ((x :: (fst (addToChain xs))), (snd (addToChain xs)))

addNode : Blockchain -> String -> Blockchain
addNode chain newStr = fst (addNodeAlt chain newStr)

display : Blockchain -> String
display (CreateChain size chain) = displayChain chain where
    displayChain : Vect size1 Node -> String
    displayChain [] = "\n"
    displayChain (x :: xs) = show x ++ "\n" ++ displayChain xs

sendToProcs : String -> Socket -> Vect n UDPAddrInfo -> (IO Bool)
sendToProcs str sock [] = pure True
sendToProcs str sock (x :: xs) = do success <- sendTo sock (remote_addr x) (remote_port x) str
                                    case success of
                                         Left l => pure False
                                         Right r => sendToProcs str sock xs

recvConf : Socket -> Vect n UDPAddrInfo -> (IO Bool)
recvConf sock [] = pure True
recvConf sock (x :: xs) = do received <- recvFrom sock 2048
                             case received of
                                  Left l => pure False
                                  Right r => case (fst (snd r)) of
                                                  "yes" => recvConf sock xs
                                                  _ => pure False

executeCommand : (chain : Blockchain) -> (command : String) -> (newStr : String) -> Maybe (String, Blockchain)
executeCommand chain "add" newStr = Just ("Added new node\n", addNode chain (strTail(newStr)))
executeCommand chain "display" "" = Just ((display chain), chain)
executeCommand chain "quit" "" = Nothing
executeCommand chain _ _ = Just ("Invalid command\n", chain)

executeCommandAlt : (chain : Blockchain) -> (command : String) -> (newStr : String) -> (sock : Socket) -> (addrs : Vect n UDPAddrInfo) -> IO (Maybe (String, Blockchain))
executeCommandAlt chain "add" newStr sock addrs = let newStrAct = strTail(newStr)
                                                      newChain = addNodeAlt chain newStrAct
                                                  in do success <- sendToProcs (newStrAct ++ "+" ++ (bitsToStr (snd newChain))) sock addrs
                                                        case success of
                                                             False => pure (Just ("Unable to send message; did not add node\n", chain))
                                                             True => do consensus <- recvConf sock addrs
                                                                        case consensus of
                                                                             False => pure (Just ("Consensus not reached; did not add node\n", chain))
                                                                             True => pure (Just ("Consensus reached; added node", (fst newChain)))

executeCommandAlt chain "update" _ _ _ = pure (Just ("Attempting to sync chains\n", chain))
executeCommandAlt chain command newStr _ _ = pure (executeCommand chain command newStr)

processInput : Blockchain -> String -> Maybe (String, Blockchain)
processInput chain input = case span (/= ' ') input of
                                (command, newStr) => executeCommand chain command newStr

processInputAlt : Blockchain -> String -> Socket -> Vect n UDPAddrInfo -> IO (Maybe (String, Blockchain))
processInputAlt chain input sock addrs = case span (/= ' ') input of
                                              (command, newStr) => executeCommandAlt chain command newStr sock addrs

createAddrs : Vect n Int -> Vect n UDPAddrInfo
createAddrs [] = []
createAddrs (x :: xs) = let curAddr = IPv4Addr 127 0 0 1
                        in (MkUDPAddrInfo curAddr x) :: createAddrs xs

receiver : Socket -> PID -> (Process ProcessLib.receiverType () NoRequest Complete)
receiver sock pid = do received <- Action (recvFrom sock 2048)
                       case received of
                            Left l => LoopFail (receiver sock pid)
                            Right r => do (Respond pid (\msg => Pure ((fst r), (fst (snd r)))))
                                          Loop (receiver sock pid)

spawnProcesses : Vect n UDPAddrInfo -> Socket -> PID -> IO ()
spawnProcesses [] sock myPid = pure ()
spawnProcesses (x :: xs) sock myPid = do pid <- spawn (do run forever (receiver sock myPid)
                                                          pure ())
                                         spawnProcesses xs sock myPid

processInputLoop : Socket -> Vect n UDPAddrInfo -> Blockchain -> (Process ProcessLib.clientType () NoRequest NoRequest)
processInputLoop sock addrs chain = do foundPair <- Request 1
                                       let addedStr = snd foundPair
                                       let senderInfo = fst foundPair
                                       if ((length addedStr) == 0)
                                          then do Action (putStr "Command: ")
                                                  command <- Action (getLine)
                                                  pInput <- Action (processInputAlt chain command sock addrs)
                                                  case pInput of
                                                       Nothing => RespondToEnd (\msg => Pure ())
                                                       Just x => do Action (putStr (fst x))
                                                                    LoopNoReq (processInputLoop sock addrs (snd x))
                                          else case split (== '+') addedStr of
                                                    [newStr, hash] => let newChain = addNodeAlt chain newStr
                                                                      in case (hash == (bitsToStr (snd newChain))) of
                                                                              False => do Action (sendTo sock (remote_addr senderInfo) (remote_port senderInfo) "no")
                                                                                          LoopNoReq (processInputLoop sock addrs chain)
                                                                              True => do Action (sendTo sock (remote_addr senderInfo) (remote_port senderInfo) "yes")
                                                                                         LoopNoReq (processInputLoop sock addrs (fst newChain))
                                                    _ => do Action (sendTo sock (remote_addr senderInfo) (remote_port senderInfo) "no")
                                                            LoopNoReq (processInputLoop sock addrs chain)

{-infLoop : Int -> IO ()
infLoop x = infLoop (1 + x)-}

procMain : Vect n Int -> (Process NoRecv () NoRequest NoRequest)
procMain [] = let genNumBits = the (Bits 128) (intToBits 1)
                  genStrToInt = getIntRep (unpack "Genesis Block") 0
                  genStrBits =  the (Bits 128) (intToBits genStrToInt)
                  foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
              in Action (replWith (CreateChain 1 [CreateNode 1 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)]) "Command: " processInput)
procMain [x] = Action (putStrLn "Must specify more than 1 port number")
procMain (x :: xs) = let myAddr = IPv4Addr 127 0 0 1
                         udpAddrVect = createAddrs xs
                         genNumBits = the (Bits 128) (intToBits 1)
                         genStrToInt = getIntRep (unpack "Genesis Block") 0
                         genStrBits =  the (Bits 128) (intToBits genStrToInt)
                         foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
                     in do sock <- Action (socket AF_INET Datagram 0)
                           case sock of
                                Left l => Action (putStrLn "socket failed")
                                Right r => do bindRet <- Action (bind r (Just myAddr) x)
                                              if (bindRet == 0)
                                                 then do Just loopPID <- SpawnClient (processInputLoop r udpAddrVect (CreateChain 1 [CreateNode 1 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)]))
                                                              | Nothing => Action (putStrLn "spawn failed")
                                                         Action (spawnProcesses udpAddrVect r loopPID)
                                                         --Action (infLoop 0)
                                                 else Action (putStrLn "bind failed")
