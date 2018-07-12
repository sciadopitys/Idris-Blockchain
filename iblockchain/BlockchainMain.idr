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
  show (CreateNode node nonce dataField prevHash hash) = "\nNode #: " ++ show node ++ "\nNonce: " ++ show nonce ++ "\nData: " ++ show dataField ++ "\nPrevious Hash: " ++ show prevHash ++ "\nHash: " ++ show hash

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

addNodeAlt : Blockchain -> String -> Integer -> (Blockchain, (Integer, Bits 128))
addNodeAlt (CreateChain size chain) newStr start = let foundPair1 = addToChain chain start
                                                   in ((CreateChain (S size) (fst foundPair1)), (snd foundPair1)) where
                                                       addToChain : (Vect n Node) -> Integer -> ((Vect (S n) Node), (Integer, Bits 128))
                                                       addToChain [last] y = let curNumBits = the (Bits 128) (intToBits (toIntegerNat (S size)))
                                                                                 newStrCharList = unpack newStr
                                                                                 newStrToInt = getIntRep newStrCharList 0
                                                                                 newStrBits =  the (Bits 128) (intToBits newStrToInt)
                                                                                 foundPair = findNonceAndHash curNumBits newStrBits y (hash last)
                                                                              in ((last :: [CreateNode (S size) (fst foundPair) newStr (hash last) (snd foundPair)]), foundPair)
                                                       addToChain (x :: xs) y = ((x :: (fst (addToChain xs y))), (snd (addToChain xs y)))

addNode : Blockchain -> String -> Blockchain
addNode chain newStr = fst (addNodeAlt chain newStr 1)

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
                                  Left l => do pure False
                                  Right r => case (fst (snd r)) of
                                                  "yes" => do putStrLn "Acceptance received"
                                                              recvConf sock xs
                                                  _ => do putStrLn "Denial received"
                                                          pure False

executeCommand : (chain : Blockchain) -> (command : String) -> (newStr : String) -> Maybe (String, Blockchain)
executeCommand chain "add" newStr = Just ("Added new node\n", addNode chain (strTail(newStr)))
executeCommand chain "display" "" = Just ((display chain), chain)
executeCommand chain "quit" "" = Nothing
executeCommand chain _ _ = Just ("Invalid command\n", chain)

executeCommandAlt : (chain : Blockchain) -> (command : String) -> (newStr : String) -> (sock : Socket) -> (addrs : Vect n UDPAddrInfo) -> IO (Maybe (String, Blockchain))
executeCommandAlt chain "add" newStr sock addrs = let newStrAct = strTail(newStr)
                                                      newChain = addNodeAlt chain newStrAct 1
                                                      foundPair = snd newChain
                                                      sendStr = newStrAct ++ "+" ++ (show (fst foundPair)) ++ "+" ++ (bitsToStr (snd foundPair))
                                                  in do success <- sendToProcs sendStr sock addrs
                                                        case success of
                                                             False => pure (Just ("Unable to send message; did not add node\n", chain))
                                                             True => do consensus <- recvConf sock addrs
                                                                        case consensus of
                                                                             False => do sendToProcs "do not add" sock addrs
                                                                                         pure (Just ("Consensus not reached; did not add node\n", chain))
                                                                             True => do sendToProcs "add" sock addrs
                                                                                        pure (Just ("Consensus reached; added node\n", (fst newChain)))

executeCommandAlt chain "receive" "" sock addrs = do received <- recvFrom sock 2048
                                                     case received of
                                                          Left l => pure (Just ("Unable to receive message\n", chain))
                                                          Right r => let recvStr = fst (snd r)
                                                                         senderInfo = fst r
                                                                         senderAddr = remote_addr senderInfo
                                                                         senderPort = remote_port senderInfo
                                                                     in case split (== '+') recvStr of
                                                                             [newStr, nonceStr, hash] => let Just nonce = parseInteger nonceStr
                                                                                                             newChain = addNodeAlt chain newStr nonce
                                                                                                         in do case (hash == (bitsToStr (snd (snd newChain)))) of
                                                                                                                    False => do success <- sendTo sock senderAddr senderPort "no"
                                                                                                                                putStrLn ("Denying change")
                                                                                                                    True => do success <- sendTo sock senderAddr senderPort "yes"
                                                                                                                               putStrLn ("Accepting change")
                                                                                                               received1 <- recvFrom sock 2048
                                                                                                               case received1 of
                                                                                                                    Left l1 => pure (Just ("Unable to receive message\n", chain))
                                                                                                                    Right r1 => let recvStr = fst (snd r1)
                                                                                                                                in case recvStr of
                                                                                                                                        "add" => pure (Just ("Implementing change\n", (fst newChain)))
                                                                                                                                        _ => pure (Just ("Discarding proposed change\n", chain))
                                                                             _ => do sendTo sock senderAddr senderPort "no"
                                                                                     pure (Just ("Denying change\n", chain))
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

processInputLoop : Socket -> Vect n UDPAddrInfo -> Blockchain -> (Process ProcessLib.clientType () NoRequest NoRequest)
processInputLoop sock addrs chain = do Action (putStr "Command: ")
                                       command <- Action (getLine)
                                       pInput <- Action (processInputAlt chain command sock addrs)
                                       case pInput of
                                            Nothing => RespondToEnd (\msg => Pure ())
                                            Just x => do Action (putStr (fst x))
                                                         LoopNoReq (processInputLoop sock addrs (snd x))

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
                                                         RequestToWait loopPID 1
                                                 else Action (putStrLn "bind failed")
