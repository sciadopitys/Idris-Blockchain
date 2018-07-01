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

addNode : Blockchain -> (newStr : String) -> Blockchain
addNode (CreateChain size chain) newStr = CreateChain (S size) (addToChain chain) where
    addToChain : Vect curSize Node -> Vect (S curSize) Node
    addToChain [x] = let curNumBits = the (Bits 128) (intToBits (toIntegerNat (S size)))
                         newStrCharList = unpack newStr
                         newStrToInt = getIntRep newStrCharList 0
                         newStrBits =  the (Bits 128) (intToBits newStrToInt)
                         foundPair = findNonceAndHash curNumBits newStrBits 1 (hash x)
                     in x :: [CreateNode (S size) (fst foundPair) newStr (hash x) (snd foundPair)]
    addToChain (x :: xs) = x :: addToChain xs

display : Blockchain -> String
display (CreateChain size chain) = displayChain chain where
    displayChain : Vect size1 Node -> String
    displayChain [] = "\n"
    displayChain (x :: xs) = show x ++ "\n" ++ displayChain xs

executeCommand : (chain : Blockchain) -> (command : String) -> (newStr : String) -> Maybe (String, Blockchain)
executeCommand chain "add" newStr = Just ("Added new node\n", addNode chain (strTail(newStr)))
executeCommand chain "display" "" = Just ((display chain), chain)
executeCommand chain "quit" "" = Nothing
executeCommand chain _ _ = Just ("Invalid command\n", chain)

processInput : Blockchain -> String -> Maybe (String, Blockchain)
processInput chain input = case span (/= ' ') input of
                                (command, newStr) => executeCommand chain command newStr

createAddrs : Vect n Int -> Vect n UDPAddrInfo
createAddrs [] = []
createAddrs (x :: xs) = let curAddr = IPv4Addr 127 0 0 1
                        in (MkUDPAddrInfo curAddr x) :: createAddrs xs

receiver : Socket -> PID -> (Process ProcessLib.receiverType () NoRequest Complete)
receiver sock pid = do received <- Action (recvFrom sock _)
                       case received of
                            Left l => Loop2 (receiver sock pid)
                            Right r => do (Respond pid (\msg => Pure (fst (snd r))))
                                          Loop (receiver sock pid)

spawnProcesses : Vect n UDPAddrInfo -> Socket -> PID -> IO ()
spawnProcesses [] sock myPid = pure ()
spawnProcesses (x :: xs) sock myPid = do pid <- spawn (do run forever (receiver sock myPid)
                                                          pure ())
                                         spawnProcesses xs sock myPid

procMain : Vect n Int -> (Process NoRecv () NoRequest NoRequest)
procMain [] = let genNumBits = the (Bits 128) (intToBits 1)
                  genStrToInt = getIntRep (unpack "Genesis Block") 0
                  genStrBits =  the (Bits 128) (intToBits genStrToInt)
                  foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
              in Action (replWith (CreateChain 1 [CreateNode 1 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)]) "Command: " processInput)
procMain [x] = Action (putStrLn "Must specify more than 1 port number")
procMain (x :: xs) = let myAddr = IPv4Addr 127 0 0 1
                         udpAddrVect = createAddrs xs
                         myPid = the (PID) ?getPID
                     in do sock <- Action (socket AF_INET Datagram 0)
                           case sock of
                                Left l => Action (putStrLn "socket failed")
                                Right r => do bindRet <- Action (bind r (Just myAddr) x)
                                              if (bindRet == 0)
                                                 then do Action (spawnProcesses udpAddrVect r myPid)
                                                 else Action (putStrLn "bind failed")
