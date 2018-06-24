module BlockchainMain

import Data.Vect
import Data.Bits
import ProcessLib
import Network.Socket
import src.Data.Crypto.Hash.MD5
import src.Data.Crypto.Hash

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

findNonceAndHash : (nodeNum : Nat) -> (datum : String) -> (curNonce : Integer) -> (prevHash: Bits 128) -> (Integer, Bits 128)
findNonceAndHash nodeNum datum curNonce prevHash = let nodeNumBits = the (Bits 128) (intToBits (toIntegerNat nodeNum))
                                                       nonceBits =  the (Bits 128) (intToBits curNonce)
                                                       datumCharList = unpack datum
                                                       datumToInt = getIntRep datumCharList 0
                                                       datumBits =  the (Bits 128) (intToBits datumToInt)
                                                       message = the (Vect 4 (Bits 128)) [nodeNumBits, nonceBits, datumBits, prevHash]
                                                       curHash = hashMessage ?rhs2 message
                                                       in case bitsToInt curHash <= 9999999999999999 of
                                                               False => findNonceAndHash nodeNum datum (S curNonce) prevHash
                                                               True => (curNonce, curHash)

addNode : Blockchain -> (newStr : String) -> Blockchain
addNode (CreateChain size chain) newStr = CreateChain (S size) (addToChain chain) where
    addToChain : Vect curSize Node -> Vect (S curSize) Node
    addToChain [x] = let foundPair = findNonceAndHash (S size) newStr 1 (prevHash x)
                     in x :: [CreateNode (S size) (fst foundPair) newStr (prevHash x) (snd foundPair)]
    addToChain (x :: xs) = x :: addToChain xs

display : Blockchain -> String
display (CreateChain size chain) = displayChain chain where
    displayChain : Vect size1 Node -> String
    displayChain [] = "Error: Empty Blockchain"
    displayChain (x :: xs) = show x ++ "\n" ++ displayChain xs

executeCommand : (chain : Blockchain) -> (command : String) -> (newStr : String) -> Maybe (String, Blockchain)
executeCommand chain "add" newStr = Just ("Added new node\n", addNode chain newStr)
executeCommand chain "display" "" = Just ((display chain), chain)
executeCommand chain "quit" "" = Nothing
executeCommand chain _ _ = Just ("Invalid command\n", chain)

processInput : Blockchain -> String -> Maybe (String, Blockchain)
processInput chain input = case span (/= ' ') input of
                                (command, newStr) => executeCommand chain command newStr

{-bindSock : Socket -> SocketAddress -> Int -> IO Int
bindSock (Left l) _ _ = pure (-1)
bindSock (Right r) addr portNum = bind r (Just addr) portNum-}

initSockets : Vect n Int -> Vect n ((Maybe Socket), SocketAddress)
initSockets [] = []
initSockets (x :: xs) = let curAddr = IPv4Addr 127 0 0 1
                        in do curSocket <- socket AF_INET Datagram 0
                              case curSocket of
                                   (Left l) => (Nothing, curAddr) :: initSockets xs
                                   (Right r) => bind r (Just curAddr) x
                                                (r, curAddr) :: initSockets xs


procMain : Vect n Int -> (Process NoRecv () NoRequest NoRequest)
procMain [] = let foundPair = findNonceAndHash 1 "Genesis Block" 1 (intToBits 0)
              in Action (replWith (CreateChain 1 [CreateNode 1 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)]) "Command: " processInput)
procMain (x :: xs) = let portList = initSockets (x :: xs)
                         foundPair = findNonceAndHash 1 "Genesis Block" 1 (intToBits 0)
                     in Action (replWith (CreateChain 1 [CreateNode 1 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)]) "Command: " processInput)
