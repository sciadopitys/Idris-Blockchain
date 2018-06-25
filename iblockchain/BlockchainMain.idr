module BlockchainMain

import Data.Vect
import Data.Bits
import ProcessLib
import Data.Fin
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

findNonceAndHash : (nodeNumBits : Bits 128) -> (datumBits : Bits 128) -> (curNonce : Integer) -> (prevHash: Bits 128) -> (Integer, Bits 128)
findNonceAndHash nodeNumBits datumBits curNonce prevHash = let nonceBits =  the (Bits 128) (intToBits curNonce)
                                                               message = the (Vect 4 (Bits 128)) [nodeNumBits, nonceBits, datumBits, prevHash]
                                                               curHash = hashMessage dummyMD5 message
                                                           in case bitsToInt curHash <= 9999999999999999 of
                                                                   False => findNonceAndHash nodeNumBits datumBits (curNonce + 1) prevHash
                                                                   True => (curNonce, curHash)

addNode : Blockchain -> (newStr : String) -> Blockchain
addNode (CreateChain size chain) newStr = CreateChain (S size) (addToChain chain) where
    addToChain : Vect curSize Node -> Vect (S curSize) Node
    addToChain [x] = let curNumBits = the (Bits 128) (intToBits (toIntegerNat (S size)))
                         newStrCharList = unpack newStr
                         newStrToInt = getIntRep newStrCharList 0
                         newStrBits =  the (Bits 128) (intToBits newStrToInt)
                         foundPair = findNonceAndHash curNumBits newStrBits 1 (prevHash x)
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

initSockets : Vect n Int -> List (Socket, SocketAddress)
{-initSockets [] = []
initSockets (x :: xs) = let curAddr = IPv4Addr 127 0 0 1
                        in do curSocket <- socket AF_INET Datagram 0
                              case curSocket of
                                   (Left l) => initSockets xs
                                   (Right r) => bind r (Just curAddr) x
                                                (r, curAddr) :: initSockets xs-}


procMain : Vect n Int -> (Process NoRecv () NoRequest NoRequest)
procMain [] = let genNumBits = the (Bits 128) (intToBits 1)
                  genStrToInt = getIntRep (unpack "Genesis Block") 0
                  genStrBits =  the (Bits 128) (intToBits genStrToInt)
                  foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
              in Action (replWith (CreateChain 1 [CreateNode 1 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)]) "Command: " processInput)
procMain (x :: xs) = let portList = initSockets (x :: xs)
                         genNumBits = the (Bits 128) (intToBits 1)
                         genStrToInt = getIntRep (unpack "Genesis Block") 0
                         genStrBits =  the (Bits 128) (intToBits genStrToInt)
                         foundPair = findNonceAndHash genNumBits genStrBits 1 (intToBits 0)
                     in Action (replWith (CreateChain 1 [CreateNode 1 (fst foundPair) "Genesis Block" (intToBits 0) (snd foundPair)]) "Command: " processInput)
