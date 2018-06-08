import Data.Vect

%default total

record Node where
       constructor CreateNode
       node : Nat
       nonce : Int
       dataField : String
       --prevHash :
       --hash :

Show Node where
  show (CreateNode node nonce dataField) = "Node #: " ++ show node ++ "\nNonce: " ++ show nonce ++ "\nData: " ++ show dataField ++ "\n"


record Blockchain where
       constructor CreateChain
       size : Nat
       chain : Vect size Node

findNonce : (nodeNum : Nat) -> (datum : String) -> (curNonce : Int) -> Int

addNode : Blockchain -> (newStr : String) -> Blockchain
addNode (CreateChain size chain) newStr = CreateChain (S size) (addToChain chain) where
    addToChain : Vect curSize Node -> Vect (S curSize) Node
    addToChain [] = [CreateNode (S size) (findNonce (S size) newStr 1) newStr]
    addToChain (x :: xs) = x :: addToChain xs

displayChain : Vect size Node -> String
displayChain [] = "Error: Empty Blockchain"
displayChain (x :: xs) = show x ++ displayChain xs

display : Blockchain -> String
display (CreateChain size chain) = displayChain chain

executeCommand : (chain : Blockchain) -> (command : String) -> (newStr : String) -> Maybe (String, Blockchain)
executeCommand chain "add" newStr = Just ("Added new node\n", addNode chain newStr)
executeCommand chain "display" "" = Just ((display chain), chain)
executeCommand chain "quit" "" = Nothing
executeCommand chain _ _ = Just ("Invalid command\n", chain)

processInput : Blockchain -> String -> Maybe (String, Blockchain)
processInput chain input = case span (/= ' ') input of
                                (command, newStr) => executeCommand chain command newStr

main : IO ()
main = replWith (CreateChain 1 [CreateNode 1 ((findNonce 1 "Genesis Block" 1)) "Genesis Block"]) "Command: " processInput
