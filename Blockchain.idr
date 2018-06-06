import Data.Vect

record Node where
       constructor CreateNode
       node : Nat
       nonce : Int
       dataField : String
       --prevHash :
       --hash :

record Blockchain where
       constructor CreateChain
       size : Nat
       chain : Vect size Node

executeCommand : (chain : Blockchain) -> (command : String) -> (newStr : String) -> Maybe (String, Blockchain)
executeCommand chain "add" newStr = ?executeCommand_rhs
executeCommand chain "display" "" = ?executerhs2
executeCommand chain "quit" "" = Nothing
executeCommand chain _ _ = Just ("Invalid command\n", chain)

processInput : Blockchain -> String -> Maybe (String, Blockchain)
processInput chain input = case span (/= ' ') input of
                                (command, newStr) => executeCommand chain command newStr

main : IO ()
main = replWith (CreateChain 1 [CreateNode 1 ?findNonce "Genesis Block"] ) "Command: " processInput
