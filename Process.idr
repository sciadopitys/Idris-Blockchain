module ProcessLib

import System.Concurrency.Channels

%default total

data Message = Add Nat Nat

public export
data Fuel = Empty | More (Lazy Fuel)

export partial
forever : Fuel
forever = More forever

{-adder: IO ()
adder = do Just sender_channel <- listen 1 | Nothing => adder
           Just msg <- unsafeRecv Message sender_channel | Nothing => adder
           case msg of
                 Add k j => do ok <- unsafeSend sender_channel (k + j)
                               adder

main : IO ()
main = do Just adder_id <- spawn adder | Nothing => putStrLn "Spawn failed"
          Just channel <- connect adder_id | Nothing => putStrLn "Connection failed"
          ok <- unsafeSend channel (Add 2 3)
          Just answer <- unsafeRecv Nat channel | Nothing => putStrLn "Send/Recv failed"
          printLn answer-}
AdderType : Message -> Type
AdderType (Add k j) = Nat

public export
NoRecv : Void -> Type
NoRecv = const Void

export
data MessagePID : (iface : reqType -> Type) -> Type where
     MkMessage : PID -> MessagePID iface

public export
data ProcState = NoRequest | Sent | Complete

public export
data Process : (iface : reqType -> Type) -> Type -> (inState : ProcState) -> (outState : ProcState) -> Type where
     Action : IO a -> Process iface a st st
     Pure : a -> Process iface a st st
     (>>=) : Process iface a st1 st2 -> (a -> Process iface b st2 st3) -> Process iface b st1 st3
     Spawn : Process service_iface () NoRequest Complete -> Process iface (Maybe (MessagePID service_iface)) st st
     Request : MessagePID service_iface -> (msg : service_reqType) -> Process iface (service_iface msg) st st
     Respond : ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) -> Process iface (Maybe reqType) st Sent
     Loop : Inf (Process iface a NoRequest Complete) -> Process iface a Sent Complete

public export
Service : (iface : reqType -> Type) -> Type -> Type
Service iface a = Process iface a NoRequest Complete

public export
Client : Type -> Type
Client a = Process NoRecv a NoRequest NoRequest

export
run : Fuel -> Process iface ptype ist ost -> IO (Maybe ptype)
run Empty _ = pure Nothing
run fuel (Action act) = do result <- act
                           pure (Just result)
run fuel (Pure val) = pure (Just val)
run fuel (act >>= next) = do Just x <- run fuel act | Nothing => pure Nothing
                             run fuel (next x)
run fuel (Spawn process) = do Just pid <- spawn (do run fuel process
                                                    pure ())
                                   | Nothing => pure Nothing
                              pure (Just (Just (MkMessage pid)))
run fuel (Request {service_iface} (MkMessage process) msg) = do Just channel <- connect process | _ => pure Nothing
                                                                ok <- unsafeSend channel msg
                                                                if ok then do Just x <- unsafeRecv (service_iface msg) channel | Nothing => pure Nothing
                                                                              pure (Just x)
                                                                else pure Nothing
run fuel (Respond {reqType} f) = do Just sender <- listen 1 | Nothing => pure (Just Nothing)
                                    Just msg <- unsafeRecv reqType sender | Nothing => pure (Just Nothing)
                                    Just response <- run fuel (f msg) | Nothing => pure Nothing
                                    unsafeSend sender response
                                    pure (Just (Just msg))
run (More fuel) (Loop act) = run fuel act

adder : Service AdderType ()
adder = do Respond (\msg => case msg of
                                 Add x y => Pure (x + y))
           Loop adder

procMain : Client ()
procMain = do Just adder_id <- Spawn adder | Nothing => Action (putStrLn "Spawn failed")
              answer <- Request adder_id (Add 2 3)
              Action (printLn answer)

export partial
runProc : Process iface () ist ost -> IO ()
runProc process = do run forever process
                     pure ()
