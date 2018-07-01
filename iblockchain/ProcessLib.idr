module ProcessLib

import System.Concurrency.Channels

%default total

data Message = Add Nat Nat

public export
data Fuel = Empty | More (Lazy Fuel)

export partial
forever : Fuel
forever = More forever

AdderType : Message -> Type
AdderType (Add k j) = Nat

public export
receiverType : Int -> Type
receiverType x = String

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
     Request : (msg : service_reqType) -> Process iface String st st
     Respond : PID -> ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) -> Process iface (Maybe reqType) st Sent
     Loop : Inf (Process iface a NoRequest Complete) -> Process iface a Sent Complete
     Loop2 : Inf (Process iface a NoRequest Complete) -> Process iface a NoRequest Complete

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
run (More fuel) (Loop act) = run fuel act
run (More fuel) (Loop2 act) = run fuel act
run fuel (Request msg) = do Just channel <- listen 1 | _ => pure Nothing
                            ok <- unsafeSend channel msg
                            if ok then do Just x <- unsafeRecv String channel | Nothing => pure Nothing
                                          pure (Just x)
                                  else pure Nothing
run fuel (Respond {reqType} process f) = do Just sender <- connect process | Nothing => pure (Just Nothing)
                                            Just msg <- unsafeRecv reqType sender | Nothing => pure (Just Nothing)
                                            Just response <- run fuel (f msg) | Nothing => pure Nothing
                                            unsafeSend sender response
                                            pure (Just (Just msg))

adder : Service AdderType ()
{-adder = do Respond (\msg => case msg of
                                 Add x y => Pure (x + y))
           Loop adder-}

procMain : Client ()
procMain = do Just adder_id <- Spawn adder | Nothing => Action (putStrLn "Spawn failed")
              answer <- Request (Add 2 3)
              Action (printLn answer)

export partial
runProc : Process iface () ist ost -> IO ()
runProc process = do run forever process
                     pure ()
