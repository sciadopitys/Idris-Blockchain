module ProcessLib

import System.Concurrency.Channels
import Network.Socket

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
receiverType x = (UDPAddrInfo, String)

public export
clientType : Int -> Type
clientType x = ()

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
     Spawn : Process service_iface () NoRequest Complete -> Process iface (Maybe PID) st st
     SpawnClient : Process service_iface () NoRequest NoRequest -> Process iface (Maybe PID) st st
     Request : (msg : service_reqType) -> Process iface (UDPAddrInfo, String) st st
     RequestToWait : PID -> (msg : service_reqType) -> Process iface () st st
     Respond : PID -> ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) -> Process iface (Maybe ()) st Sent
     RespondToEnd : ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) -> Process iface () st st
     Loop : Inf (Process iface a NoRequest Complete) -> Process iface a Sent Complete
     LoopFail : Inf (Process iface a NoRequest Complete) -> Process iface a NoRequest Complete
     LoopNoReq : Inf (Process iface a NoRequest NoRequest) -> Process iface a NoRequest NoRequest

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
                              pure (Just (Just pid))
run fuel (SpawnClient process) = do Just pid <- spawn (do run fuel process
                                                          pure ())
                                         | Nothing => pure Nothing
                                    pure (Just (Just pid))
run (More fuel) (Loop act) = run fuel act
run (More fuel) (LoopFail act) = run fuel act
run (More fuel) (LoopNoReq act) = run fuel act
run fuel (Request msg) = do Just channel <- listen 1 | _ => pure (Just ((MkUDPAddrInfo InvalidAddress 0), ""))
                            ok <- unsafeSend channel msg
                            if ok then do Just x <- unsafeRecv (UDPAddrInfo, String) channel | Nothing => pure (Just ((MkUDPAddrInfo InvalidAddress 0), ""))
                                          pure (Just x)
                                  else pure (Just ((MkUDPAddrInfo InvalidAddress 0), ""))
run fuel (RequestToWait process msg) = do Just channel <- connect process | _ => do pure Nothing
                                          ok <- unsafeSend channel msg
                                          if ok then do Just x <- unsafeRecv () channel | Nothing => do pure Nothing
                                                        pure (Just ())
                                                else do pure Nothing
run fuel (Respond {reqType} process f) = do Just sender <- connect process | Nothing => pure (Just Nothing)
                                            Just msg <- unsafeRecv reqType sender | Nothing => pure (Just Nothing)
                                            Just response <- run fuel (f msg) | Nothing => pure Nothing
                                            unsafeSend sender response
                                            pure (Just (Just ()))
run fuel (RespondToEnd {reqType} f) = do Just sender <- listen 1 | Nothing => pure Nothing
                                         Just msg <- unsafeRecv reqType sender | Nothing => pure Nothing
                                         Just response <- run fuel (f msg) | Nothing => pure Nothing
                                         unsafeSend sender response
                                         pure (Just ())

export partial
runProc : Process iface () ist ost -> IO ()
runProc process = do run forever process
                     pure ()
