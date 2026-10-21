import Harmonia.Distributed.Membership
namespace Harmonia.Distributed
universe u
inductive Status where | running | crashed
  deriving DecidableEq
structure Local (D V : Type u) where
  durable : D
  volatile : V
  status : Status
  deriving DecidableEq
structure Outgoing (M L P : Type u) where
  recipient : M
  logical : L
  payload : P
  deriving DecidableEq
structure Envelope (M L P : Type u) where
  sender : M
  recipient : M
  logical : L
  payload : P
  deriving DecidableEq
structure Transmission (M L P : Type u) where
  tid : Nat
  envelope : Envelope M L P
  deriving DecidableEq
inductive Stimulus (C K : Type u) where
  | local : C → Stimulus C K
  | timeout : K → Stimulus C K
  deriving DecidableEq
inductive Input (M L P C K : Type u) where
  | message : Envelope M L P → Input M L P C K
  | scheduled : Stimulus C K → Input M L P C K
/-- Fixed protocols get only own data and explicit input. Static closures remain
part of the model discipline; no changing external oracle is licensed. -/
structure Protocol (M D V L P C K : Type u) where
  initial : M → D → V → Prop
  react : M → D → V → Input M L P C K → D → V → List (Outgoing M L P) → Prop
  crashReset : D → V → V
  recover : D → V
structure FaultProfile where
  allowDrop : Bool
  allowDuplicate : Bool
  allowCrash : Bool
  allowRecover : Bool
  deriving DecidableEq
namespace FaultProfile
def reliable : FaultProfile := ⟨false,false,false,false⟩
def crashRecovery : FaultProfile := ⟨false,false,true,true⟩
def omission : FaultProfile := ⟨true,true,true,true⟩
end FaultProfile
end Harmonia.Distributed
