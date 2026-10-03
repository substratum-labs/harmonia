/-
  Harmonia.DSL.Syntax
  Declarative protocol specification macros and automatic SMT lowering.
-/

import Lean
import Harmonia.SMT.AST

open Lean

namespace Harmonia.DSL

/-- High-level metadata of a distributed protocol declared via eDSL. -/
structure ProtocolMetadata where
  name     : String
  roles    : List String
  states   : List String
  messages : List String
deriving Repr, DecidableEq

/-- Helper to generate SMT-LIB2 datatype declarations from protocol metadata. -/
def generateSMTDatatypes (meta : ProtocolMetadata) : List Harmonia.SMT.Command := [
  Harmonia.SMT.Command.comment s!"Auto-generated Datatypes for protocol: {meta.name}",
  Harmonia.SMT.Command.declareDatatype s!"{meta.name}Role" meta.roles,
  Harmonia.SMT.Command.declareDatatype s!"{meta.name}State" meta.states,
  Harmonia.SMT.Command.declareDatatype s!"{meta.name}Payload" meta.messages
]

/-- Declarative macro defining a distributed protocol.
    Expands into native inductive types for Role, State, Payload, NodeState,
    and attaches automatic SMT-LIB2 lowering metadata. -/
macro "declare_protocol " name:ident " where "
  "roles" ":=" "[" roles:ident,* "]"
  "states" ":=" "[" states:ident,* "]"
  "messages" ":=" "[" msgs:ident,* "]" : command => do
  let roleName := mkIdent (name.getId ++ `Role)
  let stateName := mkIdent (name.getId ++ `State)
  let msgName := mkIdent (name.getId ++ `Payload)
  let nodeStateName := mkIdent (name.getId ++ `NodeState)
  let metaName := mkIdent (name.getId ++ `metadata)
  let smtName := mkIdent (name.getId ++ `smtDatatypes)

  let rCtors ← roles.getElems.mapM fun id => `(Parser.Command.ctor| | $id:ident)
  let sCtors ← states.getElems.mapM fun id => `(Parser.Command.ctor| | $id:ident)
  let mCtors ← msgs.getElems.mapM fun id => `(Parser.Command.ctor| | $id:ident)

  let rStrs := roles.getElems.map fun id => Syntax.mkStrLit id.getId.toString
  let sStrs := states.getElems.map fun id => Syntax.mkStrLit id.getId.toString
  let mStrs := msgs.getElems.map fun id => Syntax.mkStrLit id.getId.toString
  let nameStr := Syntax.mkStrLit name.getId.toString

  `(
    inductive $roleName where
      $[$rCtors]*
    deriving DecidableEq, Repr

    inductive $stateName where
      $[$sCtors]*
    deriving DecidableEq, Repr

    inductive $msgName where
      $[$mCtors]*
    deriving DecidableEq, Repr

    structure $nodeStateName where
      role  : $roleName
      state : $stateName
    deriving DecidableEq, Repr

    def $metaName : Harmonia.DSL.ProtocolMetadata := {
      name     := $nameStr,
      roles    := [$[$rStrs],*],
      states   := [$[$sStrs],*],
      messages := [$[$mStrs],*]
    }

    def $smtName : List Harmonia.SMT.Command :=
      Harmonia.DSL.generateSMTDatatypes $metaName
  )

end Harmonia.DSL
