import Harmonia.Applications.Kadmos.Generated.TargetSyntax

/-! Literal normalization of fixed DEBIT source selectors. Execution proofs
check the source equality with `with_unfolding_all change`; these values add
no execution primitive and contain the original AST nodes. -/
namespace Harmonia.Applications.Kadmos.Generated
set_option autoImplicit false
def balanceStepTsGuardSyntax : TargetExpr := TargetExpr.call
  (TargetExpr.local "evaluateWorld")
  (TargetExpr.sequence
    (TargetExpr.property
      (TargetExpr.local "transition")
      "guard")
    (TargetExpr.sequence
      (TargetExpr.call
        (TargetExpr.local "env")
        (TargetExpr.sequence
          (TargetExpr.property
            (TargetExpr.local "this")
            "#state")
          (TargetExpr.sequence
            (TargetExpr.property
              (TargetExpr.local "this")
              "#context")
            (TargetExpr.empty))))
      (TargetExpr.empty)))

def balanceStepPyPrefixSyntax : TargetStmt := TargetStmt.sequence
  (TargetStmt.defineFunction
    "security_reject"
    [{ name := "message", defaultValue := none },
     { name := "action", defaultValue := some (TargetExpr.string "<invalid>") }]
    (TargetStmt.sequence
      (TargetStmt.doExpr
        (TargetExpr.call
          (TargetExpr.local "rollback")
          (TargetExpr.empty)))
      (TargetStmt.sequence
        (TargetStmt.assign
          (AssignTarget.local "trace")
          (TargetExpr.binary
            (BinaryOp.add)
            (TargetExpr.listComprehension
              (TargetExpr.call
                (TargetExpr.property
                  (TargetExpr.local "copy")
                  "deepcopy")
                (TargetExpr.sequence
                  (TargetExpr.local "r")
                  (TargetExpr.empty)))
              ["r"]
              (TargetExpr.local "original_history")
              (TargetExpr.empty))
            (TargetExpr.array
              (TargetExpr.sequence
                (TargetExpr.object
                  (TargetExpr.objectEntry
                    "step"
                    (TargetExpr.binary
                      (BinaryOp.add)
                      (TargetExpr.call
                        (TargetExpr.local "len")
                        (TargetExpr.sequence
                          (TargetExpr.local "original_history")
                          (TargetExpr.empty)))
                      (TargetExpr.integer 1))
                    (TargetExpr.objectEntry
                      "state"
                      (TargetExpr.local "previous")
                      (TargetExpr.objectEntry
                        "action"
                        (TargetExpr.local "action")
                        (TargetExpr.empty)))))
                (TargetExpr.empty)))))
        (TargetStmt.sequence
          (TargetStmt.returnValue
            (TargetExpr.object
              (TargetExpr.objectEntry
                "allowed"
                (TargetExpr.bool false)
                (TargetExpr.objectEntry
                  "previousState"
                  (TargetExpr.local "previous")
                  (TargetExpr.objectEntry
                    "currentState"
                    (TargetExpr.local "previous")
                    (TargetExpr.objectEntry
                      "context"
                      (TargetExpr.local "original_context")
                      (TargetExpr.objectEntry
                        "directiveAllowed"
                        (TargetExpr.null)
                        (TargetExpr.objectEntry
                          "violation"
                          (TargetExpr.object
                            (TargetExpr.objectEntry
                              "code"
                              (TargetExpr.string "SECURITY_VIOLATION")
                              (TargetExpr.objectEntry
                                "message"
                                (TargetExpr.local "message")
                                (TargetExpr.objectEntry
                                  "shortestCounterexampleTrace"
                                  (TargetExpr.local "trace")
                                  (TargetExpr.empty)))))
                          (TargetExpr.empty)))))))))
          (TargetStmt.empty)))))
  (TargetStmt.sequence
    (TargetStmt.ifThenElse
      (TargetExpr.binary
        (BinaryOp.isNotIdentity)
        (TargetExpr.call
          (TargetExpr.local "type")
          (TargetExpr.sequence
            (TargetExpr.local "request")
            (TargetExpr.empty)))
        (TargetExpr.local "dict"))
      (TargetStmt.sequence
        (TargetStmt.returnValue
          (TargetExpr.call
            (TargetExpr.local "security_reject")
            (TargetExpr.sequence
              (TargetExpr.string "step request must be a dict")
              (TargetExpr.empty))))
        (TargetStmt.empty))
      (TargetStmt.empty))
    (TargetStmt.sequence
      (TargetStmt.assign
        (AssignTarget.local "action_val")
        (TargetExpr.null))
      (TargetStmt.sequence
        (TargetStmt.assign
          (AssignTarget.local "has_action")
          (TargetExpr.bool false))
        (TargetStmt.sequence
          (TargetStmt.assign
            (AssignTarget.local "proposed_val")
            (TargetExpr.null))
          (TargetStmt.sequence
            (TargetStmt.assign
              (AssignTarget.local "has_proposed")
              (TargetExpr.bool false))
            (TargetStmt.sequence
              (TargetStmt.assign
                (AssignTarget.local "raw_payload")
                (TargetExpr.null))
              (TargetStmt.sequence
                (TargetStmt.forDo
                  ["key", "value"]
                  (TargetExpr.call
                    (TargetExpr.local "list")
                    (TargetExpr.sequence
                      (TargetExpr.call
                        (TargetExpr.property
                          (TargetExpr.local "dict")
                          "items")
                        (TargetExpr.sequence
                          (TargetExpr.local "request")
                          (TargetExpr.empty)))
                      (TargetExpr.empty)))
                  (TargetStmt.sequence
                    (TargetStmt.ifThenElse
                      (TargetExpr.binary
                        (BinaryOp.isNotIdentity)
                        (TargetExpr.call
                          (TargetExpr.local "type")
                          (TargetExpr.sequence
                            (TargetExpr.local "key")
                            (TargetExpr.empty)))
                        (TargetExpr.local "str"))
                      (TargetStmt.sequence
                        (TargetStmt.returnValue
                          (TargetExpr.call
                            (TargetExpr.local "security_reject")
                            (TargetExpr.sequence
                              (TargetExpr.string "request keys must be strings")
                              (TargetExpr.empty))))
                        (TargetStmt.empty))
                      (TargetStmt.empty))
                    (TargetStmt.sequence
                      (TargetStmt.ifThenElse
                        (TargetExpr.binary
                          (BinaryOp.eq)
                          (TargetExpr.local "key")
                          (TargetExpr.string "transitionId"))
                        (TargetStmt.sequence
                          (TargetStmt.assign
                            (AssignTarget.local "action_val")
                            (TargetExpr.local "value"))
                          (TargetStmt.sequence
                            (TargetStmt.assign
                              (AssignTarget.local "has_action")
                              (TargetExpr.bool true))
                            (TargetStmt.empty)))
                        (TargetStmt.ifThenElse
                          (TargetExpr.binary
                            (BinaryOp.eq)
                            (TargetExpr.local "key")
                            (TargetExpr.string "proposedDirective"))
                          (TargetStmt.sequence
                            (TargetStmt.assign
                              (AssignTarget.local "proposed_val")
                              (TargetExpr.local "value"))
                            (TargetStmt.sequence
                              (TargetStmt.assign
                                (AssignTarget.local "has_proposed")
                                (TargetExpr.bool true))
                              (TargetStmt.empty)))
                          (TargetStmt.ifThenElse
                            (TargetExpr.binary
                              (BinaryOp.eq)
                              (TargetExpr.local "key")
                              (TargetExpr.string "eventPayload"))
                            (TargetStmt.sequence
                              (TargetStmt.assign
                                (AssignTarget.local "raw_payload")
                                (TargetExpr.local "value"))
                              (TargetStmt.empty))
                            (TargetStmt.empty))))
                      (TargetStmt.empty))))
                (TargetStmt.sequence
                  (TargetStmt.ifThenElse
                    (TargetExpr.orElse
                      (TargetExpr.unary
                        (UnaryOp.not)
                        (TargetExpr.local "has_action"))
                      (TargetExpr.binary
                        (BinaryOp.isNotIdentity)
                        (TargetExpr.call
                          (TargetExpr.local "type")
                          (TargetExpr.sequence
                            (TargetExpr.local "action_val")
                            (TargetExpr.empty)))
                        (TargetExpr.local "str")))
                    (TargetStmt.sequence
                      (TargetStmt.returnValue
                        (TargetExpr.call
                          (TargetExpr.local "security_reject")
                          (TargetExpr.sequence
                            (TargetExpr.string "transitionId must be a string")
                            (TargetExpr.empty))))
                      (TargetStmt.empty))
                    (TargetStmt.empty))
                  (TargetStmt.sequence
                    (TargetStmt.assign
                      (AssignTarget.local "action")
                      (TargetExpr.local "action_val"))
                    (TargetStmt.sequence
                      (TargetStmt.ifThenElse
                        (TargetExpr.andThen
                          (TargetExpr.andThen
                            (TargetExpr.local "has_proposed")
                            (TargetExpr.binary
                              (BinaryOp.isNotIdentity)
                              (TargetExpr.local "proposed_val")
                              (TargetExpr.null)))
                          (TargetExpr.binary
                            (BinaryOp.isNotIdentity)
                            (TargetExpr.call
                              (TargetExpr.local "type")
                              (TargetExpr.sequence
                                (TargetExpr.local "proposed_val")
                                (TargetExpr.empty)))
                            (TargetExpr.local "str")))
                        (TargetStmt.sequence
                          (TargetStmt.returnValue
                            (TargetExpr.call
                              (TargetExpr.local "security_reject")
                              (TargetExpr.sequence
                                (TargetExpr.string
                                  "proposedDirective must be a string, null, or undefined")
                                (TargetExpr.sequence
                                  (TargetExpr.string "<invalid>")
                                  (TargetExpr.empty)))))
                          (TargetStmt.empty))
                        (TargetStmt.empty))
                      (TargetStmt.sequence
                        (TargetStmt.assign
                          (AssignTarget.local "proposed")
                          (TargetExpr.local "proposed_val"))
                        (TargetStmt.sequence
                          (TargetStmt.tryCatchFinally
                            (TargetStmt.sequence
                              (TargetStmt.assign
                                (AssignTarget.local "payload")
                                (TargetExpr.call
                                  (TargetExpr.local "sanitize_world_payload")
                                  (TargetExpr.sequence
                                    (TargetExpr.local "raw_payload")
                                    (TargetExpr.empty))))
                              (TargetStmt.empty))
                            (some "Exception")
                            (some "error")
                            (TargetStmt.sequence
                              (TargetStmt.returnValue
                                (TargetExpr.call
                                  (TargetExpr.local "security_reject")
                                  (TargetExpr.sequence
                                    (TargetExpr.call
                                      (TargetExpr.local "str")
                                      (TargetExpr.sequence
                                        (TargetExpr.local "error")
                                        (TargetExpr.empty)))
                                    (TargetExpr.sequence
                                      (TargetExpr.local "action")
                                      (TargetExpr.empty)))))
                              (TargetStmt.empty))
                            (TargetStmt.empty))
                          (TargetStmt.sequence
                            (TargetStmt.assign
                              (AssignTarget.local "record")
                              (TargetExpr.object
                                (TargetExpr.objectEntry
                                  "step"
                                  (TargetExpr.binary
                                    (BinaryOp.add)
                                    (TargetExpr.call
                                      (TargetExpr.local "len")
                                      (TargetExpr.sequence
                                        (TargetExpr.local "original_history")
                                        (TargetExpr.empty)))
                                    (TargetExpr.integer 1))
                                  (TargetExpr.objectEntry
                                    "state"
                                    (TargetExpr.local "previous")
                                    (TargetExpr.objectEntry
                                      "action"
                                      (TargetExpr.local "action")
                                      (TargetExpr.empty))))))
                            (TargetStmt.sequence
                              (TargetStmt.ifThenElse
                                (TargetExpr.binary
                                  (BinaryOp.isNotIdentity)
                                  (TargetExpr.local "payload")
                                  (TargetExpr.null))
                                (TargetStmt.sequence
                                  (TargetStmt.assign
                                    (AssignTarget.index
                                      (TargetExpr.local "record")
                                      (TargetExpr.string "eventPayload"))
                                    (TargetExpr.local "payload"))
                                  (TargetStmt.empty))
                                (TargetStmt.empty))
                              (TargetStmt.sequence
                                (TargetStmt.ifThenElse
                                  (TargetExpr.local "has_proposed")
                                  (TargetStmt.sequence
                                    (TargetStmt.assign
                                      (AssignTarget.index
                                        (TargetExpr.local "record")
                                        (TargetExpr.string "proposedDirective"))
                                      (TargetExpr.local "proposed"))
                                    (TargetStmt.empty))
                                  (TargetStmt.empty))
                                (TargetStmt.sequence
                                  (TargetStmt.defineFunction
                                    "reject"
                                    [{ name := "code", defaultValue := none },
                                     { name := "message", defaultValue := none },
                                     { name := "invariant",
                                       defaultValue := some (TargetExpr.null) }]
                                    (TargetStmt.sequence
                                      (TargetStmt.doExpr
                                        (TargetExpr.call
                                          (TargetExpr.local "rollback")
                                          (TargetExpr.empty)))
                                      (TargetStmt.sequence
                                        (TargetStmt.assign
                                          (AssignTarget.local "violation")
                                          (TargetExpr.object
                                            (TargetExpr.objectEntry
                                              "code"
                                              (TargetExpr.local "code")
                                              (TargetExpr.objectEntry
                                                "message"
                                                (TargetExpr.local "message")
                                                (TargetExpr.objectEntry
                                                  "shortestCounterexampleTrace"
                                                  (TargetExpr.binary
                                                    (BinaryOp.add)
                                                    (TargetExpr.listComprehension
                                                      (TargetExpr.call
                                                        (TargetExpr.property
                                                          (TargetExpr.local
                                                            "copy")
                                                          "deepcopy")
                                                        (TargetExpr.sequence
                                                          (TargetExpr.local "r")
                                                          (TargetExpr.empty)))
                                                      ["r"]
                                                      (TargetExpr.local
                                                        "original_history")
                                                      (TargetExpr.empty))
                                                    (TargetExpr.array
                                                      (TargetExpr.sequence
                                                        (TargetExpr.call
                                                          (TargetExpr.property
                                                            (TargetExpr.local
                                                              "copy")
                                                            "deepcopy")
                                                          (TargetExpr.sequence
                                                            (TargetExpr.local
                                                              "record")
                                                            (TargetExpr.empty)))
                                                        (TargetExpr.empty))))
                                                  (TargetExpr.empty))))))
                                        (TargetStmt.sequence
                                          (TargetStmt.ifThenElse
                                            (TargetExpr.binary
                                              (BinaryOp.isNotIdentity)
                                              (TargetExpr.local "invariant")
                                              (TargetExpr.null))
                                            (TargetStmt.sequence
                                              (TargetStmt.assign
                                                (AssignTarget.index
                                                  (TargetExpr.local "violation")
                                                  (TargetExpr.string
                                                    "violatedInvariant"))
                                                (TargetExpr.local "invariant"))
                                              (TargetStmt.empty))
                                            (TargetStmt.empty))
                                          (TargetStmt.sequence
                                            (TargetStmt.returnValue
                                              (TargetExpr.object
                                                (TargetExpr.objectEntry
                                                  "allowed"
                                                  (TargetExpr.bool false)
                                                  (TargetExpr.objectEntry
                                                    "previousState"
                                                    (TargetExpr.local "previous")
                                                    (TargetExpr.objectEntry
                                                      "currentState"
                                                      (TargetExpr.local
                                                        "previous")
                                                      (TargetExpr.objectEntry
                                                        "context"
                                                        (TargetExpr.local
                                                          "original_context")
                                                        (TargetExpr.objectEntry
                                                          "directiveAllowed"
                                                          (TargetExpr.null)
                                                          (TargetExpr.objectEntry
                                                            "violation"
                                                            (TargetExpr.local
                                                              "violation")
                                                            (TargetExpr.empty)))))))))
                                            (TargetStmt.empty))))))
                                  (TargetStmt.sequence
                                    (TargetStmt.assign
                                      (AssignTarget.local "transition")
                                      (TargetExpr.call
                                        (TargetExpr.local "next")
                                        (TargetExpr.sequence
                                          (TargetExpr.generator
                                            (TargetExpr.local "item")
                                            ["item"]
                                            (TargetExpr.index
                                              (TargetExpr.local "_WORLD")
                                              (TargetExpr.string "transitions"))
                                            (TargetExpr.andThen
                                              (TargetExpr.binary
                                                (BinaryOp.eq)
                                                (TargetExpr.index
                                                  (TargetExpr.local "item")
                                                  (TargetExpr.string "id"))
                                                (TargetExpr.local "action"))
                                              (TargetExpr.binary
                                                (BinaryOp.eq)
                                                (TargetExpr.index
                                                  (TargetExpr.local "item")
                                                  (TargetExpr.string "from"))
                                                (TargetExpr.local "previous"))))
                                          (TargetExpr.sequence
                                            (TargetExpr.null)
                                            (TargetExpr.empty)))))
                                    (TargetStmt.sequence
                                      (TargetStmt.ifThenElse
                                        (TargetExpr.binary
                                          (BinaryOp.isIdentity)
                                          (TargetExpr.local "transition")
                                          (TargetExpr.null))
                                        (TargetStmt.sequence
                                          (TargetStmt.returnValue
                                            (TargetExpr.call
                                              (TargetExpr.local "reject")
                                              (TargetExpr.sequence
                                                (TargetExpr.conditional
                                                  (TargetExpr.call
                                                    (TargetExpr.local "any")
                                                    (TargetExpr.sequence
                                                      (TargetExpr.generator
                                                        (TargetExpr.andThen
                                                          (TargetExpr.binary
                                                            (BinaryOp.eq)
                                                            (TargetExpr.index
                                                              (TargetExpr.local
                                                                "s")
                                                              (TargetExpr.string
                                                                "id"))
                                                            (TargetExpr.local
                                                              "previous"))
                                                          (TargetExpr.call
                                                            (TargetExpr.property
                                                              (TargetExpr.local
                                                                "s")
                                                              "get")
                                                            (TargetExpr.sequence
                                                              (TargetExpr.string
                                                                "terminal")
                                                              (TargetExpr.empty))))
                                                        ["s"]
                                                        (TargetExpr.index
                                                          (TargetExpr.local
                                                            "_WORLD")
                                                          (TargetExpr.string
                                                            "states"))
                                                        (TargetExpr.empty))
                                                      (TargetExpr.empty)))
                                                  (TargetExpr.string
                                                    "ILLEGAL_TRANSITION")
                                                  (TargetExpr.string
                                                    "INVALID_TRANSITION"))
                                                (TargetExpr.sequence
                                                  (TargetExpr.formatted
                                                    (TargetExpr.formatPart
                                                      "Transition '"
                                                      (TargetExpr.local "action")
                                                      (TargetExpr.formatPart
                                                        "' is not legal from state '"
                                                        (TargetExpr.local
                                                          "previous")
                                                        (TargetExpr.formatPart
                                                          "'"
                                                          (TargetExpr.empty)
                                                          (TargetExpr.empty)))))
                                                  (TargetExpr.empty)))))
                                          (TargetStmt.empty))
                                        (TargetStmt.empty))
                                      (TargetStmt.sequence
                                        (TargetStmt.ifThenElse
                                          (TargetExpr.binary
                                            (BinaryOp.ne)
                                            (TargetExpr.local "proposed")
                                            (TargetExpr.index
                                              (TargetExpr.local "transition")
                                              (TargetExpr.string "directive")))
                                          (TargetStmt.sequence
                                            (TargetStmt.returnValue
                                              (TargetExpr.call
                                                (TargetExpr.local "reject")
                                                (TargetExpr.sequence
                                                  (TargetExpr.string
                                                    "UNAUTHORIZED_DIRECTIVE")
                                                  (TargetExpr.sequence
                                                    (TargetExpr.string
                                                      "Directive does not match declared transition")
                                                    (TargetExpr.empty)))))
                                            (TargetStmt.empty))
                                          (TargetStmt.empty))
                                        (TargetStmt.sequence
                                          (TargetStmt.assign
                                            (AssignTarget.local "environment")
                                            (TargetExpr.lambdaExpr
                                              ["state", "values"]
                                              (TargetExpr.object
                                                (TargetExpr.objectSpread
                                                  (TargetExpr.local "values")
                                                  (TargetExpr.objectEntry
                                                    "state"
                                                    (TargetExpr.local "state")
                                                    (TargetExpr.objectEntry
                                                      "event"
                                                      (TargetExpr.orElse
                                                        (TargetExpr.local
                                                          "payload")
                                                        (TargetExpr.object
                                                          (TargetExpr.empty)))
                                                      (TargetExpr.objectEntry
                                                        "request"
                                                        (TargetExpr.orElse
                                                          (TargetExpr.local
                                                            "payload")
                                                          (TargetExpr.object
                                                            (TargetExpr.empty)))
                                                        (TargetExpr.empty))))))))
                                          (TargetStmt.empty)))))))))))))))))))))

def balanceStepPyGuardSyntax : TargetExpr := TargetExpr.call
  (TargetExpr.local "evaluate_world")
  (TargetExpr.sequence
    (TargetExpr.index
      (TargetExpr.local "transition")
      (TargetExpr.string "guard"))
    (TargetExpr.sequence
      (TargetExpr.call
        (TargetExpr.local "environment")
        (TargetExpr.sequence
          (TargetExpr.local "previous")
          (TargetExpr.sequence
            (TargetExpr.local "original_context")
            (TargetExpr.empty))))
      (TargetExpr.empty)))

end Harmonia.Applications.Kadmos.Generated
