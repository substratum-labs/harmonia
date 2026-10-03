/-
  Harmonia.SMT.TwoPhaseCommitVC
  Verification Condition Generator for Two-Phase Commit:
  Automates inductive invariant checking and counterexample synthesis via Z3.
-/

import Harmonia.SMT.Solver

namespace Harmonia.SMT.TwoPhaseCommitVC

open Harmonia.SMT

/-- Build SMT-LIB2 commands declaring types and state variables for pre-state and post-state. -/
def baseDeclarations : List Command := [
  Command.comment "Declare 2PC State Enums and Sorts",
  Command.declareDatatype "TxState" ["tx_init", "tx_prepared", "tx_committed", "tx_aborted"],

  Command.comment "Pre-state (s): Coordinator (0) and Participant (1)",
  Command.declareConst "s0_state" (SMTSort.custom "TxState"),
  Command.declareConst "s1_state" (SMTSort.custom "TxState"),
  Command.declareConst "s1_willing" SMTSort.bool,

  Command.comment "Pre-state (s): Network Message Pool",
  Command.declareConst "net_prepare" SMTSort.bool,
  Command.declareConst "net_vote_yes" SMTSort.bool,
  Command.declareConst "net_vote_no" SMTSort.bool,
  Command.declareConst "net_commit" SMTSort.bool,
  Command.declareConst "net_abort" SMTSort.bool,

  Command.comment "Post-state (s')",
  Command.declareConst "s0_state_next" (SMTSort.custom "TxState"),
  Command.declareConst "s1_state_next" (SMTSort.custom "TxState"),
  Command.declareConst "s1_willing_next" SMTSort.bool,

  Command.comment "Post-state (s'): Network Message Pool",
  Command.declareConst "net_prepare_next" SMTSort.bool,
  Command.declareConst "net_vote_yes_next" SMTSort.bool,
  Command.declareConst "net_vote_no_next" SMTSort.bool,
  Command.declareConst "net_commit_next" SMTSort.bool,
  Command.declareConst "net_abort_next" SMTSort.bool
]

/-- Primary Safety Invariant: Agreement (No conflicting decisions). -/
def agreementInv (s0 s1 : String) : Term :=
  Term.not (
    Term.and [
      Term.or [Term.eq (Term.var s0) (Term.var "tx_committed"), Term.eq (Term.var s1) (Term.var "tx_committed")],
      Term.or [Term.eq (Term.var s0) (Term.var "tx_aborted"), Term.eq (Term.var s1) (Term.var "tx_aborted")]
    ]
  )

/-- Auxiliary Invariants to complete inductive closure:
    1. If commit message in flight, no node is aborted and participant willing was true.
    2. If abort message in flight, no node is committed.
    3. If coordinator is committed, no abort message is in flight. -/
def inductiveInv (isPost : Bool) : Term :=
  let s0 := if isPost then "s0_state_next" else "s0_state"
  let s1 := if isPost then "s1_state_next" else "s1_state"
  let willing := if isPost then "s1_willing_next" else "s1_willing"
  let m_commit   := if isPost then "net_commit_next" else "net_commit"
  let m_abort    := if isPost then "net_abort_next" else "net_abort"
  let m_vote_yes := if isPost then "net_vote_yes_next" else "net_vote_yes"
  let m_vote_no  := if isPost then "net_vote_no_next" else "net_vote_no"

  Term.and [
    agreementInv s0 s1,

    -- Vote message integrity
    Term.implies (Term.var m_vote_yes) (
      Term.and [
        Term.eq (Term.var willing) (Term.boolConst true),
        Term.distinct [Term.var s1, Term.var "tx_init"],
        Term.not (Term.var m_vote_no)
      ]
    ),
    Term.implies (Term.var m_vote_no) (
      Term.and [
        Term.distinct [Term.var s1, Term.var "tx_init"],
        Term.distinct [Term.var s1, Term.var "tx_committed"],
        Term.not (Term.var m_commit)
      ]
    ),
    Term.not (Term.and [Term.var m_vote_yes, Term.var m_vote_no]),
    Term.implies (Term.not (Term.var willing)) (Term.not (Term.var m_vote_yes)),

    -- Commit message integrity (Commit is irrevocable and exclusive)
    Term.implies (Term.var m_commit) (
      Term.and [
        Term.eq (Term.var s0) (Term.var "tx_committed"),
        Term.or [Term.eq (Term.var s1) (Term.var "tx_prepared"), Term.eq (Term.var s1) (Term.var "tx_committed")],
        Term.eq (Term.var willing) (Term.boolConst true),
        Term.not (Term.var m_abort),
        Term.not (Term.var m_vote_no)
      ]
    ),

    -- Abort message integrity (Sent only by coordinator when transitioning to aborted)
    Term.implies (Term.var m_abort) (
      Term.and [
        Term.eq (Term.var s0) (Term.var "tx_aborted"),
        Term.distinct [Term.var s1, Term.var "tx_committed"],
        Term.not (Term.var m_commit)
      ]
    ),

    -- Coordinator committed implies participant is prepared or committed, and willing was true
    Term.implies (Term.eq (Term.var s0) (Term.var "tx_committed")) (
      Term.and [
        Term.or [Term.eq (Term.var s1) (Term.var "tx_prepared"), Term.eq (Term.var s1) (Term.var "tx_committed")],
        Term.eq (Term.var willing) (Term.boolConst true),
        Term.not (Term.var m_abort),
        Term.not (Term.var m_vote_no)
      ]
    ),

    -- Participant aborted while coordinator in init implies it never voted yes
    Term.implies (
      Term.and [Term.eq (Term.var s0) (Term.var "tx_init"), Term.eq (Term.var s1) (Term.var "tx_aborted")]
    ) (Term.not (Term.var m_vote_yes)),

    -- Coordinator aborted implies no commit message
    Term.implies (Term.eq (Term.var s0) (Term.var "tx_aborted")) (
      Term.not (Term.var m_commit)
    ),

    -- Participant committed implies coordinator is committed and no abort in flight
    Term.implies (Term.eq (Term.var s1) (Term.var "tx_committed")) (
      Term.and [
        Term.eq (Term.var s0) (Term.var "tx_committed"),
        Term.not (Term.var m_abort)
      ]
    )
  ]

/-- Operational transitions of 2PC. -/
def transitions (allowBuggyParticipantTimeout : Bool) : Term :=
  let validSteps := [
    -- 1. Coordinator initiates: sends prepare
    Term.and [
      Term.eq (Term.var "s0_state") (Term.var "tx_init"),
      Term.eq (Term.var "s0_state_next") (Term.var "tx_init"),
      Term.eq (Term.var "s1_state_next") (Term.var "s1_state"),
      Term.eq (Term.var "s1_willing_next") (Term.var "s1_willing"),
      Term.eq (Term.var "net_prepare_next") (Term.boolConst true),
      Term.eq (Term.var "net_vote_yes_next") (Term.var "net_vote_yes"),
      Term.eq (Term.var "net_vote_no_next") (Term.var "net_vote_no"),
      Term.eq (Term.var "net_commit_next") (Term.var "net_commit"),
      Term.eq (Term.var "net_abort_next") (Term.var "net_abort")
    ],

    -- 2. Participant 1 receives prepare and votes yes (if willing)
    Term.and [
      Term.var "net_prepare",
      Term.eq (Term.var "s1_state") (Term.var "tx_init"),
      Term.var "s1_willing",
      Term.eq (Term.var "s1_state_next") (Term.var "tx_prepared"),
      Term.eq (Term.var "s0_state_next") (Term.var "s0_state"),
      Term.eq (Term.var "s1_willing_next") (Term.var "s1_willing"),
      Term.eq (Term.var "net_prepare_next") (Term.var "net_prepare"),
      Term.eq (Term.var "net_vote_yes_next") (Term.boolConst true),
      Term.eq (Term.var "net_vote_no_next") (Term.var "net_vote_no"),
      Term.eq (Term.var "net_commit_next") (Term.var "net_commit"),
      Term.eq (Term.var "net_abort_next") (Term.var "net_abort")
    ],

    -- 3. Participant 1 receives prepare and votes no (if unwilling)
    Term.and [
      Term.var "net_prepare",
      Term.eq (Term.var "s1_state") (Term.var "tx_init"),
      Term.not (Term.var "s1_willing"),
      Term.eq (Term.var "s1_state_next") (Term.var "tx_aborted"),
      Term.eq (Term.var "s0_state_next") (Term.var "s0_state"),
      Term.eq (Term.var "s1_willing_next") (Term.var "s1_willing"),
      Term.eq (Term.var "net_prepare_next") (Term.var "net_prepare"),
      Term.eq (Term.var "net_vote_yes_next") (Term.var "net_vote_yes"),
      Term.eq (Term.var "net_vote_no_next") (Term.boolConst true),
      Term.eq (Term.var "net_commit_next") (Term.var "net_commit"),
      Term.eq (Term.var "net_abort_next") (Term.var "net_abort")
    ],

    -- 4. Coordinator receives vote_yes -> commits and sends commit
    Term.and [
      Term.var "net_vote_yes",
      Term.eq (Term.var "s0_state") (Term.var "tx_init"),
      Term.eq (Term.var "s0_state_next") (Term.var "tx_committed"),
      Term.eq (Term.var "s1_state_next") (Term.var "s1_state"),
      Term.eq (Term.var "s1_willing_next") (Term.var "s1_willing"),
      Term.eq (Term.var "net_prepare_next") (Term.var "net_prepare"),
      Term.eq (Term.var "net_vote_yes_next") (Term.var "net_vote_yes"),
      Term.eq (Term.var "net_vote_no_next") (Term.var "net_vote_no"),
      Term.eq (Term.var "net_commit_next") (Term.boolConst true),
      Term.eq (Term.var "net_abort_next") (Term.var "net_abort")
    ],

    -- 5. Coordinator receives vote_no -> aborts and sends abort
    Term.and [
      Term.var "net_vote_no",
      Term.eq (Term.var "s0_state") (Term.var "tx_init"),
      Term.eq (Term.var "s0_state_next") (Term.var "tx_aborted"),
      Term.eq (Term.var "s1_state_next") (Term.var "s1_state"),
      Term.eq (Term.var "s1_willing_next") (Term.var "s1_willing"),
      Term.eq (Term.var "net_prepare_next") (Term.var "net_prepare"),
      Term.eq (Term.var "net_vote_yes_next") (Term.var "net_vote_yes"),
      Term.eq (Term.var "net_vote_no_next") (Term.var "net_vote_no"),
      Term.eq (Term.var "net_commit_next") (Term.var "net_commit"),
      Term.eq (Term.var "net_abort_next") (Term.boolConst true)
    ],

    -- 6. Participant 1 receives commit -> transitions to committed
    Term.and [
      Term.var "net_commit",
      Term.eq (Term.var "s1_state") (Term.var "tx_prepared"),
      Term.eq (Term.var "s1_state_next") (Term.var "tx_committed"),
      Term.eq (Term.var "s0_state_next") (Term.var "s0_state"),
      Term.eq (Term.var "s1_willing_next") (Term.var "s1_willing"),
      Term.eq (Term.var "net_prepare_next") (Term.var "net_prepare"),
      Term.eq (Term.var "net_vote_yes_next") (Term.var "net_vote_yes"),
      Term.eq (Term.var "net_vote_no_next") (Term.var "net_vote_no"),
      Term.eq (Term.var "net_commit_next") (Term.var "net_commit"),
      Term.eq (Term.var "net_abort_next") (Term.var "net_abort")
    ],

    -- 7. Participant 1 receives abort -> transitions to aborted
    Term.and [
      Term.var "net_abort",
      Term.or [Term.eq (Term.var "s1_state") (Term.var "tx_init"), Term.eq (Term.var "s1_state") (Term.var "tx_prepared")],
      Term.eq (Term.var "s1_state_next") (Term.var "tx_aborted"),
      Term.eq (Term.var "s0_state_next") (Term.var "s0_state"),
      Term.eq (Term.var "s1_willing_next") (Term.var "s1_willing"),
      Term.eq (Term.var "net_prepare_next") (Term.var "net_prepare"),
      Term.eq (Term.var "net_vote_yes_next") (Term.var "net_vote_yes"),
      Term.eq (Term.var "net_vote_no_next") (Term.var "net_vote_no"),
      Term.eq (Term.var "net_commit_next") (Term.var "net_commit"),
      Term.eq (Term.var "net_abort_next") (Term.var "net_abort")
    ],

    -- 8. Valid Participant Timeout in init: unilateral abort
    Term.and [
      Term.eq (Term.var "s1_state") (Term.var "tx_init"),
      Term.eq (Term.var "s1_state_next") (Term.var "tx_aborted"),
      Term.eq (Term.var "s0_state_next") (Term.var "s0_state"),
      Term.eq (Term.var "s1_willing_next") (Term.var "s1_willing"),
      Term.eq (Term.var "net_prepare_next") (Term.var "net_prepare"),
      Term.eq (Term.var "net_vote_yes_next") (Term.var "net_vote_yes"),
      Term.eq (Term.var "net_vote_no_next") (Term.var "net_vote_no"),
      Term.eq (Term.var "net_commit_next") (Term.var "net_commit"),
      Term.eq (Term.var "net_abort_next") (Term.var "net_abort")
    ]
  ]

  let allSteps := if allowBuggyParticipantTimeout then
    validSteps ++ [
      -- BUGGY TRANSITION: Participant in prepared state prematurely aborts on timeout!
      Term.and [
        Term.eq (Term.var "s1_state") (Term.var "tx_prepared"),
        Term.eq (Term.var "s1_state_next") (Term.var "tx_aborted"),
        Term.eq (Term.var "s0_state_next") (Term.var "s0_state"),
        Term.eq (Term.var "s1_willing_next") (Term.var "s1_willing"),
        Term.eq (Term.var "net_prepare_next") (Term.var "net_prepare"),
        Term.eq (Term.var "net_vote_yes_next") (Term.var "net_vote_yes"),
        Term.eq (Term.var "net_vote_no_next") (Term.var "net_vote_no"),
        Term.eq (Term.var "net_commit_next") (Term.var "net_commit"),
        Term.eq (Term.var "net_abort_next") (Term.var "net_abort")
      ]
    ]
  else
    validSteps

  Term.or allSteps

/-- Construct verification script checking Inductive Invariant Preservation:
    Query: Assert Inv(s) ∧ Step(s, s') ∧ ¬Inv(s')
    Target: UNSAT (no violation possible) -/
def buildVerificationScript : List Command :=
  baseDeclarations ++ [
    Command.comment "Pre-state satisfies Inductive Invariant",
    Command.assert (inductiveInv false),

    Command.comment "Execute a valid transition step",
    Command.assert (transitions false),

    Command.comment "Check if post-state violates the Invariant",
    Command.assert (Term.not (inductiveInv true)),

    Command.checkSat,
    Command.getModel
  ]

/-- Construct falsification script injecting the classic 2PC blocking bug:
    Target: SAT (Z3 must reconstruct a counterexample showing split-brain / disagreement) -/
def buildFalsificationScript : List Command :=
  baseDeclarations ++ [
    Command.comment "Pre-state satisfies Inductive Invariant",
    Command.assert (inductiveInv false),

    Command.comment "Execute transition with BUGGY participant timeout",
    Command.assert (transitions true),

    Command.comment "Check if post-state violates the Agreement Invariant",
    Command.assert (Term.not (agreementInv "s0_state_next" "s1_state_next")),

    Command.checkSat,
    Command.getModel
  ]

end Harmonia.SMT.TwoPhaseCommitVC
