/-
  Harmonia.Gatekeeper.CExport
  Un-mangled C-ABI exports for physical runtime gatekeepers.
  Enforces zero-allocation, formally verified pre-commit checks in Rust/C++.
-/

namespace Harmonia.Gatekeeper

/--
  Pack verdict into a 32-bit integer:
  - bits 0..7   : status (1 = ALLOWED, 0 = REJECTED)
  - bits 8..15  : next_state (0 = init, 1 = prepared, 2 = committed, 3 = aborted)
  - bits 16..23 : action (0 = none, 1 = broadcast_commit, 2 = broadcast_abort, 3 = reply_vote_yes, 4 = reply_vote_no)
  - bits 24..31 : reserved
-/
def packVerdict (allowed : UInt8) (nextState : UInt8) (action : UInt8) : UInt32 :=
  (allowed.toUInt32) |||
  (nextState.toUInt32 <<< 8) |||
  (action.toUInt32 <<< 16)

/--
  Physical C-ABI exported entrypoint for message processing.
  Invoked by Rust before committing any state or sending network packets.
-/
@[export harmonia_2pc_step]
def harmonia2pcStep (currState : UInt8) (role : UInt8) (msgType : UInt8) (willing : UInt8) : UInt32 :=
  match role with
  | 0 => -- Coordinator
    match msgType with
    | 1 => -- VoteYes received
      if currState == 0 then
        -- In simple 1-participant slice: vote_yes commits
        packVerdict 1 2 1 -- ALLOWED, nextState = committed, action = broadcast_commit
      else
        packVerdict 0 currState 0 -- REJECTED: cannot accept vote when not in init
    | 2 => -- VoteNo received
      if currState == 0 then
        packVerdict 1 3 2 -- ALLOWED, nextState = aborted, action = broadcast_abort
      else
        packVerdict 0 currState 0 -- REJECTED
    | _ => packVerdict 0 currState 0 -- REJECTED: unexpected message for coordinator

  | 1 => -- Participant
    match msgType with
    | 0 => -- Prepare received
      if currState == 0 then
        if willing != 0 then
          packVerdict 1 1 3 -- ALLOWED, nextState = prepared, action = reply_vote_yes
        else
          packVerdict 1 3 4 -- ALLOWED, nextState = aborted, action = reply_vote_no
      else
        packVerdict 0 currState 0 -- REJECTED: prepare received when not in init

    | 3 => -- Global Commit received
      if currState == 1 then
        packVerdict 1 2 0 -- ALLOWED, nextState = committed, action = none
      else
        packVerdict 0 currState 0 -- REJECTED: cannot commit unless prepared!

    | 4 => -- Global Abort received
      if currState == 0 || currState == 1 then
        packVerdict 1 3 0 -- ALLOWED, nextState = aborted, action = none
      else
        packVerdict 0 currState 0 -- REJECTED

    | _ => packVerdict 0 currState 0 -- REJECTED: invalid message for participant

  | _ => packVerdict 0 currState 0 -- REJECTED: unknown role

/--
  Physical C-ABI exported entrypoint for timeout transitions.
  Enforces the fundamental distributed invariant: PREPARED PARTICIPANTS CANNOT ABORT!
-/
@[export harmonia_2pc_timeout]
def harmonia2pcTimeout (currState : UInt8) (role : UInt8) (hasVotes : UInt8) : UInt32 :=
  match role with
  | 0 => -- Coordinator
    if currState == 0 then
      if hasVotes != 0 then
        -- Timeout waiting for votes: coordinator unilaterally aborts
        packVerdict 1 3 2 -- ALLOWED, nextState = aborted, action = broadcast_abort
      else
        -- Initial trigger: coordinator starts transaction
        packVerdict 1 0 0 -- ALLOWED
    else
      packVerdict 0 currState 0 -- REJECTED

  | 1 => -- Participant
    if currState == 0 then
      -- Timeout waiting for prepare: participant can unilaterally abort
      packVerdict 1 3 0 -- ALLOWED, nextState = aborted, action = none
    else
      -- CRITICAL NON-BLOCKING INVARIANT:
      -- A prepared participant CANNOT timeout unilaterally. It MUST BLOCK!
      packVerdict 0 currState 0 -- REJECTED: Formal gatekeeper blocks unilateral abort!

  | _ => packVerdict 0 currState 0 -- REJECTED

end Harmonia.Gatekeeper
