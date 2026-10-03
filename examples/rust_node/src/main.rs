//! Harmonia Kadmos-Gatekeeper Rust Host Node
//! Demonstrates zero-cost, formally verified pre-commit runtime gatekeeping.

use std::time::Instant;

#[link(name = "harmonia_gatekeeper")]
extern "C" {
    fn harmonia_gatekeeper_init();
    fn harmonia_2pc_step(curr_state: u8, role: u8, msg_type: u8, willing: u8) -> u32;
    fn harmonia_2pc_timeout(curr_state: u8, role: u8, has_votes: u8) -> u32;
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum Role {
    Coordinator = 0,
    Participant = 1,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum TxState {
    Init = 0,
    Prepared = 1,
    Committed = 2,
    Aborted = 3,
}

impl TxState {
    pub fn from_u8(v: u8) -> Self {
        match v {
            0 => TxState::Init,
            1 => TxState::Prepared,
            2 => TxState::Committed,
            _ => TxState::Aborted,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum MsgType {
    Prepare = 0,
    VoteYes = 1,
    VoteNo = 2,
    Commit = 3,
    Abort = 4,
}

#[derive(Debug, PartialEq, Eq)]
pub struct GatekeeperVerdict {
    pub allowed: bool,
    pub next_state: TxState,
    pub action: u8,
}

impl GatekeeperVerdict {
    pub fn from_packed(raw: u32) -> Self {
        let allowed = (raw & 0xFF) == 1;
        let next_state = TxState::from_u8(((raw >> 8) & 0xFF) as u8);
        let action = ((raw >> 16) & 0xFF) as u8;
        GatekeeperVerdict {
            allowed,
            next_state,
            action,
        }
    }
}

pub struct HarmoniaGatekeeper;

impl HarmoniaGatekeeper {
    pub fn init() -> Self {
        unsafe { harmonia_gatekeeper_init() };
        HarmoniaGatekeeper
    }

    #[inline(always)]
    pub fn step(
        &self,
        curr_state: TxState,
        role: Role,
        msg: MsgType,
        willing: bool,
    ) -> GatekeeperVerdict {
        let raw = unsafe {
            harmonia_2pc_step(
                curr_state as u8,
                role as u8,
                msg as u8,
                if willing { 1 } else { 0 },
            )
        };
        GatekeeperVerdict::from_packed(raw)
    }

    #[inline(always)]
    pub fn timeout(&self, curr_state: TxState, role: Role, has_votes: bool) -> GatekeeperVerdict {
        let raw = unsafe {
            harmonia_2pc_timeout(
                curr_state as u8,
                role as u8,
                if has_votes { 1 } else { 0 },
            )
        };
        GatekeeperVerdict::from_packed(raw)
    }
}

fn main() {
    let gatekeeper = HarmoniaGatekeeper::init();

    println!("============================================================");
    println!("  Harmonia (Lean 4) -> Rust Runtime Gatekeeper Defense Demo");
    println!("============================================================");

    // Scenario 1: Normal, sound 2PC transaction flow
    println!("\n[Scenario 1] Legitimate 2PC Flow:");
    let v1 = gatekeeper.step(TxState::Init, Role::Participant, MsgType::Prepare, true);
    println!("  Participant receives Prepare (willing=true) -> {:?}", v1);
    assert!(v1.allowed && v1.next_state == TxState::Prepared);

    let v2 = gatekeeper.step(TxState::Prepared, Role::Participant, MsgType::Commit, true);
    println!("  Participant receives GlobalCommit while Prepared -> {:?}", v2);
    assert!(v2.allowed && v2.next_state == TxState::Committed);
    println!("  ✓ Legitimate protocol transitions verified and committed!");

    // Scenario 2: Hostile race condition - Prepared Participant attempts unilateral timeout abort
    println!("\n[Scenario 2] Hostile Race Defense (Prepared Participant timeout):");
    let v_buggy = gatekeeper.timeout(TxState::Prepared, Role::Participant, false);
    println!("  Prepared Participant attempts unilateral abort -> {:?}", v_buggy);
    assert!(!v_buggy.allowed, "MUST BE REJECTED");
    println!("  🛡️ DEFENSE TRIGGERED: Formal gatekeeper blocked unilateral abort in memory!");
    println!("     Split-brain / Inconsistent history physically prevented before I/O.");

    // Scenario 3: Out-of-order packet - Commit received in Init state
    println!("\n[Scenario 3] Out-of-order Packet Defense (Commit received in Init):");
    let v_bad = gatekeeper.step(TxState::Init, Role::Participant, MsgType::Commit, true);
    println!("  Commit received while in Init state -> {:?}", v_bad);
    assert!(!v_bad.allowed);
    println!("  🛡️ DEFENSE TRIGGERED: Premature commit blocked by formal specification!");

    // Scenario 4: Performance Benchmark
    println!("\n[Scenario 4] Performance Benchmark (1,000,000 Pre-Commit Gatekeeper Checks):");
    let start = Instant::now();
    let iters = 1_000_000;
    for _ in 0..iters {
        let _ = gatekeeper.step(TxState::Init, Role::Participant, MsgType::Prepare, true);
    }
    let duration = start.elapsed();
    let per_op_ns = duration.as_nanos() as f64 / iters as f64;
    println!("  Completed {} gatekeeper checks in {:?}", iters, duration);
    println!("  Latency: {:.2} ns per formal check!", per_op_ns);

    println!("\n============================================================");
    println!("  Kadmos-Harmonia World-Fabric Architecture: Physical Proof Complete!");
    println!("============================================================");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gatekeeper_blocks_unilateral_abort() {
        let gatekeeper = HarmoniaGatekeeper::init();
        let verdict = gatekeeper.timeout(TxState::Prepared, Role::Participant, false);
        assert!(!verdict.allowed, "Gatekeeper must block unilateral abort when prepared!");
    }

    #[test]
    fn test_gatekeeper_allows_valid_prepare() {
        let gatekeeper = HarmoniaGatekeeper::init();
        let verdict = gatekeeper.step(TxState::Init, Role::Participant, MsgType::Prepare, true);
        assert!(verdict.allowed);
        assert_eq!(verdict.next_state, TxState::Prepared);
        assert_eq!(verdict.action, 3);
    }
}
