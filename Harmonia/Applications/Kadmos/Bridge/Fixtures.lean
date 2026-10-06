import Harmonia.Applications.Kadmos.Bridge.Certificate
namespace Harmonia.Applications.Kadmos.BridgeFixtures
open Harmonia.Applications.Kadmos.Bridge
open Harmonia.Applications.Kadmos
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
def balanceRaw : RawWorld := ⟨"kadmos.world.v0","BalanceWorld",none,[⟨"Ready",true,false,none⟩],[("balance",⟨"integer",some 0,some 9007199254740991,some 100,none,none⟩)],[⟨"nonnegative","balance >= 0",none⟩],[⟨"DEBIT","Ready","Ready",.expr "event.amount > 0",["balance = balance - event.amount"],none⟩],["amount"],[]⟩
def balanceCandidate : World 1 1 1 1 :=
  ⟨(fun j => (["Ready"])[j]),(fun j => ([true])[j]),(fun j => ([false])[j]),(fun j => (["balance"])[j]),(fun j => ([⟨0,9007199254740991,some 100⟩])[j]),(fun j => (["amount"])[j]),(fun j => (["DEBIT"])[j]),(fun j => ([⟨0,0,(.not (.le (.request 0) (.int 0))),[⟨0,(.sub (.context 0) (.request 0))⟩],none⟩])[j]),[("nonnegative",(.not (.lt (.context 0) (.int 0))))]⟩
theorem balance_certificate : checkBridge balanceRaw balanceCandidate = .ok balanceCandidate := by decide +kernel

def orderRaw : RawWorld := ⟨"kadmos.world.v0","OrderPhaseWorld",none,[⟨"A",true,false,none⟩,⟨"B",false,false,none⟩],[("x",⟨"integer",some 0,some 9007199254740991,some 1,none,none⟩),("y",⟨"integer",some 0,some 9007199254740991,some 0,none,none⟩)],[⟨"phase_order","state == 'B' => y == x",none⟩],[⟨"STEP","A","B",.bool true,["x = x + 1","y = x"],none⟩],[],[]⟩
def orderCandidate : World 2 2 0 1 :=
  ⟨(fun j => (["A","B"])[j]),(fun j => ([true,false])[j]),(fun j => ([false,false])[j]),(fun j => (["x","y"])[j]),(fun j => ([⟨0,9007199254740991,some 1⟩,⟨0,9007199254740991,some 0⟩])[j]),(fun j => ([])[j]),(fun j => (["STEP"])[j]),(fun j => ([⟨0,1,.bool true,[⟨0,(.add (.context 0) (.int 1))⟩,⟨1,.context 0⟩],none⟩])[j]),[("phase_order",(.implies (.stateIs 1) ((.eqInt (.context 1) (.context 0)))))]⟩
theorem order_certificate : checkBridge orderRaw orderCandidate = .ok orderCandidate := by decide +kernel

end Harmonia.Applications.Kadmos.BridgeFixtures
