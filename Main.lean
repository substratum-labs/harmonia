import Harmonia

def main : IO Unit := do
  IO.println Harmonia.welcomeBanner
  IO.println "Core modules loaded: Event, Network, SmallStep, Protocols.TwoPhaseCommit"
