/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

/-- Package `lake lint` driver: no extra rules beyond `lake build --wfail`. -/
def main (_args : List String) : IO UInt32 := do
  IO.println "lake lint: no extra driver checks"
  return 0