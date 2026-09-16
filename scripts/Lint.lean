/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

/-- Iteration-0 `lake lint` driver: the package has no extra lint rules yet. -/
def main (_args : List String) : IO UInt32 := do
  IO.println "lake lint: no extra driver checks in iteration 0"
  return 0