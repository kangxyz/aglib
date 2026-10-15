/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Data.Nat.Basic

/-! Positive coverage data for defining-module origin inventories. The namespace
is intentionally unrelated to Aglib and retained R5Lab/Quillen APIs. -/

@[expose] public section

namespace AuditForeign

inductive GeneratedDatum where
  | mk : Nat → GeneratedDatum

private def hiddenDatum : Nat := 7

def rootDatum : Nat := 7

example : rootDatum = 7 := rfl

end AuditForeign
