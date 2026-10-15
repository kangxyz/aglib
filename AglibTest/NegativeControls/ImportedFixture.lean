/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Data.Nat.Basic

/-! Deliberately invalid isolated control: excluded from positive roots and
source placeholder acceptance. It must be rejected by the legacy origin audit. -/

@[expose] public section

namespace UnrelatedNegativeNamespace

axiom importedBad : False

private theorem hiddenBad : False := importedBad

inductive GeneratedBad where
  | mk : False → GeneratedBad

private def hiddenGenerated : GeneratedBad := .mk hiddenBad

end UnrelatedNegativeNamespace
