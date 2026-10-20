/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent

/-!
# Natural torsion levels and their multiplication kernels

The primary component is `Ideal.primaryComponent`; finite levels reuse
`AddSubgroup.torsionBy`, without a second subgroup implementation.

Source: `R5Lab.Aglib.GroupTheory.Torsion.Levels`.
Packet SHA-256:
`24b0659ee3b5de51d764c67a67287a722d6bb8ad53573b15270309159b49005d`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

namespace AddSubgroup

variable (T : Type*) [AddCommGroup T]

/-- Mathlib's integer torsion subgroup has the literal natural multiplication kernel. -/
theorem torsionBy_natCast_eq_ker (n : ℕ) :
    torsionBy T (n : ℤ) = (nsmulAddMonoidHom n : T →+ T).ker := by
  ext x
  exact torsionBy.nsmul_iff

end AddSubgroup
