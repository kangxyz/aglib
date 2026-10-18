/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Monic irreducible polynomials and finite divisor support

The subtype represents polynomial places without depending on a residue theory.
The declarations are extracted from Motivic's Milnor residue-support module;
their original field hypothesis and defining polynomial are unchanged.
-/

@[expose] public section

namespace Polynomial

variable (k : Type*) [Field k]

/-- Polynomial places represented by their unique monic irreducible polynomial. -/
abbrev MonicIrreducible := {p : k[X] // p.Monic ∧ Irreducible p}

instance MonicIrreducible.instIrreducible (p : MonicIrreducible k) :
    Fact (Irreducible p.val) := ⟨p.property.2⟩

variable {k}

/-- Nonzero polynomials have only finitely many monic irreducible divisors. -/
theorem finite_monicIrreducible_divisors (q : k[X]) (hq : q ≠ 0) :
    Set.Finite {p : MonicIrreducible k | p.val ∣ q} := by
  classical
  have h := Set.Finite.preimage (f := fun p : MonicIrreducible k => p.val)
    Subtype.val_injective.injOn
    (Multiset.finite_toSet (UniqueFactorizationMonoid.normalizedFactors q))
  refine h.subset ?_
  intro p hp
  exact (Polynomial.mem_normalizedFactors_iff hq).mpr ⟨p.property.2, p.property.1, hp⟩

end Polynomial
