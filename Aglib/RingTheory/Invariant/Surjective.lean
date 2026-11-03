/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RepresentationTheory.Invariants.Surjective
public import Mathlib.RingTheory.Invariant.Defs

/-! # Invariance through an original equivariant algebra surjection

Native invariant-vector lifting proves invariance of the actual target algebra.
The group order must be a unit in the coefficient ring; no field, faithful
action, quotient model or residue separability is assumed.
-/

@[expose] public noncomputable section

namespace Algebra.IsInvariant

universe r b c g

variable {R : Type r} [CommRing R]
  {B : Type b} [CommRing B] [Algebra R B]
  {C : Type c} [CommRing C] [Algebra R C]
  (G : Type g) [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G R B]
  [MulSemiringAction G C] [SMulCommClass G R C]
  [Algebra.IsInvariant R B G]

/-- A surjective actual equivariant algebra map preserves the native invariant
extension property when the original finite group order is invertible. -/
theorem of_surjective_equivariant (f : B →ₐ[R] C) (hf : Function.Surjective f)
    (he : ∀ (g : G) (b : B), f (g • b) = g • f b)
    (hG : IsUnit (Nat.card G : R)) : Algebra.IsInvariant R C G := by
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Fintype.card G : R) :=
    (show IsUnit (Fintype.card G : R) by simpa only [Nat.card_eq_fintype_card] using hG).invertible
  let ρ := Representation.ofDistribMulAction R G B
  let σ := Representation.ofDistribMulAction R G C
  let t : Representation.IntertwiningMap ρ σ :=
    f.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ σ he
  constructor
  intro c hc
  obtain ⟨b, hb, hbc⟩ := t.exists_invariant_preimage hf hc
  obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := G) b hb
  refine ⟨r, ?_⟩
  exact (f.commutes r).symm.trans ((congrArg f hr).trans hbc)

end Algebra.IsInvariant
