/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Invariant.Surjective
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Galois.Basic

/-! # Residue invariance and separability from invertible group order

An actual invariant local-ring extension has an invariant residue-field
extension when the finite group order is a unit in the original base ring.
The residue field is then Galois over the original base residue field. No
faithfulness, perfectness, or pre-assumed residue separability is needed.
The action must be on the actual local ring: a global group action at an
unstabilized prime does not supply these hypotheses.
-/

@[expose] public noncomputable section

namespace IsLocalRing

universe r s g

variable {R : Type r} [CommRing R] [IsLocalRing R]
  {S : Type s} [CommRing S] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  (G : Type g) [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S]
  [Algebra.IsInvariant R S G]

omit [IsLocalRing R] [IsLocalHom (algebraMap R S)] [Finite G] [Algebra.IsInvariant R S G] in
/-- The original base-ring scalar action commutes with the induced action on
the actual target residue field. -/
theorem residueScalarCommClass : SMulCommClass G R (ResidueField S) where
  smul_comm g r z := by
    obtain ⟨x, rfl⟩ := residue_surjective (R := S) z
    change residue S (g • (r • x)) = residue S (r • (g • x))
    exact congrArg (residue S) (smul_comm g r x)

/-- Original residue-field invariance is constructed by averaging a lift along
the literal residue map. -/
theorem residue_isInvariant (hG : IsUnit (Nat.card G : R)) :
    Algebra.IsInvariant (ResidueField R) (ResidueField S) G := by
  let := residueScalarCommClass (R := R) (S := S) G
  let f : S →ₐ[R] ResidueField S := IsScalarTower.toAlgHom R S (ResidueField S)
  have h : Algebra.IsInvariant R (ResidueField S) G :=
    Algebra.IsInvariant.of_surjective_equivariant G f (residue_surjective)
      (fun g s => ResidueField.residue_smul G g s) hG
  let := h
  constructor
  intro z hz
  obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := G) z hz
  refine ⟨residue R r, ?_⟩
  exact hr

omit [Finite G] [Algebra.IsInvariant R S G] in
/-- The original base residue-field scalars are fixed by the induced action. -/
theorem residueFieldScalarCommClass : SMulCommClass G (ResidueField R) (ResidueField S) where
  smul_comm g r z := by
    obtain ⟨a, rfl⟩ := residue_surjective (R := R) r
    obtain ⟨x, rfl⟩ := residue_surjective (R := S) z
    change residue S (g • (a • x)) = residue S (a • (g • x))
    exact congrArg (residue S) (smul_comm g a x)

/-- The actual residue extension is Galois. The finite group need not act
faithfully; native fixed-field Galois theory supplies separability. -/
theorem residue_isGalois (hG : IsUnit (Nat.card G : R)) :
    IsGalois (ResidueField R) (ResidueField S) := by
  let := residueFieldScalarCommClass (R := R) (S := S) G
  let := residue_isInvariant (R := R) (S := S) G hG
  have hfixed : FixedPoints.intermediateField G =
      (⊥ : IntermediateField (ResidueField R) (ResidueField S)) := by
    rw [eq_bot_iff]
    exact Algebra.IsInvariant.isInvariant
  rw [← isGalois_iff_isGalois_bot, ← hfixed]
  exact IsGalois.of_fixed_field (ResidueField S) G

/-- Separability of the original residue-field map is a consequence, not an input. -/
theorem residue_isSeparable (hG : IsUnit (Nat.card G : R)) :
    Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
  (residue_isGalois (R := R) (S := S) G hG).to_isSeparable

end IsLocalRing
