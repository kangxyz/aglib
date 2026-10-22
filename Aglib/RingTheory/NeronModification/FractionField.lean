/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Domain
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! # The unchanged fraction field of a Néron modification

The original fraction field receives the actual divided coordinates and remains
a fraction field of the saturated modification. Thus iteration can retain one
field and its original coefficient action, rather than merely equal numerical
transcendence degrees of unrelated fields.
-/

@[expose] public noncomputable section

namespace Algebra.NeronModification

universe u v w

variable {B : Type u} {ι : Type v} [CommRing B] [IsDomain B]
variable (K : Type w) [Field K] [Algebra B K] [IsFractionRing B K]
variable (p : B) (g : ι → B) (hp : p ≠ 0)

/-- The actual fractional point sends each new coordinate to `gᵢ / p`. -/
def fractionPoint : Modification p g →+* K :=
  lift p g (algebraMap B K) (fun i => algebraMap B K (g i) / algebraMap B K p)
    (fun i => by
      rw [mul_div_cancel₀ _
        ((map_ne_zero_iff (algebraMap B K) (IsFractionRing.injective B K)).mpr hp)])
    (isRegular_iff_ne_zero.mpr
      ((map_ne_zero_iff (algebraMap B K) (IsFractionRing.injective B K)).mpr hp))

omit [IsDomain B] in
@[simp] theorem fractionPoint_of (b : B) :
    fractionPoint K p g hp (of p g b) = algebraMap B K b :=
  lift_of _ _ _ _ _ _ b

omit [IsDomain B] in
/-- The common fraction-field point is injective, not just a map. -/
theorem fractionPoint_injective : Function.Injective (fractionPoint K p g hp) :=
  lift_injective p g (algebraMap B K) (IsFractionRing.injective B K) _ _ _

omit [IsDomain B] in
/-- With its actual divided-coordinate action, the old field is still the fraction field. -/
theorem isFractionRing_fractionPoint :
    letI : Algebra (Modification p g) K := (fractionPoint K p g hp).toAlgebra
    IsFractionRing (Modification p g) K := by
  have hsurj : ∀ z : K, ∃ x y : Modification p g,
      z = fractionPoint K p g hp x / fractionPoint K p g hp y := by
    intro z
    obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective B z
    refine ⟨of p g a, of p g b, ?_⟩
    rw [fractionPoint_of, fractionPoint_of]
    exact hab.symm
  let : Algebra (Modification p g) K := (fractionPoint K p g hp).toAlgebra
  let : FaithfulSMul (Modification p g) K :=
    (faithfulSMul_iff_algebraMap_injective (Modification p g) K).mpr
      (fractionPoint_injective K p g hp)
  exact IsFractionRing.of_field (Modification p g) K hsurj

omit [IsDomain B] in
/-- The common-field action is compatible with every original base coefficient. -/
theorem fractionPoint_scalarTower {P : Type*} [CommRing P] [Algebra P B]
    [Algebra P K] [IsScalarTower P B K] :
    letI : Algebra (Modification p g) K := (fractionPoint K p g hp).toAlgebra
    IsScalarTower P (Modification p g) K := by
  let : Algebra (Modification p g) K := (fractionPoint K p g hp).toAlgebra
  refine IsScalarTower.of_algebraMap_eq (R := P) (S := Modification p g) (A := K) ?_
  intro a
  change algebraMap P K a = fractionPoint K p g hp (of p g (algebraMap P B a))
  rw [fractionPoint_of, IsScalarTower.algebraMap_apply P B K]

/-- The native new fraction ring is equivalent to the original field over the original base. -/
def fractionRingAlgEquiv {P : Type*} [CommRing P] [Algebra P B]
    [Algebra P K] [IsScalarTower P B K] : FractionRing (Modification p g) ≃ₐ[P] K := by
  letI : IsDomain (Modification p g) := isDomain_modification p g hp
  letI : Algebra (Modification p g) K := (fractionPoint K p g hp).toAlgebra
  letI : IsFractionRing (Modification p g) K := isFractionRing_fractionPoint K p g hp
  letI : IsScalarTower P (Modification p g) K := fractionPoint_scalarTower K p g hp
  exact (FractionRing.algEquiv (Modification p g) K).restrictScalars P

omit [IsDomain B] in
include hp in
/-- Original transcendence degree is retained under the coefficient-compatible equivalence. -/
theorem lift_trdeg_fractionRing_eq {P : Type*} [CommRing P] [Algebra P B]
    [Algebra P K] [IsScalarTower P B K] :
    Cardinal.lift.{w} (Algebra.trdeg P (FractionRing (Modification p g))) =
      Cardinal.lift.{max u v} (Algebra.trdeg P K) :=
  (fractionRingAlgEquiv K p g hp (P := P)).lift_trdeg_eq

end Algebra.NeronModification
