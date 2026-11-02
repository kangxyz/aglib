/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Value
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.ConstantRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackCoefficientIso

/-! # Bounded finite field trivializations with the original coefficient iso

The existing finite Galois cover and small finite value construction are used
once. The original sheaf annihilator is reflected through the actual constant
functor, so the small constant value is killed by the same integer. No curve
comparison, vanishing, or Galois-module dictionary enters this construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u eY eZ

attribute [local instance] hasSheafifyLarge

/-- The original constant functor on a nonempty scheme reflects the precise
annihilator through an actual coefficient isomorphism. -/
theorem constantValue_killed_of_coefficientIso
    {X : Scheme.{u}} (x : X) (F : AbelianSheaf.{u, u + 1} X)
    (A : AddCommGrpCat.{u + 1})
    (t : F ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
    (n : ℕ) (hF : n • 𝟙 F = 0) : ∀ a : A, n • a = 0 := by
  have hc : n • 𝟙 ((constantSheaf X.smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj A) = 0 := by
    apply (cancel_epi t.hom).mp
    rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
    have h := congrArg (fun a : F ⟶ F => a ≫ t.hom) hF
    simpa using h
  have hv : n • 𝟙 A = 0 := by
    apply Constructible.FiniteColimits.constant_map_injective_at_point X A A x
    simpa using hc
  intro a
  exact ConcreteCategory.congr_hom hv a

/-- A finite locally constant field coefficient has an actual finite Galois
trivialization by a small finite group killed by its original annihilator.
The bound is retained even for n = 0; positivity and invertibility belong to
the subsequent curve theorem, not this finite coefficient construction. -/
theorem exists_finiteGalois_bounded_small_trivialization
    (K : Type u) [Field K]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of K)))
    (hfinite : IsFiniteLocallyConstant F) (n : ℕ) (hF : n • 𝟙 F = 0) :
    ∃ (L : FiniteGaloisIntermediateField K (SeparableClosure K))
      (B : Type u) (_ : AddCommGroup B) (_ : Finite B),
      (∀ b : B, n • b = 0) ∧
      Nonempty ((inverseImage (Spec.algebraMap K L)).obj F ≅
        ConstantFinite.coefficient B (Spec (.of L))) := by
  obtain ⟨L, A, hA, ⟨t⟩⟩ := exists_finiteGalois_trivialization K F hfinite
  let : Finite A := hA
  have hL : n • 𝟙 ((inverseImage (Spec.algebraMap K L)).obj F) = 0 :=
    killedBy_pullback (Spec.algebraMap K L) hF
  have hAn := constantValue_killed_of_coefficientIso (default : Spec (.of L))
    ((inverseImage (Spec.algebraMap K L)).obj F) A t n hL
  obtain ⟨B, hB, hfiniteB, ⟨e⟩⟩ := ConstantFinite.exists_small_finiteValueIso A
  let := hB
  let := hfiniteB
  have hBn (b : B) : n • b = 0 := by
    have h : e.hom (n • ULift.up b) = e.hom 0 := by
      simpa using hAn (e.hom (ULift.up b))
    exact congrArg ULift.down ((Iso.addCommGroupIsoToAddEquiv e).injective h)
  exact ⟨L, B, hB, hfiniteB, hBn,
    ⟨t ≪≫ ((constantSheaf (Spec (.of L)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).mapIso e).symm⟩⟩

/-- A supplied coefficient iso transports zero of the same original class
under the same original geometric pullback, with independent Ext universes. -/
theorem cohomologyPullback_eq_zero_iff_coefficientIso
    {Y Z : Scheme.{u}} (z : Z ⟶ Y)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    {F E : AbelianSheaf.{u, u + 1} Y} (t : F ≅ E)
    (q : ℕ) (c : Sheaf.H.{eY} F q) :
    cohomologyPullback.{u, eY, eZ} z E q (Sheaf.H.map t.hom q c) = 0 ↔
      cohomologyPullback.{u, eY, eZ} z F q c = 0 := by
  rw [cohomologyPullback_coefficientMap]
  constructor
  · intro h
    apply (cohomologyMapIso_bijective ((inverseImage z).mapIso t) q).injective
    simpa using h
  · intro h
    rw [h, map_zero]

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
