/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.GenericCoefficientZeroSpreading

/-! # Arbitrary-coefficient zero on the original reconstructed generic cover

The supplied reconstruction is only over the inverse image of the original
open V. It identifies actual finite etale covers, not cohomology models.
An original arbitrary-coefficient class zero on the generic cover becomes
zero on the same reconstructed cover over a nonempty principal base open.
This is support-induction input and does not assert target-point coverage.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u eX e eY

attribute [local instance] hasSheafifyLarge

/-- Exact generic reconstruction carries an original arbitrary-coefficient
zero to the unchanged cover over a nonzero principal base open. All Ext
worlds and the original composite class map remain explicit. -/
theorem exists_genericCover_principalOpen_cohomologyPullback_eq_zero
    (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (V : X.Opens)
    (G : FiniteEtale V) [CompactSpace G.obj.left] [QuasiSeparatedSpace G.obj.left]
    (Y : FiniteEtale (pullback p (Spec.algebraMap R K)))
    (E : (FiniteEtale.baseChange ((pullback.fst p (Spec.algebraMap R K)) ∣_ V)).obj G ≅
      (FiniteEtale.baseChange ((pullback.fst p (Spec.algebraMap R K)) ⁻¹ᵁ V).ι).obj Y)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y.obj.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} G.obj.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback G.obj.hom ((pullback.fst p (Spec.algebraMap R K)) ∣_ V)))]
    [HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback (G.obj.hom ≫ V.ι ≫ p) (Spec.algebraMap R K)))]
    [∀ s : Finset R⁰, HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((PrincipalNeighborhoodLimit.baseChangeDiagram R⁰ (G.obj.hom ≫ V.ι ≫ p)).obj
        (op s)))]
    [∀ s : Finset R⁰, HasExt.{e} (AbelianSheaf.{u, u + 1}
      (stageSourceOpen R⁰ (G.obj.hom ≫ V.ι ≫ p) s))]
    [HasColimitsOfShape (Finset R⁰) AddCommGrpCat.{e}] [UnivLE.{u, e}]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{eX} F q)
    (hc : cohomologyPullback.{u, eX, eY}
      (Y.obj.hom ≫ pullback.fst p (Spec.algebraMap R K)) F q c = 0) :
    ∃ s : Finset R⁰, denominator R⁰ s ≠ 0 ∧ Nonempty (stageBaseOpen R⁰ s) ∧
      cohomologyPullback.{u, eX, e}
        ((stageSourceOpen R⁰ (G.obj.hom ≫ V.ι ≫ p) s).ι ≫ G.obj.hom ≫ V.ι) F q c = 0 := by
  let γ := Spec.algebraMap R K
  let B : Scheme.{u} := pullback p γ
  let π : B ⟶ X := pullback.fst p γ
  let U : B.Opens := π ⁻¹ᵁ V
  let r : U.toScheme ⟶ V.toScheme := π ∣_ V
  let T : Scheme.{u} := pullback G.obj.hom r
  let h : G.obj.left ⟶ X := G.obj.hom ≫ V.ι
  let pG : G.obj.left ⟶ Spec (.of R) := G.obj.hom ≫ V.ι ≫ p
  let eMap : T ⟶ pullback Y.obj.hom U.ι := E.hom.hom.left
  have heMap : eMap ≫ pullback.snd Y.obj.hom U.ι = pullback.snd G.obj.hom r :=
    Over.w E.hom.hom
  let z : T ⟶ Y.obj.left := eMap ≫ pullback.fst Y.obj.hom U.ι
  have hz : z ≫ (Y.obj.hom ≫ π) = pullback.fst G.obj.hom r ≫ h := by
    dsimp only [z, h]
    rw [Category.assoc, ← Category.assoc (pullback.fst Y.obj.hom U.ι),
      pullback.condition, Category.assoc, ← Category.assoc eMap,
      heMap, ← morphismRestrict_ι, ← Category.assoc,
      ← pullback.condition, Category.assoc]
  have H : IsPullback (pullback.fst G.obj.hom r)
      (pullback.snd G.obj.hom r ≫ U.ι ≫ pullback.snd p γ) pG γ := by
    simpa only [pG, h, Category.assoc] using
      (((IsPullback.of_hasPullback G.obj.hom r).paste_vert
        (isPullback_morphismRestrict π V)).paste_vert
          (IsPullback.of_hasPullback p γ))
  exact exists_fraction_principalOpen_composite_zero_of_reconstruction R K pG h
    (pullback.fst G.obj.hom r)
    (pullback.snd G.obj.hom r ≫ U.ι ≫ pullback.snd p γ) H
    z (Y.obj.hom ≫ π) hz F q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
