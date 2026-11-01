/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PrincipalLocalizationZero
public import Aglib.AlgebraicGeometry.Spec.PrincipalFractionProjection
public import Mathlib.AlgebraicGeometry.FunctionField

/-! # The same generic-cover zero spreads to a base open

The cover and the original constant class are unchanged. Zero is obtained on
the cover's inverse image of a nonempty base open, which need not contain the
closed base point. This is an open piece of support induction, not strict-local
target effacement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

open Curves

/-- The original class on a qcqs source which is zero generically is zero on
an actual nonempty base-open inverse image of the same source. -/
theorem exists_fraction_baseOpen_composite_zero
    (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {Z X : Scheme.{u}} [CompactSpace Z] [QuasiSeparatedSpace Z]
    (pZ : Z ⟶ Spec (.of R)) (h : Z ⟶ X)
    (A : Type u) [AddCommGroup A] (n : ℕ)
    (c : Sheaf.H.{u + 2} (coefficient A X) n)
    (hc : constantRestriction A (pullback.fst pZ (Spec.algebraMap R K) ≫ h) n c = 0) :
    ∃ (W : (Spec (.of R)).Opens) (_ : Nonempty W),
      constantRestriction A ((pZ ⁻¹ᵁ W).ι ≫ h) n c = 0 := by
  have hcZ : constantRestriction A (pullback.fst pZ (Spec.algebraMap R K)) n
      (constantRestriction A h n c) = 0 :=
    (constantRestriction_comp A h (pullback.fst pZ (Spec.algebraMap R K)) n c).symm.trans hc
  obtain ⟨t, ht⟩ := PrincipalLocalization.exists_principalOpen_constantRestriction_eq_zero
    R⁰ K pZ A n (constantRestriction A h n c) hcZ
  let W := stageBaseOpen R⁰ t
  have hW : Nonempty W := by
    let x : Spec (.of (stage R⁰ t)) := Classical.choice inferInstance
    refine ⟨⟨(Spec.algebraMap R (stage R⁰ t)) x, ?_⟩⟩
    exact ⟨x, rfl⟩
  refine ⟨W, hW, ?_⟩
  exact (constantRestriction_comp A h (stageSourceOpen R⁰ pZ t).ι n c).trans ht

/-- An exact reconstruction on the restricted original generic fibre carries
its original class-zero to the same cover. It then spreads only to a nonempty
base open; no neighborhood of the closed base point is asserted. -/
theorem exists_genericCover_baseOpen_zero
    (R : Type u) [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (V : X.Opens)
    (G : FiniteEtale V) [CompactSpace G.obj.left] [QuasiSeparatedSpace G.obj.left]
    (Y : FiniteEtale (pullback p
      ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))))))
    (e : (FiniteEtale.baseChange ((pullback.fst p _) ∣_ V)).obj G ≅
      (FiniteEtale.baseChange ((pullback.fst p _) ⁻¹ᵁ V).ι).obj Y)
    (A : Type u) [AddCommGroup A] (n : ℕ)
    (c : Sheaf.H.{u + 2} (coefficient A X) n)
    (hc : constantRestriction A (Y.obj.hom ≫ pullback.fst p _) n c = 0) :
    ∃ (W : (Spec (.of R)).Opens) (_ : Nonempty W),
      constantRestriction A
        (((G.obj.hom ≫ V.ι ≫ p) ⁻¹ᵁ W).ι ≫ G.obj.hom ≫ V.ι) n c = 0 := by
  let γ := (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R)))
  let B : Scheme.{u} := pullback p γ
  let π : B ⟶ X := pullback.fst p γ
  let U : B.Opens := π ⁻¹ᵁ V
  let q : U.toScheme ⟶ V.toScheme := π ∣_ V
  let T : Scheme.{u} := pullback G.obj.hom q
  let h : G.obj.left ⟶ X := G.obj.hom ≫ V.ι
  let pG : G.obj.left ⟶ Spec (.of R) := G.obj.hom ≫ V.ι ≫ p
  let eMap : T ⟶ pullback Y.obj.hom U.ι := e.hom.hom.left
  have heMap : eMap ≫ pullback.snd Y.obj.hom U.ι = pullback.snd G.obj.hom q :=
    Over.w e.hom.hom
  let z : T ⟶ Y.obj.left := eMap ≫ pullback.fst Y.obj.hom U.ι
  have hz : z ≫ (Y.obj.hom ≫ π) = pullback.fst G.obj.hom q ≫ h := by
    dsimp only [z, h]
    rw [Category.assoc, ← Category.assoc (pullback.fst Y.obj.hom U.ι),
      pullback.condition, Category.assoc, ← Category.assoc eMap,
      heMap, ← morphismRestrict_ι, ← Category.assoc,
      ← pullback.condition, Category.assoc]
  have hT : constantRestriction A (pullback.fst G.obj.hom q ≫ h) n c = 0 := by
    rw [← hz, constantRestriction_comp, hc, map_zero]
  have H : IsPullback (pullback.fst G.obj.hom q)
      (pullback.snd G.obj.hom q ≫ U.ι ≫ pullback.snd p γ) pG γ := by
    simpa only [pG, h, Category.assoc] using
      (((IsPullback.of_hasPullback G.obj.hom q).paste_vert
        (isPullback_morphismRestrict π V)).paste_vert
          (IsPullback.of_hasPullback p γ))
  have hgeneric : constantRestriction A (pullback.fst pG γ ≫ h) n c = 0 := by
    rw [← H.isoPullback_inv_fst, Category.assoc, constantRestriction_comp, hT, map_zero]
  let : Algebra R (Spec (.of R)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  let : IsFractionRing R (Spec (.of R)).functionField :=
    functionField_isFractionRing_of_affine (.of R)
  have hγ : γ = Spec.algebraMap R (Spec (.of R)).functionField :=
    Spec.fromSpecStalk_eq' (.of R) (genericPoint (Spec (.of R)))
  rw [hγ] at hgeneric
  exact exists_fraction_baseOpen_composite_zero R (Spec (.of R)).functionField
    pG h A n c hgeneric

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
