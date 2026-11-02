/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Affine-target maps descend through an isomorphism on global sections

The original Gamma--Spec adjunction proves bijectivity of literal
precomposition. Over-category triangles are reflected using the same result
for the affine base. No affineness of the source or geometric connectedness
is assumed, and no new representation of the target is selected.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

universe u

/-- Maps to the original spectrum descend uniquely along an isomorphism on
the actual global sections. -/
theorem bijective_precomp_spec_of_isIso_appTop
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsIso q.appTop] (R : CommRingCat.{u}) :
    Function.Bijective (fun a : Y ⟶ Spec R => q ≫ a) := by
  have : IsIso (Scheme.Γ.rightOp.map q) := by
    change IsIso q.appTop.op
    infer_instance
  constructor
  · intro a b hab
    change q ≫ a = q ≫ b at hab
    apply (ΓSpec.adjunction.homEquiv Y (op R)).symm.injective
    apply (cancel_epi (Scheme.Γ.rightOp.map q)).mp
    rw [← ΓSpec.adjunction.homEquiv_naturality_left_symm,
      ← ΓSpec.adjunction.homEquiv_naturality_left_symm, hab]
  · intro a
    let b := ΓSpec.adjunction.homEquiv Y (op R)
      (inv (Scheme.Γ.rightOp.map q) ≫ (ΓSpec.adjunction.homEquiv X (op R)).symm a)
    refine ⟨b, ?_⟩
    apply (ΓSpec.adjunction.homEquiv X (op R)).symm.injective
    rw [ΓSpec.adjunction.homEquiv_naturality_left_symm]
    simp only [b, Equiv.symm_apply_apply, ← Category.assoc, IsIso.hom_inv_id,
      Category.id_comp]

/-- Literal precomposition is bijective for every affine target. -/
theorem bijective_precomp_of_isAffine_of_isIso_appTop
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsIso q.appTop]
    (Z : Scheme.{u}) [IsAffine Z] :
    Function.Bijective (fun a : Y ⟶ Z => q ≫ a) := by
  have h := bijective_precomp_spec_of_isIso_appTop q Γ(Z, ⊤)
  constructor
  · intro a b hab
    apply (cancel_mono Z.isoSpec.hom).mp
    apply h.injective
    simpa only [← Category.assoc] using congrArg (fun k => k ≫ Z.isoSpec.hom) hab
  · intro a
    obtain ⟨b, hb⟩ := h.surjective (a ≫ Z.isoSpec.hom)
    change q ≫ b = a ≫ Z.isoSpec.hom at hb
    refine ⟨b ≫ Z.isoSpec.inv, ?_⟩
    change q ≫ (b ≫ Z.isoSpec.inv) = a
    rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The same original precomposition bijection preserves and reflects the
actual Over triangles when the base and target are affine. -/
theorem bijective_over_precomp_of_isIso_appTop
    {S : Scheme.{u}} [IsAffine S] {X Y Z : Over S} [IsAffine Z.left]
    (a : X ⟶ Y) [IsIso a.left.appTop] :
    Function.Bijective (fun b : Y ⟶ Z => a ≫ b) := by
  have h := bijective_precomp_of_isAffine_of_isIso_appTop a.left Z.left
  constructor
  · intro b c hbc
    apply Over.OverMorphism.ext
    apply h.injective
    exact congrArg (fun k => k.left) hbc
  · intro b
    obtain ⟨c, hc⟩ := h.surjective b.left
    change a.left ≫ c = b.left at hc
    have hw : c ≫ Z.hom = Y.hom := by
      apply (bijective_precomp_of_isAffine_of_isIso_appTop a.left S).injective
      change a.left ≫ (c ≫ Z.hom) = a.left ≫ Y.hom
      rw [← Category.assoc, hc]
      exact b.w.trans a.w.symm
    refine ⟨Over.homMk c hw, ?_⟩
    apply Over.OverMorphism.ext
    exact hc

end AlgebraicGeometry.Scheme
