/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.AdicSectionRetraction

/-! # Original affine isomorphisms reflected by scalar section squares

An isomorphism on the specified comparison schemes determines the unchanged
bottom ring map when their original scalar maps recover global sections.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The original scalar square reflects bijectivity of its bottom ring map.
Only injectivity, not surjectivity, is needed for the second scalar map. -/
theorem ringHom_bijective_of_affineScalarSquare
    {B C : Type u} [CommRing B] [CommRing C] {X Y : Scheme.{u}}
    (p : Y ⟶ X) [IsIso p] (q : Y ⟶ Spec (.of C)) (f : X ⟶ Spec (.of B))
    (σ : B →+* C) (h : p ≫ f = q ≫ Spec.map (CommRingCat.ofHom σ))
    (hf : Function.Bijective (affineScalarMap f))
    (hq : Function.Injective (affineScalarMap q)) : Function.Bijective σ := by
  have hs : Function.Bijective ((affineScalarMap q).comp σ) := by
    rw [← affineScalarMap_square p q f σ h]
    have hp : Function.Bijective p.appTop.hom := by
      change Function.Bijective (Scheme.Γ.map p.op).hom
      exact ConcreteCategory.bijective_of_isIso (Scheme.Γ.map p.op)
    exact hp.comp hf
  exact Function.Bijective.of_comp_left
    (f := affineScalarMap q) (g := σ) hs hq

/-- The affine morphism itself is an isomorphism, not only an abstract
comparison of coordinate rings. -/
theorem isIso_specMap_of_affineScalarSquare
    {B C : Type u} [CommRing B] [CommRing C] {X Y : Scheme.{u}}
    (p : Y ⟶ X) [IsIso p] (q : Y ⟶ Spec (.of C)) (f : X ⟶ Spec (.of B))
    (σ : B →+* C) (h : p ≫ f = q ≫ Spec.map (CommRingCat.ofHom σ))
    (hf : Function.Bijective (affineScalarMap f))
    (hq : Function.Injective (affineScalarMap q)) :
    IsIso (Spec.map (CommRingCat.ofHom σ)) := by
  let : IsIso (CommRingCat.ofHom σ) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (ringHom_bijective_of_affineScalarSquare p q f σ h hf hq)
  infer_instance

end AlgebraicGeometry.Scheme
