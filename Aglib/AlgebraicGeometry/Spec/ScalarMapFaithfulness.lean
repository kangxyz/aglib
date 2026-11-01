/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.AdicSectionRetraction

/-! # Original affine maps detected by injective scalar sections -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- Scalar composition retains the original ring map, without a new algebra action. -/
theorem affineScalarMap_comp_specMap
    {A B : Type u} [CommRing A] [CommRing B] {U : Scheme.{u}}
    (j : U ⟶ Spec (.of A)) (f : B →+* A) :
    affineScalarMap (j ≫ Spec.map (CommRingCat.ofHom f)) =
      (affineScalarMap j).comp f := by
  have h := affineScalarMap_square (𝟙 U) j
    (j ≫ Spec.map (CommRingCat.ofHom f)) f (by simp)
  simpa only [Hom.id_appTop, CommRingCat.hom_id, RingHom.id_comp] using h

/-- The original restriction detects maps between affine schemes whenever
its original scalar map is injective. No density model or field is chosen. -/
theorem affine_hom_ext_of_scalar_injective
    {A B : Type u} [CommRing A] [CommRing B] {U : Scheme.{u}}
    (j : U ⟶ Spec (.of A)) (hj : Function.Injective (affineScalarMap j))
    {f g : Spec (.of A) ⟶ Spec (.of B)} (h : j ≫ f = j ≫ g) : f = g := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  have he := congrArg affineScalarMap h
  have he' : (affineScalarMap j).comp f.hom = (affineScalarMap j).comp g.hom :=
    (affineScalarMap_comp_specMap j f.hom).symm.trans
      (he.trans (affineScalarMap_comp_specMap j g.hom))
  have hfg : f = g := by
    ext b
    exact hj (RingHom.congr_fun he' b)
  rw [hfg]

end AlgebraicGeometry.Scheme
