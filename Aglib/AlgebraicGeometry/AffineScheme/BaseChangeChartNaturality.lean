/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.BaseChangeChart

/-! # Original transition maps between tensor-coordinate charts -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.AffineBaseChange

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (j : Spec (CommRingCat.of B) ⟶ X) (k : Spec (CommRingCat.of D) ⟶ X)
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A B)))
  (hk : k ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A D)))
  (b : B →ₐ[A] D) (hb : Spec.map (CommRingCat.ofHom b.toRingHom) ≫ j = k)

include hb in
/-- The original tensor extension of a chart restriction commutes with both
projections and hence with the actual base-changed chart maps. -/
@[reassoc]
theorem tensorChartMap_naturality :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map b (AlgHom.id A C)).toRingHom) ≫
        tensorChartMap (C := C) f j hj = tensorChartMap (C := C) f k hk := by
  apply pullback.hom_ext
  · simp only [Category.assoc, tensorChartMap_fst]
    rw [← Category.assoc, ← Spec.map_comp]
    have hleft :
        CommRingCat.ofHom (algebraMap B (B ⊗[A] C)) ≫
          CommRingCat.ofHom (Algebra.TensorProduct.map b (AlgHom.id A C)).toRingHom =
        CommRingCat.ofHom b.toRingHom ≫
          CommRingCat.ofHom (algebraMap D (D ⊗[A] C)) := by
      ext x
      simp
    rw [hleft, Spec.map_comp, Category.assoc, hb]
  · simp only [Category.assoc, tensorChartMap_snd]
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp

end AlgebraicGeometry.Scheme.AffineBaseChange
