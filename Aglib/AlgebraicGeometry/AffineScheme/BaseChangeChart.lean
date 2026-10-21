/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.TensorPullback
public import Aglib.AlgebraicGeometry.Limits.Range

/-!
# Original tensor-coordinate charts of affine base change

An actual affine chart over the base gives a chart with its literal tensor
coordinate ring after arbitrary base change. The projection equations and
cartesian square retain the specified chart and scalar maps.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.AffineBaseChange

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (j : Spec (CommRingCat.of B) ⟶ X)
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A B)))

/-- The canonical tensor affine square, with the original tensor factors. -/
theorem tensorChart_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] C))))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
  (Spec.isPullback_of_tensorEquiv (AlgEquiv.refl : B ⊗[A] C ≃ₐ[B] B ⊗[A] C)
    (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom rfl).flip

/-- The actual affine chart after base change, with coordinate ring `B ⊗[A] C`. -/
def tensorChartMap : Spec (CommRingCat.of (B ⊗[A] C)) ⟶
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] C))) ≫ j)
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom)) (by
        rw [Category.assoc, hj]
        exact (tensorChart_isPullback (A := A) (B := B) (C := C)).w)

@[reassoc (attr := simp)]
theorem tensorChartMap_fst :
    tensorChartMap (C := C) f j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] C))) ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem tensorChartMap_snd :
    tensorChartMap (C := C) f j hj ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom) :=
  pullback.lift_snd _ _ _

/-- The tensor chart is the original affine chart pulled back along the
projection, without a flatness hypothesis on either algebra. -/
theorem tensorChartMap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] C))))
      (tensorChartMap (C := C) f j hj) j
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A C)))) := by
  apply IsPullback.flip
  apply IsPullback.of_right (h₁₂ := pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap A C)))) (h₂₂ := f)
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap A C)))
    _ (tensorChartMap_fst f j hj) (IsPullback.of_hasPullback _ _).flip
  simpa only [tensorChartMap_snd, hj] using
    (tensorChart_isPullback (A := A) (B := B) (C := C)).flip

instance tensorChartMap_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (tensorChartMap (C := C) f j hj) :=
  MorphismProperty.of_isPullback (tensorChartMap_isPullback f j hj) inferInstance

/-- The tensor chart covers precisely the inverse image of the original
chart, so any original finite affine cover remains a cover after base change. -/
theorem tensorChartMap_range :
    Set.range (tensorChartMap (C := C) f j hj) =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹' Set.range j :=
  Scheme.Pullback.Transport.range_eq_preimage_of_isPullback
    (tensorChartMap_isPullback f j hj).flip

end AlgebraicGeometry.Scheme.AffineBaseChange
