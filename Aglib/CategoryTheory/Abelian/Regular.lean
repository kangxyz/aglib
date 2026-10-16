/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Images
public import Aglib.CategoryTheory.Limits.Shapes.RegularKernel

/-!
# Generalized inverses from projective cokernels

If a morphism in an abelian category has projective target and projective
cokernel, its actual image is a retract of the target. Splitting the
original epimorphism onto this projective image gives a generalized inverse
of the original morphism. Neither its source nor its kernel is required
to be projective.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C] {X Y : C} (f : X ⟶ Y)

attribute [local instance] Abelian.hasFiniteBiproducts

/-- For a regular morphism with projective target, projectivity of its original kernel
is equivalent to projectivity of its source. Both directions use actual retractions. -/
theorem projective_kernel_iff_of_generalizedInverse [Projective Y]
    (s : Y ⟶ X) (hs : f ≫ s ≫ f = f) : Projective (kernel f) ↔ Projective X := by
  constructor
  · intro h
    let := h
    exact (sourceRetractOfGeneralizedInverse f s hs).projective
  · intro h
    let := h
    exact (kernelRetractOfGeneralizedInverse f s hs).projective

/-- A projective target and projective original cokernel give an actual generalized
inverse of the displayed morphism. The source need not be projective. -/
theorem exists_generalizedInverse_of_projective_cokernel
    [Projective Y] [Projective (cokernel f)] :
    ∃ s : Y ⟶ X, f ≫ s ≫ f = f := by
  let T := ShortComplex.mk (Abelian.image.ι f) (cokernel.π f)
    (kernel.condition (cokernel.π f))
  have hT : T.ShortExact := {
    exact := T.exact_of_f_is_kernel (kernelIsKernel (cokernel.π f))
    mono_f := by dsimp [T]; infer_instance
    epi_g := by dsimp [T]; infer_instance }
  let : Projective T.X₃ := by
    change Projective (cokernel f)
    infer_instance
  let h := hT.splittingOfProjective
  let v : Y ⟶ Abelian.image f := h.r
  have hv : Abelian.image.ι f ≫ v = 𝟙 (Abelian.image f) := h.f_r
  let r : Retract (Abelian.image f) Y := {
    i := Abelian.image.ι f
    r := v
    retract := hv }
  let : Projective (Abelian.image f) := r.projective
  let q := Abelian.factorThruImage f
  let t := Projective.factorThru (𝟙 (Abelian.image f)) q
  have ht : t ≫ q = 𝟙 _ := Projective.factorThru_comp _ _
  refine ⟨v ≫ t, ?_⟩
  calc
    f ≫ (v ≫ t) ≫ f =
        (q ≫ Abelian.image.ι f) ≫ (v ≫ t) ≫ (q ≫ Abelian.image.ι f) :=
      congrArg₂ (fun a b : X ⟶ Y => a ≫ (v ≫ t) ≫ b)
        (Abelian.image.fac f).symm (Abelian.image.fac f).symm
    _ =
        q ≫ (Abelian.image.ι f ≫ v) ≫ (t ≫ q) ≫ Abelian.image.ι f := by
      simp only [Category.assoc]
    _ = q ≫ Abelian.image.ι f := by
      rw [hv, ht]
      simp only [Category.id_comp]
    _ = f := Abelian.image.fac f

end CategoryTheory.Abelian
