/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.FiniteMatrixBaseChange
public import Aglib.LinearAlgebra.Matrix.SquareZeroLift

/-!
# Finite projective modules over a square-zero extension

Lift an actual finite projector and take its image. The existing finite-free
scalar-extension comparison identifies its original base change with the
specified module. This is object lifting, without a choice of local bases or
an assumption that the original ring extension splits.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Matrix

variable {R : Type*} [CommRing R] {n : ℕ} (p : Matrix (Fin n) (Fin n) R)

/-- The original image projection of a finite matrix. -/
def imageRetraction : (Fin n → R) →ₗ[R] LinearMap.range p.mulVecLin :=
  p.mulVecLin.rangeRestrict

/-- An idempotent matrix acts as the identity on its actual image. -/
theorem imageRetraction_comp_subtype (hp : p * p = p) :
    p.imageRetraction.comp (LinearMap.range p.mulVecLin).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change p *ᵥ x.val = x.val
  rw [← hy]
  change p *ᵥ (p *ᵥ y) = p *ᵥ y
  rw [Matrix.mulVec_mulVec, hp]

/-- The original image of an idempotent finite matrix is projective. -/
theorem projective_range_of_idempotent (hp : p * p = p) :
    Module.Projective R (LinearMap.range p.mulVecLin) :=
  Module.Projective.of_split _ p.imageRetraction (p.imageRetraction_comp_subtype hp)

/-- The image of a finite matrix is finite over the original scalar ring. -/
theorem finite_range : Module.Finite R (LinearMap.range p.mulVecLin) :=
  Module.Finite.of_surjective p.imageRetraction (by
    rintro ⟨x, y, rfl⟩
    exact ⟨y, rfl⟩)

/-- The projector of the original image inclusion and retraction is the
original matrix, without a change of coordinates. -/
theorem retractMatrix_imageRetraction :
    Module.Projective.retractMatrix (LinearMap.range p.mulVecLin).subtype
      p.imageRetraction = p := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (Module.Projective.retractMatrix (LinearMap.range p.mulVecLin).subtype
    p.imageRetraction).mulVecLin x = p.mulVecLin x
  rw [Module.Projective.retractMatrix_apply]
  rfl

end Matrix

namespace ModuleCat

open Module.Projective

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- A finite projective module lifts across a surjective square-zero extension.
The comparison is for the original extension-of-scalars functor. -/
theorem exists_finite_projective_lift_of_square_zero (f : R →+* S)
    (hsurj : Function.Surjective f) (hf : RingHom.ker f ^ 2 = ⊥)
    (M : ModuleCat.{u} S) [Module.Finite S M] [Module.Projective S M] :
    ∃ N : ModuleCat.{u} R, Module.Finite R N ∧ Module.Projective R N ∧
      Nonempty ((extendScalars f).obj N ≅ M) := by
  obtain ⟨n, r, i, _, _, hi⟩ := Module.Finite.exists_comp_eq_id_of_projective S M
  obtain ⟨p, hp, hmap⟩ := Matrix.exists_idempotent_lift_of_square_zero f hsurj hf
    (retractMatrix i r) (retractMatrix_idempotent i r hi)
  let N : ModuleCat.{u} R := ModuleCat.of R (LinearMap.range p.mulVecLin)
  refine ⟨N, p.finite_range, p.projective_range_of_idempotent hp, ?_⟩
  let e := extendScalarsRetractImageIso f N (LinearMap.range p.mulVecLin).subtype
    p.imageRetraction (p.imageRetraction_comp_subtype hp)
  have he : (retractMatrix (LinearMap.range p.mulVecLin).subtype
      p.imageRetraction).map f = retractMatrix i r := by
    rw [p.retractMatrix_imageRetraction]
    exact hmap
  let e' := (LinearEquiv.ofEq _ _ (congrArg
    (fun q : Matrix (Fin n) (Fin n) S => LinearMap.range q.mulVecLin) he)).toModuleIso
  exact ⟨e ≪≫ e' ≪≫ (retractMatrixImageIso i r hi).symm.toModuleIso⟩

end ModuleCat
