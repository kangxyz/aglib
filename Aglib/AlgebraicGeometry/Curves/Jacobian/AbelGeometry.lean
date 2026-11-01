/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelMorphism
public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardScheme

/-!
# The original ordered Abel morphism into the same Jacobian

Factor the existing ordered graph-family Abel morphism through the actual
identity component of its original Picard representative. The construction
and its whole inclusion equation precede image dimension and theta geometry.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Scheme Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom]

/-- Factor the original ordered Abel morphism through the same Picard
representative's identity component. -/
def jacobianAbelMorphism (n : ℕ) :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    parameter X.hom n ⟶ identityComponentOver P.obj := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  exact liftIdentityComponent P.obj (abelMorphism o ho P R n).hom
    (range_abelMorphism_subset_identityComponent o ho P R hX n)

/-- The factorization preserves the original scheme morphism. -/
theorem jacobianAbelMorphism_comp_inclusion (n : ℕ) :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    jacobianAbelMorphism hX o ho P R n ≫ identityComponentι P.obj =
      (abelMorphism o ho P R n).hom := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  exact liftIdentityComponent_ι P.obj (abelMorphism o ho P R n).hom
    (range_abelMorphism_subset_identityComponent o ho P R hX n)

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
