/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Multiplication

/-! Native multiplication, including zero/one, on the original Picard component. -/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry Scheme.Modules.Invertible Scheme.RelativePicard

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [GeometricallyIntegral A.hom]
  (P : Scheme.LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((Scheme.locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf A.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsProper (picardIdentityComponent A.hom P R).hom]
  [GeometricallyIntegral (picardIdentityComponent A.hom P R).hom]

example (n : ℕ) :
    picardIdentityComponentPullback P R P R ((𝟙 A) ^ n) =
      (𝟙 (picardIdentityComponent A.hom P R)) ^ n :=
  picardIdentityComponentPullback_multiplication A P R n

example : picardIdentityComponentPullback P R P R (𝟙 A) =
    𝟙 (picardIdentityComponent A.hom P R) := by
  simpa only [pow_one] using picardIdentityComponentPullback_multiplication A P R 1

example {T : Over (Spec (.of k))} (f : T ⟶ A)
    (d : T ⟶ picardIdentityComponent A.hom P R) (n : ℕ) :
    pullbackClass (lift (f ^ n) d).left (poincareClass A P R) =
      n • pullbackClass (lift f d).left (poincareClass A P R) :=
  poincareClass_pullback_pow A P R f d n

end
