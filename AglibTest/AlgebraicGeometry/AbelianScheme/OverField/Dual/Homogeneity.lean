/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Homogeneity

/-! Original Poincare homogeneity on arbitrary test schemes, under the
explicit geometric conditions on the same native Picard component. -/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
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

example {T : Over (Spec (.of k))} (t : T ⟶ A)
    (d : T ⟶ picardIdentityComponent A.hom P R) :
    universalTranslationClass A t d (poincareClass A P R) =
      pullbackClass (pullback.snd A.hom T.hom)
        (pullbackClass (lift t d).left (poincareClass A P R)) :=
  poincareTranslationClass_eq_basePullback A P R t d

end
