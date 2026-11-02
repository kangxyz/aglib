/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.Torsion.RepresentedConstructible
public import Aglib.AlgebraicGeometry.Picard.Representability.FineStrata

/-! # Constructibility from the actual projective Picard construction

The original representative and its properties are constructed internally.
The supplied-representative endpoints are re-exported from `RepresentedConstructible`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w s v

namespace AlgebraicGeometry.Scheme.OverField.Curve.PicardTorsion

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {ιX : Type u} {Y : Scheme.{u}}
  (i : Y ⟶ ProjectiveSpace A ιX) [IsClosedImmersion i]
  {N : ℕ} (e : ιX ≃ Fin (N + 1))
  [SmoothOfRelativeDimension 1 (i ≫ toSpec A ιX)]
  [IsProper (i ≫ toSpec A ιX)] [Flat (i ≫ toSpec A ιX)]
  [GeometricallyIntegral (i ≫ toSpec A ιX)]
  [GeometricallyConnected (i ≫ toSpec A ιX)]
  (o : Spec (.of A) ⟶ Y) (ho : o ≫ (i ≫ toSpec A ιX) = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of A))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec A ιX)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
    [∀ U : (Spec (.of A)).Etale, HasExt.{s}
      (Sheaf ((Scheme.smallEtaleTopology Y).over
        ((siteBaseChange (i ≫ toSpec A ιX)).obj U)) AddCommGrpCat.{u + 1})]
    [∀ Z : Scheme.{u}, HasExt.{v} (AbelianSheaf.{u, u + 1} Z)]

include e o ho in
omit [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)] in
/-- The existing projective Picard construction removes any external representability
premise from the original R1 mu constructibility endpoint. -/
theorem isConstructible_rootsHigherDirectImage
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : A)) :
    IsConstructible ((higherDirectImage (i ≫ toSpec A ιX) 1).obj (mu Y n)) := by
  obtain ⟨P, R, _, _, hsep, hP, _⟩ := exists_representableBy_fppfPicardSheaf i e
  let := hP
  let := hsep
  exact isConstructible_rootsHigherDirectImage_withRepresenter i e o ho P R n hn hinv

end AlgebraicGeometry.Scheme.OverField.Curve.PicardTorsion
