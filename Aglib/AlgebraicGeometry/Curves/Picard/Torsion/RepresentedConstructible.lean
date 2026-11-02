/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.Torsion.SheafKernelConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.RepresentedComparison

/-! # Constructibility of the original projective curve Picard torsion

The same Picard representative supplies the original multiplication kernel.
Its finiteness and formal unramifiedness are constructed, not assumed.
The final endpoint uses the original relative Kummer comparison for literal R1 mu.
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

include e o ho P R in
omit [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)] in
/-- Literal R1 mu constructibility, using the original relative Kummer isomorphism. -/
theorem isConstructible_rootsHigherDirectImage_withRepresenter
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : A)) :
    IsConstructible ((higherDirectImage (i ≫ toSpec A ιX) 1).obj (mu Y n)) := by
  have hS : IsUnit (n : Γ(Spec (.of A), ⊤)) := by
    simpa only [map_natCast] using hinv.map (Scheme.ΓSpecIso (.of A)).inv.hom
  have hY := levelInvertible (i ≫ toSpec A ιX) n hS
  apply (isConstructible_iff_of_iso
    (Kummer.rootsHigherDirectImagePicardRepresenterTorsionIso
      (i ≫ toSpec A ιX) n hn hY o ho P R)).mpr
  exact isConstructible_picardSheafKernel i e o ho P R n hn hinv

end AlgebraicGeometry.Scheme.OverField.Curve.PicardTorsion
