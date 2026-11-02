/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.Torsion.GenericFiniteEtale
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.Constructible

/-! # Constructibility of the original projective curve Picard torsion

The same Picard representative supplies the original multiplication kernel.
Its finiteness and formal unramifiedness are constructed, not assumed.
The separate relative Kummer comparison and R1 mu endpoint are downstream.
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

universe u

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

include e o ho in
/-- Constructibility of the literal sheaf multiplication kernel for the same P/R. -/
theorem isConstructible_picardSheafKernel (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : A)) :
    letI := picardCommGrpObj (i ≫ toSpec A ιX) P R
    IsConstructible (kernel (n • 𝟙 (representedSheaf (Grp.mk P.obj)))) := by
  let := picardCommGrpObj (i ≫ toSpec A ιX) P R
  let : IsFinite (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom :=
    isFinite_kernel_of_isUnit i e o ho P R n hn hinv
  let : FormallyUnramified (Group.Kernel.group ((𝟙 (Grp.mk P.obj)) ^ n)).X.hom :=
    formallyUnramified_kernel_of_isUnit i e o ho P R n hn hinv
  exact RepresentedKernel.Native.isConstructible_multiplicationKernel (Grp.mk P.obj) n hn

end AlgebraicGeometry.Scheme.OverField.Curve.PicardTorsion
