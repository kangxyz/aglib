/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.Core
public import Aglib.AlgebraicGeometry.Picard.Fppf
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver

/-!
# The original bounded Abel family in a relative Picard representation

The parameter is the original finite product over the original base. Its graph
line bundle defines a section of the original fppf Picard sheaf; the given
representation sends that section to a morphism into the same representing
scheme. Naturality identifies the morphism on every locally Noetherian test.
This is the arbitrary-base construction underlying the field specialization in
`Curves.Jacobian.AbelMorphism`; it asserts neither stratum properness nor coverage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- The original proper tuple parameter, viewed as a locally Noetherian test. -/
def locallyNoetherianParameterOver [IsLocallyNoetherian S] [IsProper p]
    (n : ℕ) : LocallyNoetherianOver S :=
  ⟨parameter p n, LocallyOfFiniteType.isLocallyNoetherian (parameter p n).hom⟩

section Separated

variable [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- The original graph-sum line bundle as a section of the fppf Picard sheaf. -/
def abelSectionOver (n : ℕ) : (fppfPicardSheaf p).obj.obj (op (parameter p n)) :=
  (quotientProjection p ≫ toFppfPicardSheaf p).app (op (parameter p n))
    (classOf _ (lineBundle p o ho n))

end Separated

variable [SmoothOfRelativeDimension 1 p] [IsLocallyNoetherian S] [IsProper p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  (P : LocallyNoetherianOver S)
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The actual bounded Abel morphism into the given relative representation. -/
def abelMorphismOver (n : ℕ) : locallyNoetherianParameterOver p n ⟶ P :=
  R.homEquiv.symm (abelSectionOver p o ho n)

/-- The given representation sends the Abel map to the original graph family. -/
theorem homEquiv_abelMorphismOver (n : ℕ) :
    R.homEquiv (abelMorphismOver p o ho P R n) = abelSectionOver p o ho n :=
  R.homEquiv.apply_symm_apply _

/-- On every test the same representation gives the pullback of the original
line-bundle class along the original family map. -/
theorem homEquiv_comp_abelMorphismOver {n : ℕ} {T : LocallyNoetherianOver S}
    (a : T ⟶ locallyNoetherianParameterOver p n) :
    R.homEquiv (a ≫ abelMorphismOver p o ho P R n) =
      (quotientProjection p ≫ toFppfPicardSheaf p).app (op T.obj)
        (pullbackClass ((familyScheme p).map a.hom) (classOf _ (lineBundle p o ho n))) := by
  rw [R.homEquiv_comp, homEquiv_abelMorphismOver]
  exact (NatTrans.naturality_apply (quotientProjection p ≫ toFppfPicardSheaf p)
    a.hom.op (classOf _ (lineBundle p o ho n))).symm

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
