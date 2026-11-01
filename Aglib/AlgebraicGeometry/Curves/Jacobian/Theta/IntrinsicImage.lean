/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.Positive
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.AbelGeometry

/-!
# The positive Abel image without a rational base point

Classify the existing positive graph-divisor family into the same supplied
Picard representative. The original ordered parameter scheme and original
fppf class maps are retained. No rational point is needed to construct this
morphism or its actual integral schematic image.

The classifying identities hold on the represented locally Noetherian test
site, including nonreduced tests. Comparison with the chosen degree stratum,
the based theta Cartier divisor, and the selected Hilbert divisor image is
separate; none is assumed by the definitions here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] (X : FScheme k)
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-- The original fppf section of the positive ordered divisor family. -/
def positiveAbelSection (n : ℕ) :
    (fppfPicardSheaf X.hom).obj.obj (op (parameter X.hom n)) :=
  (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op (parameter X.hom n))
    (classOf _ (positiveFamilyLineBundle X.hom n))

variable (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The positive degree-n Abel morphism into the same Picard representative,
without an origin choice. -/
def positiveAbelMorphism (n : ℕ) : locallyNoetherianParameter X n ⟶ P :=
  R.homEquiv.symm (positiveAbelSection X n)

theorem homEquiv_positiveAbelMorphism (n : ℕ) :
    R.homEquiv (positiveAbelMorphism X P R n) = positiveAbelSection X n :=
  R.homEquiv.apply_symm_apply _

/-- Classification after every original parameter map on the represented
test site; this is not merely a formula at field-valued points. -/
theorem homEquiv_comp_positiveAbelMorphism {n : ℕ}
    {T : LocallyNoetherianOver (Spec (.of k))} (a : T ⟶ locallyNoetherianParameter X n) :
    R.homEquiv (a ≫ positiveAbelMorphism X P R n) =
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
        (pullbackClass ((familyScheme X.hom).map a.hom)
          (classOf _ (positiveFamilyLineBundle X.hom n))) := by
  rw [R.homEquiv_comp, homEquiv_positiveAbelMorphism]
  exact (NatTrans.naturality_apply (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom)
    a.hom.op (classOf _ (positiveFamilyLineBundle X.hom n))).symm

/-- The actual schematic image of the positive Abel morphism. The object
has no base-point parameter. -/
def positiveAbelImage (n : ℕ) : Scheme.{u} :=
  (positiveAbelMorphism X P R n).hom.left.image

variable [IsSeparated P.obj.hom]

/-- The positive Abel morphism is proper by properness of its original
parameter scheme and separatedness of the target. -/
theorem isProper_positiveAbelMorphism (n : ℕ) :
    IsProper (positiveAbelMorphism X P R n).hom.left := by
  have : IsProper ((positiveAbelMorphism X P R n).hom.left ≫ P.obj.hom) := by
    rw [Over.w]
    exact parameter_isProper X.hom n
  exact IsProper.of_comp _ P.obj.hom

/-- The positive image is an actual integral closed subscheme, for the
original curve, without a rational point on it. -/
theorem isIntegral_positiveAbelImage (hX : Properties X) (n : ℕ) :
    IsIntegral (positiveAbelImage X P R n) := by
  have := isIntegral_parameter hX n
  have : IsIntegral (locallyNoetherianParameter X n).obj.left :=
    inferInstanceAs (IsIntegral (parameter X.hom n).left)
  have := isProper_positiveAbelMorphism X P R n
  exact schemeImage_isIntegral (positiveAbelMorphism X P R n).hom.left

/-- Its dimension is bounded by the degree of the original ordered divisor
parameter, without choosing a normalization point. -/
theorem topologicalKrullDim_positiveAbelImage_le (hX : Properties X) (n : ℕ) :
    topologicalKrullDim (positiveAbelImage X P R n) ≤ n := by
  have := isProper_positiveAbelMorphism X P R n
  exact ((positiveAbelMorphism X P R n).hom.left.topologicalKrullDim_image_le).trans
    (topologicalKrullDim_parameter hX n).le

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
