/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelGeometry
public import Aglib.AlgebraicGeometry.Limits.FiniteProducts.Smooth
public import Aglib.AlgebraicGeometry.Dimension.ProperImage
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Integral
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality

/-!
# Actual based Abel images in the original Jacobian

The existing ordered graph family maps into the identity component of the
same supplied Picard representative. Its actual scheme-theoretic image is
integral, and properness bounds its dimension by the number of points.

These images depend on the specified rational base point. Their comparison
with the intrinsic divisor-Hilbert Abel image in the degree stratum remains
a separate construction. In particular the upper dimension bound alone is
not a proof of theta Cartierness or Abel birationality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Scheme Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)

include hX

/-- Its actual relative dimension is the number of points, including zero. -/
theorem smoothOfRelativeDimension_parameter (n : ℕ) :
    SmoothOfRelativeDimension n (parameter X.hom n).hom := by
  simpa [parameter] using @smoothOfRelativeDimension_finiteProductOver (Spec (.of k)) n
    (fun _ : Fin n => Over.mk X.hom) (fun _ => 1) (fun _ => hX.smooth)

/-- The same parameter scheme is integral, using connectedness and its
actual smooth normal local rings. -/
theorem isIntegral_parameter (n : ℕ) : IsIntegral (parameter X.hom n).left := by
  have := connectedSpace_parameter hX n
  have := smoothOfRelativeDimension_parameter hX n
  have : Smooth (parameter X.hom n).hom := SmoothOfRelativeDimension.smooth n _
  have : IsLocallyNoetherian (parameter X.hom n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (parameter X.hom n).hom
  exact isIntegral_of_connected_normalStalks_actual (parameter X.hom n).left
    (smoothFieldNormality k (parameter X.hom n).left (parameter X.hom n).hom inferInstance)

/-- The ordered divisor parameter scheme has dimension equal to its degree. -/
theorem topologicalKrullDim_parameter (n : ℕ) :
    topologicalKrullDim (parameter X.hom n).left = n := by
  have := connectedSpace_parameter hX n
  exact smoothFieldDimension k (parameter X.hom n).left (parameter X.hom n).hom n
    (smoothOfRelativeDimension_parameter hX n) inferInstance

variable (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom]

/-- The actual closed subscheme parametrized by the based degree-n Abel map.
No smoothness, dimension or Cartier conclusion is built into this definition. -/
def basedAbelImage (n : ℕ) : Scheme.{u} :=
  (jacobianAbelMorphism hX o ho P R n).left.image

variable [IsSeparated P.obj.hom]

-- The identity-component structure map is the native open-immersion composite.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original map into the Jacobian is proper because its source is proper. -/
theorem isProper_jacobianAbelMorphism (n : ℕ) :
    IsProper (jacobianAbelMorphism hX o ho P R n).left := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  have : IsSeparated (identityComponentOver P.obj).hom := by
    rw [identityComponentOver_hom]
    infer_instance
  have : IsProper ((jacobianAbelMorphism hX o ho P R n).left ≫
      (identityComponentOver P.obj).hom) := by
    rw [Over.w]
    exact parameter_isProper X.hom n
  exact IsProper.of_comp _ (identityComponentOver P.obj).hom

/-- The actual schematic image is integral, without discarding nilpotents
from a separately chosen image model. -/
theorem isIntegral_basedAbelImage (n : ℕ) :
    IsIntegral (basedAbelImage hX o ho P R n) := by
  have := isIntegral_parameter hX n
  have := isProper_jacobianAbelMorphism hX o ho P R n
  exact schemeImage_isIntegral (jacobianAbelMorphism hX o ho P R n).left

/-- The based Abel image has dimension at most the degree of its actual
ordered divisor parameter scheme. -/
theorem topologicalKrullDim_basedAbelImage_le (n : ℕ) :
    topologicalKrullDim (basedAbelImage hX o ho P R n) ≤ n := by
  have := isProper_jacobianAbelMorphism hX o ho P R n
  exact ((jacobianAbelMorphism hX o ho P R n).left.topologicalKrullDim_image_le).trans
    (topologicalKrullDim_parameter hX n).le

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
