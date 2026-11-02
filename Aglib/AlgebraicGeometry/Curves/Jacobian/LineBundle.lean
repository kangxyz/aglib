/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Smooth
public import Aglib.AlgebraicGeometry.Curves.Jacobian.ProjectivityField
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Square
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Symmetric
/-!
# Cube and multiplication pullback on the original Jacobian

These are thin instances of the general projective group constructions for
the same supplied Picard representative `P,R` and its actual identity
component. Projectivity and geometric integrality are supplied over the
original ground field by the native projectivity and smoothness theorems.
The equations use the original maps and actual line bundles. No new
representability, cubical-comparison or genus assumption is introduced.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.Modules.Invertible
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

include hX

/-- The cube on the actual Jacobian, on every test scheme. -/
theorem cubeClass_identityComponentOver :
    letI := picardCommGrpObj X.hom P R
    ∀ {T : Over (Spec (.of k))} (f g h : T ⟶ identityComponentOver P.obj)
      (a : PicardGroup (identityComponentOver P.obj).left),
      LineBundleCube.cubeClass f g h a = 0 := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  intro T f g h a
  exact LineBundleCube.cubeClass_eq_zero (identityComponentOver P.obj) f g h a

/-- The square identity on the original Jacobian translations. -/
theorem pullbackClass_translation_mul_identityComponentOver :
    letI := picardCommGrpObj X.hom P R
    ∀ (x y : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj)
      (a : PicardGroup (identityComponentOver P.obj).left),
      pullbackClass (GrpObj.mulRight (x * y)).hom.left a + a =
        pullbackClass (GrpObj.mulRight x).hom.left a +
          pullbackClass (GrpObj.mulRight y).hom.left a := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  intro x y a
  exact LineBundleCube.pullbackClass_translation_mul (identityComponentOver P.obj) x y a

/-- Multiplication pullback on the same actual Jacobian, including zero and
one and with no invertibility condition on the level. -/
theorem pullbackClass_multiplication_identityComponentOver :
    letI := picardCommGrpObj X.hom P R
    ∀ (a : PicardGroup (identityComponentOver P.obj).left) (n : ℕ),
      pullbackClass ((𝟙 (identityComponentOver P.obj)) ^ n).left a =
        (n * (n + 1) / 2) • a + (n * (n - 1) / 2) •
          pullbackClass ((𝟙 (identityComponentOver P.obj))⁻¹).left a := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  intro a n
  exact LineBundleCube.pullbackClass_multiplication (identityComponentOver P.obj) a n

/-- The square-exponent law for symmetric classes on the original Jacobian. -/
theorem pullbackClass_multiplication_identityComponentOver_of_symmetric :
    letI := picardCommGrpObj X.hom P R
    ∀ (a : PicardGroup (identityComponentOver P.obj).left),
      pullbackClass ((𝟙 (identityComponentOver P.obj))⁻¹).left a = a →
        ∀ n : ℕ, pullbackClass ((𝟙 (identityComponentOver P.obj)) ^ n).left a = n ^ 2 • a := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  intro a ha n
  exact LineBundleCube.pullbackClass_multiplication_of_symmetric
    (identityComponentOver P.obj) a ha n

/-- The symmetric law as an isomorphism of the actual Jacobian line bundles. -/
theorem nonempty_multiplicationPullbackIso_identityComponentOver_of_symmetric :
    letI := picardCommGrpObj X.hom P R
    ∀ (L : LineBundle (identityComponentOver P.obj).left),
      pullbackClass ((𝟙 (identityComponentOver P.obj))⁻¹).left (classOf _ L) = classOf _ L →
        ∀ n : ℕ,
          Nonempty ((pullbackLineBundle ((𝟙 (identityComponentOver P.obj)) ^ n).left L).val ≅
            (tensorPowerLineBundle (identityComponentOver P.obj).left L (n ^ 2)).val) := by
  let := picardCommGrpObj X.hom P R
  let := isHProjective_identityComponentOver hX P R
  let := geometricallyIntegral_identityComponentOver hX P R
  intro L hL n
  exact LineBundleCube.nonempty_multiplicationPullbackIso_of_symmetric
    (identityComponentOver P.obj) L hL n

end AlgebraicGeometry.Scheme.OverField.Curve
