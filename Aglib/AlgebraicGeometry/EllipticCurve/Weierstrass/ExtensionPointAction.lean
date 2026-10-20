/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ExtensionPoints
public import Aglib.AlgebraicGeometry.RationalPoint.FieldAutomorphism

/-!
# Coefficient-fixing field actions on the actual Weierstrass extension points

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.PeriodDescent`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 120–156.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
namespace WeierstrassCurve.Projective
universe u
variable {F K : Type u} [Field F] [Field K]
  (f : F →+* K) (σ : K ≃+* K) (hfix : σ.toRingHom.comp f = f)

include hfix in
/-- The actual affine evaluation ring maps intertwine field automorphisms. -/
theorem affinePointEvalExtension_automorphism (W : WeierstrassCurve F)
    (x y : K) (h : (W.map f).toAffine.Equation x y)
    (h' : (W.map f).toAffine.Equation (σ x) (σ y)) :
    σ.toRingHom.comp (affinePointEvalExtension W f x y h) =
      affinePointEvalExtension W f (σ x) (σ y) h' := by
  apply affinePointEvalExtension_ext W
  · intro a
    simp only [RingHom.comp_apply, affinePointEvalExtension_constant]
    exact automorphism_fixes_image f σ hfix a
  · simp only [RingHom.comp_apply, affinePointEvalExtension_x]
    rfl
  · simp only [RingHom.comp_apply, affinePointEvalExtension_y]
    rfl

/-- The literal affine scheme-point action, not just equality of coordinates. -/
theorem affinePointOverExtension_automorphism (W : WeierstrassCurve F)
    (x y : K) (h : (W.map f).toAffine.Equation x y)
    (h' : (W.map f).toAffine.Equation (σ x) (σ y)) :
    extensionPointAutomorphism f σ hfix ≫ affinePointOverExtension W f x y h =
      affinePointOverExtension W f (σ x) (σ y) h' := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun g : affineRing W →+* K => Spec.map (CommRingCat.ofHom g))
    (affinePointEvalExtension_automorphism f σ hfix W x y h h')

/-- The pole branch is the original infinity section, also fixed over F. -/
theorem originOverExtension_automorphism (W : WeierstrassCurve F) :
    extensionPointAutomorphism f σ hfix ≫ originOverExtension W f =
      originOverExtension W f := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ (Spec.map _ ≫ infinitySection W) = Spec.map _ ≫ infinitySection W
  rw [← Category.assoc, ← Spec.map_comp]
  have h := congrArg (fun g : F →+* K => Spec.map (CommRingCat.ofHom g)) hfix
  exact congrArg (fun g => g ≫ infinitySection W) h


end WeierstrassCurve.Projective
