/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.DedekindDimension
public import Aglib.AlgebraicGeometry.Stalk.GenericFiber.Horizontal
public import Aglib.AlgebraicGeometry.Curves.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity

/-!
# The model stalk bound from its actual generic curve

Source: `R5Lab.AlgebraicGeometry.ArithmeticSurface.RelativeDimension`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `4231f79caefdd9eca03ed9375cbae3c5e98c14ad7a7a2fc384086615709af529`, selected lines [[35,
47]].
The actual scheme objects, canonical maps, universes and conditions are retained.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.LocalRing.GenericFiber (baseMap scheme stalkEquiv horizontalLift)
namespace AlgebraicGeometry.Scheme.DedekindBase
variable {A : Type u} [CommRing A] [IsDedekindDomain A]
  (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
  {X : Scheme.{u}} [IsIntegral X]

/-- An actual generic curve over a Dedekind base bounds all model-stalk dimensions by two.
The curve properties refer to the literal pullback along the supplied fraction-field map. -/
theorem stalk_dimension_le_two_of_generic_curve
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [IsDominant f]
    (hcurve : OverField.Curve.Properties (Over.mk (pullback.snd f (baseMap A K))))
    (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
  apply stalk_dimension_le_two_of_horizontal_stalk_le_one K f ?_ x
  intro y hy
  let z := horizontalLift A K f y hy
  let : SmoothOfRelativeDimension 1 (pullback.snd f (baseMap A K)) := hcurve.smooth
  have hd := smoothOfRelativeDimension_stalk_dimension_le K
    (scheme A K f) (pullback.snd f (baseMap A K)) 1 z
  have he := ringKrullDim_eq_of_ringEquiv (stalkEquiv A K f z)
  rw [← he, LocalRing.GenericFiber.horizontalLift_projection] at hd
  exact hd

end AlgebraicGeometry.Scheme.DedekindBase
