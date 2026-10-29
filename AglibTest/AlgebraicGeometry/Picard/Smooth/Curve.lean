/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Smooth.Curve

/-!
# Consumer checks for the smoothness of the Picard scheme of a curve

For a closed subscheme `X` of `P^N_k`, flat with geometrically integral fibres, integral of
dimension one, and its Picard scheme `picardScheme h` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Prop. 5.19, p. 47): smoothness of `picardScheme h` and of `Pic⁰_{X/k}`,
with and without a rational point, also at the target-5 proof
`Strata.fineStrataRepresentableByHQuasiProjective i e`; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.RelativePicard.Strata

universe u

namespace AglibTest.PicardSmoothCurve

variable {k : Type u} [Field k] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace k ι} [IsClosedImmersion i] [Flat (i ≫ toSpec k ι)]
  [GeometricallyIntegral (i ≫ toSpec k ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- With a section, points lift and the Picard scheme is smooth. -/
example (o : Spec (.of k) ⟶ X) (ho : o ≫ i ≫ toSpec k ι = 𝟙 _) [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) :
    (picardScheme h).obj.hom.LiftsAlongNoetherianSquareZero ∧ Smooth (picardScheme h).obj.hom :=
  ⟨liftsAlongNoetherianSquareZero_picardScheme_of_curve_of_section h o ho hdim,
    (smooth_picardScheme_of_curve_of_section h o ho hdim).1⟩

/-- Without a rational point, the Picard scheme and its identity component are smooth. -/
example [IsIntegral X] (hdim : topologicalKrullDim X = 1) :
    Smooth (picardScheme h).obj.hom ∧
      Smooth (picardIdentityComponent (i ≫ toSpec k ι) (picardScheme h)
        (picardSchemeRepresentableBy h)).hom :=
  smooth_picardScheme_of_curve h hdim

/-- At the target-5 proof of the fine-strata premise. -/
example (e : ι ≃ Fin (N + 1)) [IsIntegral X] (hdim : topologicalKrullDim X = 1) :
    Smooth (picardScheme (fineStrataRepresentableByHQuasiProjective i e)).obj.hom :=
  (smooth_picardScheme_of_curve _ hdim).1

/-- The smooth locus of the Picard scheme is everything. -/
example [IsIntegral X] (hdim : topologicalKrullDim X = 1) :
    (picardScheme h).obj.hom.smoothLocus = ⊤ :=
  have := (smooth_picardScheme_of_curve h hdim).1
  Scheme.Hom.smoothLocus_eq_top _

end AglibTest.PicardSmoothCurve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Projectivity.exists_isAffineHom_to_projectiveP1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.OverField.Curve.Projectivity.exists_isAffineHom_to_projectiveP1

/--
info: 'AlgebraicGeometry.Scheme.isProper_pullback_snd_specOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isProper_pullback_snd_specOver

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.liftsAlongNoetherianSquareZero_picardScheme_of_curve_of_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.RelativePicard.liftsAlongNoetherianSquareZero_picardScheme_of_curve_of_section

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.smooth_picardIdentityComponent_of_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.smooth_picardIdentityComponent_of_smooth

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.smooth_picardScheme_of_curve_of_section' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.smooth_picardScheme_of_curve_of_section

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.smooth_picardScheme_of_curve' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.smooth_picardScheme_of_curve
