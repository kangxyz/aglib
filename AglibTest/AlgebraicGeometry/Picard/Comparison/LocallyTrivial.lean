/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Comparison.LocallyTrivial

/-! Focused consumer of Kleiman's Thm 2.5(1) (*The Picard scheme*, arXiv:math/0504020v1, p. 18;
Stacks 0B9M): for `S` locally Noetherian and `p` proper, flat, with geometrically integral
fibres, fppf-locally trivial classes are base classes, and the committed comparison map
`toFppfPicardSheaf p` is injective and a monomorphism. -/

@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.RelativePicard

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S)

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    FppfLocallyTrivialMemBaseImage p :=
  fppfLocallyTrivialMemBaseImage_of_isProper_of_flat_of_geometricallyIntegral p

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
    (T : (Over S)ᵒᵖ) : Function.Injective ((toFppfPicardSheaf p).app T).hom :=
  toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral p T

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    Mono (toFppfPicardSheaf p) :=
  mono_toFppfPicardSheaf_of_isProper_of_flat_of_geometricallyIntegral p

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.fppfLocallyTrivialMemBaseImage_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fppfLocallyTrivialMemBaseImage_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.mono_toFppfPicardSheaf_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mono_toFppfPicardSheaf_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.bijective_familyPullback_map_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms bijective_familyPullback_map_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.exists_familyPullback_iso_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_familyPullback_iso_of_isProper_of_flat_of_geometricallyIntegral
