/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Smooth.Lifting

/-!
# Consumer checks for lifting points of a representing scheme of the relative Picard functor

The base change `X_A ⟶ X_{A'}` of a square-zero surjection is a closed immersion with square-zero
kernel; points of a scheme representing the relative Picard functor of a family with an affine map
to the projective line lift along Noetherian square-zero thickenings; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.RelativePicard

universe u

namespace AglibTest.PicardSmoothLifting

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  {A' A : Type u} [CommRing A'] [CommRing A] [Algebra k A'] [Algebra k A]

/-- The thickening `X_A ⟶ X_{A'}` of a square-zero surjection, with its square-zero kernel. -/
example (g : A' →ₐ[k] A) (hg : Function.Surjective g) (hK : RingHom.ker g ^ 2 = ⊥) :
    IsClosedImmersion (familySpecOverMap p g) ∧ (familySpecOverMap p g).ker ^ 2 = ⊥ :=
  ⟨familySpecOverMap_isClosedImmersion p g hg, familySpecOverMap_ker_sq p g hg hK⟩

/-- The thickening is the map of the base-change family `familyScheme p`. -/
example (g : A' →ₐ[k] A) : familySpecOverMap p g = (familyScheme p).map (specOverMap g) :=
  familySpecOverMap_eq p g

/-- Lifting for a scheme representing the relative Picard functor over a field. -/
example {K : Type u} [Field K] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K))
    {P : LocallyNoetherianOver (Spec (.of K))}
    (R : ((locallyNoetherianOverInclusion (Spec (.of K))).op ⋙ relativePicardFunctor q ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (ρ : Y ⟶ ProjectiveLine.projectiveP1 K) [IsAffineHom ρ] :
    P.obj.hom.LiftsAlongNoetherianSquareZero :=
  liftsAlongNoetherianSquareZero_of_relativeRepresentableBy_of_isAffineHom_projectiveP1 q R ρ

end AglibTest.PicardSmoothLifting

/--
info: 'AlgebraicGeometry.Scheme.isAffineHom_pullback_fst_specOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isAffineHom_pullback_fst_specOver

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.familySpecOverMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.familySpecOverMap

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.familySpecOverMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.familySpecOverMap_eq

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.familySpecOverMap_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.familySpecOverMap_isPullback

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.familySpecOverMap_isClosedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.familySpecOverMap_isClosedImmersion

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.familySpecOverMap_ker_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.familySpecOverMap_ker_sq

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.liftsAlongNoetherianSquareZero_of_relativeRepresentableBy_of_isAffineHom_projectiveP1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.RelativePicard.liftsAlongNoetherianSquareZero_of_relativeRepresentableBy_of_isAffineHom_projectiveP1
