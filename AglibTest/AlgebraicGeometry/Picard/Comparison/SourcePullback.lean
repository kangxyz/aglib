/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.SourcePullback

/-! # Actual source/parameter coherence, with its O-connectedness premise discharged -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory AlgebraicGeometry
open Scheme Scheme.RelativePicard

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : Over S}
    [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
    (oX : 𝟙_ (Over S) ⟶ X) (oY : 𝟙_ (Over S) ⟶ Y)
    (f : X ⟶ Y) (hf : oX ≫ f = oY)
    {T₀ T₁ T₂ : Over S} (a : T₀ ⟶ T₁) (b : T₁ ⟶ T₂)
    (Q : RigidifiedPair Y.hom oY.left (Over.w oY) T₂) :
    (RigidifiedPair.mapCompIso a b (RigidifiedPair.sourcePullback oX oY f hf Q)).trans
        ((RigidifiedPair.Iso.map a
          (RigidifiedPair.sourcePullbackParameterIso oX oY f hf b Q)).trans
          (RigidifiedPair.sourcePullbackParameterIso oX oY f hf a (RigidifiedPair.map b Q))) =
      (RigidifiedPair.sourcePullbackParameterIso oX oY f hf (a ≫ b) Q).trans
        (RigidifiedPair.Iso.sourcePullback oX oY f hf (RigidifiedPair.mapCompIso a b Q)) := by
  have := isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral X.hom T₀.hom
  exact RigidifiedPair.sourcePullbackParameterIso_comp oX oY f hf a b Q

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.rigidifiedPicardPullback_comp_fppfIso'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.rigidifiedPicardPullback_comp_fppfIso
