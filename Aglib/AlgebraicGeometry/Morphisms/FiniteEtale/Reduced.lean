/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FiniteReduced
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Properties

/-! # Finite etale ascent of reducedness

The finite-projective residue-field argument removes the locally Noetherian
base restriction for finite etale morphisms. Affine localization retains the
actual morphism and its original map on sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

universe u

/-- Finite etale ascent over an affine reduced base, without Noetherianity. -/
theorem finite_isReduced_of_isAffine {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f] [IsReduced Y] : IsReduced X := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let R := Γ(Y, ⊤)
  let A := Γ(X, ⊤)
  let : Algebra R A := f.appTop.hom.toAlgebra
  have : Module.Finite R A := f.finite_appTop
  have : Algebra.Etale R A :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  have : _root_.IsReduced A := Algebra.Etale.finite_isReduced R A
  exact isReduced_of_isAffine_isReduced X

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite etale morphism with arbitrary reduced target has reduced source.
Neither Noetherianity nor a finite-component assumption is required. -/
theorem finite_isReduced {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Etale f] [IsReduced Y] : IsReduced X := by
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := Y.affineCover.pullback₁ f)
  intro i
  have : IsReduced (Y.affineCover.X i) :=
    isReduced_of_isOpenImmersion (Y.affineCover.f i)
  exact finite_isReduced_of_isAffine (pullback.snd f (Y.affineCover.f i))

end AlgebraicGeometry.Etale
