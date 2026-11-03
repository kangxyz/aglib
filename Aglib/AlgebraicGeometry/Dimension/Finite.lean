/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.OpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Basic

/-! # Dimension does not increase under finite morphisms

An integral algebra contracts strict chains of prime ideals strictly. Applying
this fact over the affine cover of the target bounds the dimension of the
source of any finite morphism, including empty and nonreduced schemes.

The three proofs are extracted from the private dimension helpers in
`Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ResidueFiberDimension` at
`0ba24db0ca05a863d7d5630834316be36f03b7bf`. That curve leaf now consumes
the public scheme-morphism theorem instead of maintaining its own copy.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

private theorem integral_ring_dimension_le {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
  intro I J h
  exact Ideal.IsIntegral.under_lt_under h

private theorem affine_finite_dimension_le {X Z : Scheme.{u}}
    (f : X ⟶ Z) [IsAffine X] [IsAffine Z] [IsFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Z := by
  let := f.appTop.hom.toAlgebra
  let : Module.Finite Γ(Z, ⊤) Γ(X, ⊤) := f.finite_appTop
  calc
    topologicalKrullDim X = topologicalKrullDim (Spec Γ(X, ⊤)) :=
      IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph
    _ = ringKrullDim Γ(X, ⊤) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ ≤ ringKrullDim Γ(Z, ⊤) := integral_ring_dimension_le
    _ = topologicalKrullDim (Spec Γ(Z, ⊤)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
    _ = topologicalKrullDim Z :=
      (IsHomeomorph.topologicalKrullDim_eq _ Z.isoSpec.hom.homeomorph.isHomeomorph).symm

/-- A finite morphism does not increase topological Krull dimension.
Neither scheme is required to be Noetherian, reduced, nonempty, or of finite
dimension, and the morphism need not be surjective. -/
theorem Hom.topologicalKrullDim_le_of_isFinite
    {X Z : Scheme.{u}} (f : X ⟶ Z) [IsFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Z := by
  apply Scheme.topologicalKrullDim_le_of_openCover (Z.affineCover.pullback₁ f)
  intro i
  let : IsAffine (Z.affineCover.X i) := Scheme.isAffine_affineCover Z i
  let : IsOpenImmersion (Z.affineCover.f i) := Z.affineCover.map_prop i
  let : IsAffineHom (pullback.snd f (Z.affineCover.f i)) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  let : IsAffine (pullback f (Z.affineCover.f i)) :=
    isAffine_of_isAffineHom (pullback.snd f (Z.affineCover.f i))
  exact (affine_finite_dimension_le (pullback.snd f (Z.affineCover.f i))).trans
    (Z.affineCover.f i).isOpenEmbedding.isInducing.topologicalKrullDim_le

end AlgebraicGeometry.Scheme
