/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ResidueFiber
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Comparison
public import Aglib.AlgebraicGeometry.Dimension.OpenCover
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Dimension of the literal closed fibre

An integral algebra contracts strict chains of prime ideals strictly. Applying
this fact on the inverse images of affine opens bounds the dimension of a
finite cover of the projective line, including empty and nonreduced covers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

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

private theorem finite_dimension_le {X Z : Scheme.{u}} (f : X ⟶ Z) [IsFinite f] :
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

/-- Every finite cover of the projective line over a field has dimension at most one. -/
theorem finite_projectiveLine_topologicalKrullDim_le_one
    {K : Type u} [Field K] {Y : Scheme.{u}}
    (p : Y ⟶ ProjectiveLine.projectiveP1 K) [IsFinite p] :
    topologicalKrullDim Y ≤ 1 := by
  have hd : topologicalKrullDim (ProjectiveLine.projectiveP1 K) = 1 := by
    let e := ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1 K
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm.trans
      (Scheme.OverField.Curve.Projectivity.twoChartLine_topologicalKrullDim K)
  exact (finite_dimension_le p).trans hd.le

/-- The actual closed fibre has dimension at most one, without Noetherianity of the base. -/
theorem residueFiber_topologicalKrullDim_le_one
    {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}
    (p : Y ⟶ ProjectiveLine.projectiveP1 R) [IsFinite p] :
    topologicalKrullDim (residueFiber p) ≤ 1 :=
  finite_projectiveLine_topologicalKrullDim_le_one (residueFiberLineMap p)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
