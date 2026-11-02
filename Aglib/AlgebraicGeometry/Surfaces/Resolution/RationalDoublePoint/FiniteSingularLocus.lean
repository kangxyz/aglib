/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.RegularLocus
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Properties.Regular.Affine
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finite singular sets on actual finite-type normal surface models

J-2 is applied to the actual structural algebra on every affine chart.
The original affine stalk isomorphisms identify its singular points with
those on the original model. A finite affine cover then gives a finite
singular set, without a supplied resolving model or chart classification.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The singular points in an actual affine open of a normal finite-type
surface over a J-2 base form a finite subset of the original model. -/
theorem finite_singularSet_inter_affine_of_isJ2Ring
    (A : Type u) [CommRing A] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hA : IsJ2Ring.{u, 0} A) (hX : NormalStalks X)
    (hdim : topologicalKrullDim X ≤ 2) (U : X.Opens) (hU : IsAffineOpen U) :
    {x : X | x ∈ U ∧ ¬ IsRegularLocalRing (X.presheaf.stalk x)}.Finite := by
  classical
  by_cases hne : Nonempty U
  · let : Nonempty U := hne
    let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
    let : IsIntegrallyClosed Γ(X, U) := isIntegrallyClosed_sections_of_isAffineOpen X U hU
    let φ : A →+* Γ(X, U) :=
      (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
    let : Algebra A Γ(X, U) := φ.toAlgebra
    let : Algebra.FiniteType A Γ(X, U) :=
      (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
        (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (.of A)).inv.hom
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2)
    have hd : ringKrullDim Γ(X, U) ≤ 2 := by
      have h := hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
      change topologicalKrullDim (PrimeSpectrum Γ(X, U)) ≤ topologicalKrullDim X at h
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
      exact h.trans hdim
    have hfin := PrimeSpectrum.finite_compl_regularLocus_of_finiteType_of_isJ2Ring
      A Γ(X, U) hA hd
    exact finite_singularSet_inter_affine_of_finite_compl_regularLocus U hU hfin
  · apply Set.finite_empty.subset
    rintro x ⟨hxU, _⟩
    exact (hne ⟨⟨x, hxU⟩⟩).elim

/-- A Noetherian integral normal surface of finite type over a J-2 base has
finitely many singular points on its original underlying scheme. -/
theorem finite_singularSet_of_finiteType_of_isJ2Ring
    (A : Type u) [CommRing A] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hA : IsJ2Ring.{u, 0} A) (hX : NormalStalks X)
    (hdim : topologicalKrullDim X ≤ 2) :
    {x : X | ¬ IsRegularLocalRing (X.presheaf.stalk x)}.Finite := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  have haff (i : 𝒰.I₀) : IsAffine (𝒰.X i) := by
    change IsAffine (X.affineCover.X (X.affineCover.idx i.val))
    exact Scheme.isAffine_affineCover X _
  let V (i : 𝒰.I₀) : X.Opens := (𝒰.f i).opensRange
  have hV (i : 𝒰.I₀) : IsAffineOpen (V i) := by
    let : IsAffine (𝒰.X i) := haff i
    exact isAffineOpen_opensRange (𝒰.f i)
  have hf (i : 𝒰.I₀) :
      {x : X | x ∈ V i ∧ ¬ IsRegularLocalRing (X.presheaf.stalk x)}.Finite :=
    finite_singularSet_inter_affine_of_isJ2Ring A f hA hX hdim (V i) (hV i)
  apply (Set.finite_iUnion hf).subset
  intro x hx
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_, hx⟩
  change x ∈ Set.range (𝒰.f i)
  exact ⟨y, hy⟩

/-- Completeness and dimension at most two of the actual local base derive
J-2; normality and dimension at most two of the actual model then give its
finite singular set. No resolution, marking or finite-chart algebra is input. -/
theorem finite_singularSet_of_finiteType_complete_local
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hdA : ringKrullDim A ≤ 2) (hX : NormalStalks X)
    (hdX : topologicalKrullDim X ≤ 2) :
    {x : X | ¬ IsRegularLocalRing (X.presheaf.stalk x)}.Finite := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hdA
  have hN : IsNagataRing.{u, 0} A := IsNagataRing.of_complete_local_dimLE_two A
  have hJ : IsJ2Ring.{u, 0} A :=
    IsNagataRing.isJ2Ring_of_semilocal_dimLE_two A hN hdA
  exact finite_singularSet_of_finiteType_of_isJ2Ring A f hJ hX hdX

end AlgebraicGeometry.Scheme
