/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.KrullDimension.FiniteTypeBaseChange
public import Aglib.AlgebraicGeometry.Dimension.OpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber

/-! # Uniform finite dimension of geometric fibres

A finite-type morphism to a quasi-compact scheme has one natural-number bound
on all field-valued fibres. The proof takes finite affine covers and bounds
field base changes by the numbers of actual polynomial generators. It assumes
neither a Noetherian nor a finite-dimensional base, and allows arbitrary fields,
empty fibres, and nonreduced fibres.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- An affine finite-type map has a uniform finite dimension bound after any
field-valued base change. -/
theorem Scheme.Hom.exists_geometricFiber_dimension_le_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ n : ℕ, ∀ (K : Type u) [Field K] (η : Spec (.of K) ⟶ S),
      topologicalKrullDim (pullback (C := Scheme) f η) ≤ n := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) :=
    HasRingHomProperty.appTop @LocallyOfFiniteType f inferInstance
  obtain ⟨n, hn⟩ := Algebra.FiniteType.exists_ringKrullDim_tensorProduct_le
    (R := Γ(S, ⊤)) (A := Γ(X, ⊤))
  refine ⟨n, fun K _ η => ?_⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (η ≫ S.isoSpec.hom)
  let : Algebra Γ(S, ⊤) K := φ.hom.toAlgebra
  let e₁ : pullback f η ≅ pullback (Spec.map f.appTop) (Spec.map φ) :=
    asIso (pullback.map _ _ _ _ X.isoSpec.hom (𝟙 _) S.isoSpec.hom
      (Scheme.isoSpec_hom_naturality f).symm (by simpa using hφ.symm))
  let e₂ : pullback (Spec.map f.appTop) (Spec.map φ) ≅
      Spec (.of (K ⊗[Γ(S, ⊤)] Γ(X, ⊤))) :=
    pullbackSymmetry _ _ ≪≫ pullbackSpecIso Γ(S, ⊤) K Γ(X, ⊤)
  calc
    topologicalKrullDim (pullback (C := Scheme) f η) =
        topologicalKrullDim (Spec (.of (K ⊗[Γ(S, ⊤)] Γ(X, ⊤)))) :=
      IsHomeomorph.topologicalKrullDim_eq _ (e₁ ≪≫ e₂).hom.homeomorph.isHomeomorph
    _ = ringKrullDim (K ⊗[Γ(S, ⊤)] Γ(X, ⊤)) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ ≤ n := hn K

private theorem dimension_le_of_openCover
    {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : X.OpenCover) (n : ℕ)
    (K : Type u) [Field K] (η : Spec (.of K) ⟶ S)
    (h : ∀ i : 𝒰.I₀,
      topologicalKrullDim (pullback (C := Scheme) (𝒰.f i ≫ f) η) ≤ n) :
    topologicalKrullDim (pullback (C := Scheme) f η) ≤ n := by
  apply Scheme.topologicalKrullDim_le_of_openCover (Scheme.Pullback.openCoverOfLeft 𝒰 f η)
  intro i
  exact h i

/-- A finite-type map to an affine scheme has uniformly bounded field-valued
fibres, without requiring the source to be affine. -/
theorem Scheme.Hom.exists_geometricFiber_dimension_le_of_isAffine_target
    {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ n : ℕ, ∀ (K : Type u) [Field K] (η : Spec (.of K) ⟶ S),
      topologicalKrullDim (pullback (C := Scheme) f η) ≤ n := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have h (i : 𝒰.I₀) :=
    (𝒰.f i ≫ f).exists_geometricFiber_dimension_le_of_isAffine
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun K _ η => ?_⟩
  apply dimension_le_of_openCover f 𝒰 (Finset.univ.sup n) K η
  intro i
  apply (hn i K η).trans
  exact_mod_cast (Finset.le_sup (f := n) (Finset.mem_univ i))

/-- A finite-type map to a quasi-compact scheme has a uniform finite bound on
all field-valued fibres. No quasi-separatedness, Noetherianity, or dimension
bound on the target is required. -/
theorem Scheme.Hom.exists_geometricFiber_dimension_le
    {X S : Scheme.{u}} [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ n : ℕ, ∀ (K : Type u) [Field K] (η : Spec (.of K) ⟶ S),
      topologicalKrullDim (pullback (C := Scheme) f η) ≤ n := by
  classical
  let 𝒰 := S.affineCover.finiteSubcover
  have h (i : 𝒰.I₀) :=
    (pullback.snd f (𝒰.f i)).exists_geometricFiber_dimension_le_of_isAffine_target
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun K _ η => ?_⟩
  obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (η (IsLocalRing.closedPoint K))
  have hη : Set.range η ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint K)]
    exact ⟨x, hx⟩
  let η' := IsOpenImmersion.lift (𝒰.f i) η hη
  let e : pullback (pullback.snd f (𝒰.f i)) η' ≅ pullback f η :=
    pullbackLeftPullbackSndIso f (𝒰.f i) η' ≪≫
      pullback.congrHom rfl (IsOpenImmersion.lift_fac _ _ hη)
  have he : topologicalKrullDim (pullback (C := Scheme) f η) =
      topologicalKrullDim (pullback (C := Scheme) (pullback.snd f (𝒰.f i)) η') :=
    IsHomeomorph.topologicalKrullDim_eq _ e.inv.homeomorph.isHomeomorph
  rw [he]
  apply (hn i K η').trans
  exact_mod_cast (Finset.le_sup (f := n) (Finset.mem_univ i))

/-- The same uniform bound applies after every further scheme base change,
including base changes to targets that are not quasi-compact. -/
theorem Scheme.Hom.exists_baseChange_geometricFiber_dimension_le
    {X S : Scheme.{u}} [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ n : ℕ, ∀ {T : Scheme.{u}} (g : T ⟶ S)
      (K : Type u) [Field K] (η : Spec (.of K) ⟶ T),
      topologicalKrullDim (pullback (C := Scheme) (pullback.snd f g) η) ≤ n := by
  obtain ⟨n, hn⟩ := f.exists_geometricFiber_dimension_le
  refine ⟨n, fun {T} g K _ η => ?_⟩
  have he := IsHomeomorph.topologicalKrullDim_eq _
    (pullbackLeftPullbackSndIso f g η).hom.homeomorph.isHomeomorph
  exact he.le.trans (hn K (η ≫ g))

/-- The ordinary scheme-theoretic fibres of a finite-type map to a quasi-compact
base have a uniform natural-number dimension bound. -/
theorem Scheme.Hom.exists_fiber_dimension_le
    {X S : Scheme.{u}} [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ n : ℕ, ∀ s : S, topologicalKrullDim (f.fiber s) ≤ n := by
  obtain ⟨n, hn⟩ := f.exists_geometricFiber_dimension_le
  exact ⟨n, fun s => hn (S.residueField s) (S.fromSpecResidueField s)⟩

end AlgebraicGeometry
