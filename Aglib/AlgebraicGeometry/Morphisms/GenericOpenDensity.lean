/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Spectrum.Prime.GenericPrincipalDensity
public import Aglib.AlgebraicGeometry.Properties.DenseAffine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Ring.Constructions

/-! # Density of original opens in field fibres

All fibre projections below are the original pullback projections. The affine
principal step uses the native tensor-product square, including its original
projection formula. Empty fibres are permitted.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

/-- A nonzero principal open of an integral finite-type affine scheme is dense
in every original field fibre over one nonzero principal open of the base. -/
theorem exists_ne_zero_dense_principal_fibre
    (R B : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.FiniteType R B]
    (b : B) (hb : b ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type u) [Field L] [Algebra R L],
      algebraMap R L r ≠ 0 →
      Dense ((pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R L)) ⁻¹'
        (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B))) := by
  obtain ⟨r, hr, h⟩ :=
    PrimeSpectrum.exists_ne_zero_forall_dense_basicOpen_one_tmul R B b hb
  refine ⟨r, hr, ?_⟩
  intro L _ _ hL
  let H := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R L B)).flip
  intro y
  obtain ⟨z, rfl⟩ := H.isoPullback.hom.homeomorph.surjective y
  have hz := mem_closure_image H.isoPullback.hom.continuous.continuousAt (h L hL z)
  apply closure_mono _ hz
  rintro _ ⟨z, hz, rfl⟩
  change pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R L)
    (H.isoPullback.hom z) ∈ PrimeSpectrum.basicOpen b
  rw [← Scheme.Hom.comp_apply, H.isoPullback_hom_fst]
  exact hz

/-- Density can be checked on the actual members of a scheme cover. -/
theorem dense_of_cover_preimage {X : Scheme.{u}} (C : X.OpenCover)
    (V : Set X) (h : ∀ i, Dense (C.f i ⁻¹' V)) : Dense V := by
  intro x
  obtain ⟨i, y, rfl⟩ := C.exists_eq x
  have hy := mem_closure_image (C.f i).continuous.continuousAt (h i y)
  exact closure_mono (Set.image_preimage_subset _ _) hy

/-- An original nonempty open in an integral finite-type scheme is dense in
all original field fibres over one nonzero principal open of the base.
Finite type is expressed by its native locally-finite-type and quasi-compact
conditions. No separation, flatness, properness, or nonempty-fibre condition
is added. -/
theorem exists_ne_zero_dense_open_fibres
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (V : X.Opens) (hV : (V : Set X).Nonempty) :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type u) [Field L] [Algebra R L],
      algebraMap R L r ≠ 0 →
      Dense ((pullback.fst f (Spec.algebraMap R L)) ⁻¹' (V : Set X)) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := inferInstance }
  obtain ⟨ι, hι, U, hU, hcover, _⟩ := exists_finite_dense_affine_cover (X := X)
  let := hι
  have hex (i : ι) : ∃ b : Γ(X, U i), b ≠ 0 ∧ X.basicOpen b ≤ V := by
    obtain ⟨x, hxV, hxU⟩ := (hU i).2.1.inter_open_nonempty (V : Set X) V.isOpen hV
    obtain ⟨b, hbV, hxb⟩ := (hU i).1.exists_basicOpen_le ⟨x, hxV⟩ hxU
    refine ⟨b, ?_, hbV⟩
    intro hb
    simp only [hb, Scheme.basicOpen_zero, TopologicalSpace.Opens.mem_bot] at hxb
  choose b hb hbV using hex
  let (i : ι) : Nonempty (U i) := (hU i).2.1.nonempty.to_subtype
  let γ (i : ι) : R →+* Γ(X, U i) := (Spec.preimage ((hU i).1.fromSpec ≫ f)).hom
  let (i : ι) : Algebra R Γ(X, U i) := (γ i).toAlgebra
  have hγ (i : ι) : Spec.algebraMap R Γ(X, U i) = (hU i).1.fromSpec ≫ f :=
    Spec.map_preimage _
  let (i : ι) : Algebra.FiniteType R Γ(X, U i) := by
    apply RingHom.finiteType_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  choose r hr hd using fun i => exists_ne_zero_dense_principal_fibre R Γ(X, U i) (b i) (hb i)
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.mpr (fun i _ => hr i), ?_⟩
  intro L _ _ hL
  have hri (i : ι) : algebraMap R L (r i) ≠ 0 := by
    intro hi
    apply hL
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  let C : X.OpenCover := {
    I₀ := ι
    X i := Spec Γ(X, U i)
    f i := (hU i).1.fromSpec
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨?_, inferInstance⟩
      intro x
      have hx : x ∈ (⨆ i, U i) := by rw [hcover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨i, (hU i).1.range_fromSpec.symm ▸ hi⟩ }
  apply dense_of_cover_preimage (Pullback.openCoverOfLeft C f (Spec.algebraMap R L))
  intro i
  have hdi : Dense ((pullback.fst (C.f i ≫ f) (Spec.algebraMap R L)) ⁻¹'
      (PrimeSpectrum.basicOpen (b i) : Set (PrimeSpectrum Γ(X, U i)))) := by
    change Dense ((pullback.fst ((hU i).1.fromSpec ≫ f) (Spec.algebraMap R L)) ⁻¹' _)
    rw [← hγ i]
    exact hd i L (hri i)
  apply hdi.mono
  intro z hz
  have hz' : (hU i).1.fromSpec (pullback.fst (C.f i ≫ f) (Spec.algebraMap R L) z)
      ∈ X.basicOpen (b i) := by
    change pullback.fst (C.f i ≫ f) (Spec.algebraMap R L) z ∈
      ((hU i).1.fromSpec ⁻¹ᵁ X.basicOpen (b i))
    rwa [(hU i).1.fromSpec_preimage_basicOpen]
  change (pullback.map (C.f i ≫ f) (Spec.algebraMap R L)
      f (Spec.algebraMap R L) (C.f i) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      pullback.fst f (Spec.algebraMap R L)) z ∈ V
  rw [pullback.lift_fst]
  change (hU i).1.fromSpec (pullback.fst (C.f i ≫ f) (Spec.algebraMap R L) z) ∈ V
  exact hbV i hz'

end AlgebraicGeometry.Scheme
