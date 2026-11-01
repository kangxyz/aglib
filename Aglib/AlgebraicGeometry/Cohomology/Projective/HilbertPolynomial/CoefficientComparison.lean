/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.SupportBound
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.ZeroModule
public import Aglib.AlgebraicGeometry.Modules.Coherent.Extension.CommonComparison
public import Mathlib.Data.ENat.SuccOrder

/-!
# Hilbert coefficients agree across a smaller support boundary

An actual open-restriction isomorphism of coherent modules identifies
coefficient `d` of their original Hilbert polynomials when their joint
support outside that open has dimension less than `d`. The proof chooses
the existing coherent comparison span internally. For each original map,
its native image factorization and two short exact sequences reduce the
comparison to kernels and cokernels on the smaller boundary. Their
coefficients vanish by the proved support-degree upper bound.

No comparison span, resolution, polynomial-degree equality or numerical
rank law is a premise of the final isomorphism theorem. The zero-degree
case retains the actual empty-boundary conclusion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

attribute [local instance] Abelian.hasFiniteBiproducts

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem support_subset_of_mono {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Mono f] : support M ⊆ support N := by
  intro x hx
  by_contra hN
  have hz : (moduleStalk X x).kernel N :=
    (Scheme.Modules.Coherent.Support.moduleStalk_isZero_iff X N x).mpr (not_not.mp hN)
  exact hx ((Scheme.Modules.Coherent.Support.moduleStalk_isZero_iff X M x).mp
    (((moduleStalk X x).kernel).prop_of_mono f hz))

private theorem support_subset_of_epi {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Epi f] : support N ⊆ support M := by
  intro x hx
  by_contra hM
  have hz : (moduleStalk X x).kernel M :=
    (Scheme.Modules.Coherent.Support.moduleStalk_isZero_iff X M x).mpr (not_not.mp hM)
  exact hx ((Scheme.Modules.Coherent.Support.moduleStalk_isZero_iff X N x).mp
    (((moduleStalk X x).kernel).prop_of_epi f hz))

private theorem support_biprod_subset_union {X : Scheme.{u}} (M N : X.Modules) :
    support (M ⊞ N) ⊆ support M ∪ support N := by
  intro x hx
  by_contra hMN
  have hM : (moduleStalk X x).kernel M :=
    (Scheme.Modules.Coherent.Support.moduleStalk_isZero_iff X M x).mpr
      (not_not.mp (not_or.mp hMN).1)
  have hN : (moduleStalk X x).kernel N :=
    (Scheme.Modules.Coherent.Support.moduleStalk_isZero_iff X N x).mpr
      (not_not.mp (not_or.mp hMN).2)
  exact hx ((Scheme.Modules.Coherent.Support.moduleStalk_isZero_iff X (M ⊞ N) x).mp
    (((moduleStalk X x).kernel).prop_biprod hM hN))

variable (k : Type u) [Field k] [Infinite k] (ι : Type u)

/-- A coherent coefficient supported in dimension strictly below `d`
has zero degree-`d` Hilbert coefficient, including `d = 0`. -/
theorem coeff_projectiveHilbertPolynomial_eq_zero_of_supportDimension_lt
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace k ι).Modules)
    (hF : affineLocallyFiniteType _ F) (d : ℕ)
    (hd : topologicalKrullDim (support F) < (d : ℕ)) :
    (projectiveHilbertPolynomial k ι F).coeff d = 0 := by
  cases d with
  | zero =>
    have hs : support F = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      let y : support F := ⟨x, hx⟩
      let Z : IrreducibleCloseds (support F) :=
        ⟨closure ({y} : Set (support F)), isIrreducible_singleton.closure, isClosed_closure⟩
      let : Nonempty (IrreducibleCloseds (support F)) := ⟨Z⟩
      have hnonneg : 0 ≤ topologicalKrullDim (support F) := Order.krullDim_nonneg
      exact (not_lt_of_ge hnonneg) hd
    have hz := (support_eq_empty_iff F).mp hs
    rw [projectiveHilbertPolynomial_eq_zero_of_isZero k ι hz, Polynomial.coeff_zero]
  | succ d =>
    have hle : topologicalKrullDim (support F) ≤ (d : ℕ) := ENat.WithBot.lt_add_one_iff.mp hd
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((natDegree_projectiveHilbertPolynomial_le_of_supportDimension_le k ι n e d F hF hle).trans_lt
        (Nat.lt_succ_self d))

/-- A map invertible on the actual open preserves coefficient `d` when
the joint support of its source and target outside that open has
dimension less than `d`. The native kernel/image/cokernel are used. -/
theorem coeff_projectiveHilbertPolynomial_eq_of_restrict_isIso
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M N : (ProjectiveSpace k ι).Modules) (hM : affineLocallyFiniteType _ M)
    (hN : affineLocallyFiniteType _ N) (f : M ⟶ N) (U : (ProjectiveSpace k ι).Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] (d : ℕ)
    (hd : topologicalKrullDim
      (((support M ∪ support N) ∩ (U : Set (ProjectiveSpace k ι))ᶜ) : Set (ProjectiveSpace k ι)) <
      (d : ℕ)) :
    (projectiveHilbertPolynomial k ι M).coeff d = (projectiveHilbertPolynomial k ι N).coeff d := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  let I := Abelian.image f
  let p := Abelian.factorThruImage f
  let i := Abelian.image.ι f
  have hpi : p ≫ i = f := Abelian.image.fac f
  have hI : affineLocallyFiniteType (ProjectiveSpace k ι) I :=
    (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_kernel (cokernel.π f) hN
      ((affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel f hM hN)
  have hK := (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_kernel p hM hI
  have hC := (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel i hI hN
  let R := Scheme.Modules.restrictFunctor U.ι
  have hRpi : R.map p ≫ R.map i = R.map f := by rw [← CategoryTheory.Functor.map_comp, hpi]
  let : IsIso (R.map p ≫ R.map i) := by rw [hRpi]; infer_instance
  let : Mono (R.map p) := mono_of_mono (R.map p) (R.map i)
  let : Epi (R.map i) := epi_of_epi (R.map p) (R.map i)
  let : IsIso (R.map p) := isIso_of_mono_of_epi _
  let : IsIso (R.map i) := isIso_of_mono_of_epi _
  let B : Set (ProjectiveSpace k ι) := (support M ∪ support N) ∩ (U : Set _)ᶜ
  have hKB : support (kernel p) ⊆ B := by
    intro x hx
    refine ⟨Or.inl (support_subset_of_mono (kernel.ι p) hx), ?_⟩
    intro hxU
    exact support_kernel_subset_compl_of_restrict_isIso U.ι p hx ⟨⟨x, hxU⟩, rfl⟩
  have hCB : support (cokernel i) ⊆ B := by
    intro x hx
    refine ⟨Or.inr (support_subset_of_epi (cokernel.π i) hx), ?_⟩
    intro hxU
    exact support_cokernel_subset_compl_of_restrict_isIso U.ι i hx ⟨⟨x, hxU⟩, rfl⟩
  have hKzero : (projectiveHilbertPolynomial k ι (kernel p)).coeff d = 0 :=
    coeff_projectiveHilbertPolynomial_eq_zero_of_supportDimension_lt k ι n e _ hK d
      ((Topology.IsEmbedding.inclusion hKB).isInducing.topologicalKrullDim_le.trans_lt hd)
  have hCzero : (projectiveHilbertPolynomial k ι (cokernel i)).coeff d = 0 :=
    coeff_projectiveHilbertPolynomial_eq_zero_of_supportDimension_lt k ι n e _ hC d
      ((Topology.IsEmbedding.inclusion hCB).isInducing.topologicalKrullDim_le.trans_lt hd)
  have hS₁ : (ShortComplex.kernelSequence p).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact p, epi_g := inferInstanceAs (Epi p) }
  have hS₂ : (ShortComplex.cokernelSequence i).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact i, mono_f := inferInstanceAs (Mono i) }
  have h₁ := projectiveHilbertPolynomial_add_of_shortExact k ι n e _ hS₁ hK hM hI
  have h₂ := projectiveHilbertPolynomial_add_of_shortExact k ι n e _ hS₂ hI hN hC
  change projectiveHilbertPolynomial k ι M =
    projectiveHilbertPolynomial k ι (kernel p) + projectiveHilbertPolynomial k ι I at h₁
  change projectiveHilbertPolynomial k ι N =
    projectiveHilbertPolynomial k ι I + projectiveHilbertPolynomial k ι (cokernel i) at h₂
  have hc₁ := congrArg (fun P : ℚ[X] => P.coeff d) h₁
  have hc₂ := congrArg (fun P : ℚ[X] => P.coeff d) h₂
  simp only [Polynomial.coeff_add, hKzero, zero_add] at hc₁
  simp only [Polynomial.coeff_add, hCzero, add_zero] at hc₂
  exact hc₁.trans hc₂.symm

/-- Isomorphic restrictions identify degree-`d` Hilbert coefficients
across an actual smaller support boundary. The coherent comparison span
is chosen and its support controlled inside the proof. -/
theorem coeff_projectiveHilbertPolynomial_eq_of_restrictIso
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M N : (ProjectiveSpace k ι).Modules) (hM : affineLocallyFiniteType _ M)
    (hN : affineLocallyFiniteType _ N) (U : (ProjectiveSpace k ι).Opens)
    (eU : M.restrict U.ι ≅ N.restrict U.ι) (d : ℕ)
    (hd : topologicalKrullDim
      (((support M ∪ support N) ∩ (U : Set (ProjectiveSpace k ι))ᶜ) : Set (ProjectiveSpace k ι)) <
      (d : ℕ)) :
    (projectiveHilbertPolynomial k ι M).coeff d = (projectiveHilbertPolynomial k ι N).coeff d := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  obtain ⟨H, a, b, hH, hab, ha, hb⟩ :=
    Scheme.Modules.Coherent.exists_coherent_common_comparison U.ι M N hM hN eU
  let : Mono (biprod.lift a b) := hab
  let : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) := ha
  let : IsIso ((Scheme.Modules.restrictFunctor U.ι).map b) := hb
  have hHsub : support H ⊆ support M ∪ support N :=
    (support_subset_of_mono (biprod.lift a b)).trans (support_biprod_subset_union M N)
  have hBa : (support H ∪ support M) ∩ (U : Set (ProjectiveSpace k ι))ᶜ ⊆
      (support M ∪ support N) ∩ (U : Set (ProjectiveSpace k ι))ᶜ := by
    rintro x ⟨hx, hxU⟩
    refine ⟨?_, hxU⟩
    rcases hx with hx | hx
    · exact hHsub hx
    · exact Or.inl hx
  have hBb : (support H ∪ support N) ∩ (U : Set (ProjectiveSpace k ι))ᶜ ⊆
      (support M ∪ support N) ∩ (U : Set (ProjectiveSpace k ι))ᶜ := by
    rintro x ⟨hx, hxU⟩
    refine ⟨?_, hxU⟩
    rcases hx with hx | hx
    · exact hHsub hx
    · exact Or.inr hx
  have hA := coeff_projectiveHilbertPolynomial_eq_of_restrict_isIso k ι n e H M hH hM a U d
    ((Topology.IsEmbedding.inclusion hBa).isInducing.topologicalKrullDim_le.trans_lt hd)
  have hB := coeff_projectiveHilbertPolynomial_eq_of_restrict_isIso k ι n e H N hH hN b U d
    ((Topology.IsEmbedding.inclusion hBb).isInducing.topologicalKrullDim_le.trans_lt hd)
  exact hA.symm.trans hB

end AlgebraicGeometry.Scheme.Cohomology
