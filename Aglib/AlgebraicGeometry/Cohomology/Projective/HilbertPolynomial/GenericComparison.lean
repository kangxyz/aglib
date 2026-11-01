/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.CoefficientComparison
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Generic comparison of the original projective Hilbert coefficients

On an integral scheme with a closed projective embedding, a coherent module
whose support misses the original generic point has zero top-dimensional
Hilbert coefficient after the original closed pushforward. A coherent
isomorphism on a generic-point neighbourhood therefore identifies that
coefficient. The proof uses the actual common coherent span on the source,
the native image factorizations and exact closed pushforward.

The support boundary and comparison span are discharged inside the proof.
No equality between Hilbert degree and support dimension is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem support_pushforward_subset_image {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (F : X.Modules) :
    support ((Scheme.Modules.pushforward i).obj F) ⊆ i '' support F := by
  intro y hy
  by_cases hyrange : y ∈ Set.range i
  · obtain ⟨x, rfl⟩ := hyrange
    refine ⟨x, ?_, rfl⟩
    intro hx
    have hz : IsZero ((moduleStalk X x).obj F) :=
      (Scheme.Modules.Coherent.Support.moduleStalk_isZero_iff X F x).mpr hx
    have hpush : IsZero ((moduleStalk Y (i x)).obj ((Scheme.Modules.pushforward i).obj F)) :=
      ((ModuleCat.restrictScalars (i.stalkMap x).hom).map_isZero hz).of_iso
        ((closedImmersionModuleStalkIso i x).app F)
    exact hy ((Scheme.Modules.Coherent.Support.moduleStalk_isZero_iff Y _ (i x)).mp hpush)
  · exact False.elim (hy
      ((Scheme.Modules.Coherent.Support.moduleStalk_isZero_iff Y _ y).mp
        (isZero_closedImmersion_moduleStalk_of_not_mem i y hyrange F)))

variable (k : Type u) [Field k] [Infinite k] (ι : Type u)

/-- A coherent source module missing the actual generic point has zero
degree-`d` coefficient after closed pushforward, whenever `dim X ≤ d`.
The zero-dimensional case is included. -/
theorem coeff_projectiveHilbertPolynomial_pushforward_eq_zero_of_generic_not_mem
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion i]
    (F : X.Modules) (hF : affineLocallyFiniteType X F) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : ℕ)) (hη : genericPoint X ∉ support F) :
    (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward i).obj F)).coeff d = 0 := by
  cases d with
  | zero =>
    have hs : support F = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxg := mem_genericPoints_of_topologicalKrullDim_nonpos hd x
      rw [genericPoints_eq_singleton] at hxg
      exact hη (hxg ▸ hx)
    have hz := (Scheme.Modules.pushforward i).map_isZero ((support_eq_empty_iff F).mp hs)
    rw [projectiveHilbertPolynomial_eq_zero_of_isZero k ι hz, Polynomial.coeff_zero]
  | succ d =>
    have hgeneric : Disjoint (support F) (genericPoints X) := by
      rw [genericPoints_eq_singleton, Set.disjoint_singleton_right]
      exact hη
    have hdim : topologicalKrullDim (support F) ≤ (d : ℕ) :=
      topologicalKrullDim_closed_le_of_avoids_genericPoints (support F)
        (isClosed_support_of_affineLocallyFiniteType hF) hgeneric d hd
    let hImage := i.isClosedEmbedding.isEmbedding.homeomorphImage (support F)
    have hdimImage : topologicalKrullDim (i '' support F) ≤ (d : ℕ) := by
      rw [← IsHomeomorph.topologicalKrullDim_eq hImage hImage.isHomeomorph]
      exact hdim
    have hsub := (Topology.IsEmbedding.inclusion
      (support_pushforward_subset_image i F)).isInducing.topologicalKrullDim_le
    have hdimPush : topologicalKrullDim
        (support ((Scheme.Modules.pushforward i).obj F)) ≤ (d : ℕ) := hsub.trans hdimImage
    exact coeff_projectiveHilbertPolynomial_eq_zero_of_supportDimension_lt k ι n e _
      (Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward i hF)
      (d + 1) (hdimPush.trans_lt (by exact_mod_cast Nat.lt_succ_self d))

/-- A coherent source map invertible near the actual generic point
preserves the top-dimensional coefficient after the original closed embedding. -/
theorem coeff_projectiveHilbertPolynomial_pushforward_eq_of_restrict_isIso
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (M N : X.Modules) (hM : affineLocallyFiniteType X M) (hN : affineLocallyFiniteType X N)
    (f : M ⟶ N) (U : X.Opens) (hη : genericPoint X ∈ U)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : ℕ)) :
    (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj M)).coeff d =
      (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj N)).coeff d := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  let I := Abelian.image f
  let p := Abelian.factorThruImage f
  let a := Abelian.image.ι f
  have hpa : p ≫ a = f := Abelian.image.fac f
  have hI : affineLocallyFiniteType X I :=
    (affineLocallyFiniteType X).prop_kernel (cokernel.π f) hN
      ((affineLocallyFiniteType X).prop_cokernel f hM hN)
  have hK := (affineLocallyFiniteType X).prop_kernel p hM hI
  have hC := (affineLocallyFiniteType X).prop_cokernel a hI hN
  let R := Scheme.Modules.restrictFunctor U.ι
  have hRpa : R.map p ≫ R.map a = R.map f := by
    rw [← CategoryTheory.Functor.map_comp, hpa]
  let : IsIso (R.map p ≫ R.map a) := by rw [hRpa]; infer_instance
  let : Mono (R.map p) := mono_of_mono (R.map p) (R.map a)
  let : Epi (R.map a) := epi_of_epi (R.map p) (R.map a)
  let : IsIso (R.map p) := isIso_of_mono_of_epi _
  let : IsIso (R.map a) := isIso_of_mono_of_epi _
  have hKη : genericPoint X ∉ support (kernel p) := fun h =>
    support_kernel_subset_compl_of_restrict_isIso U.ι p h ⟨⟨genericPoint X, hη⟩, rfl⟩
  have hCη : genericPoint X ∉ support (cokernel a) := fun h =>
    support_cokernel_subset_compl_of_restrict_isIso U.ι a h ⟨⟨genericPoint X, hη⟩, rfl⟩
  have hKzero := coeff_projectiveHilbertPolynomial_pushforward_eq_zero_of_generic_not_mem
    k ι n e j (kernel p) hK d hd hKη
  have hCzero := coeff_projectiveHilbertPolynomial_pushforward_eq_zero_of_generic_not_mem
    k ι n e j (cokernel a) hC d hd hCη
  have hS₁ : (ShortComplex.kernelSequence p).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact p, epi_g := inferInstanceAs (Epi p) }
  have hS₂ : (ShortComplex.cokernelSequence a).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact a, mono_f := inferInstanceAs (Mono a) }
  let P := Scheme.Modules.pushforward j
  have hpush {F : X.Modules} (hF : affineLocallyFiniteType X F) :
      affineLocallyFiniteType (ProjectiveSpace k ι) (P.obj F) :=
    Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward j hF
  have h₁ := projectiveHilbertPolynomial_add_of_shortExact k ι n e _
    (hS₁.map_of_exact P) (hpush hK) (hpush hM) (hpush hI)
  have h₂ := projectiveHilbertPolynomial_add_of_shortExact k ι n e _
    (hS₂.map_of_exact P) (hpush hI) (hpush hN) (hpush hC)
  change projectiveHilbertPolynomial k ι (P.obj M) =
    projectiveHilbertPolynomial k ι (P.obj (kernel p)) +
      projectiveHilbertPolynomial k ι (P.obj I) at h₁
  change projectiveHilbertPolynomial k ι (P.obj N) =
    projectiveHilbertPolynomial k ι (P.obj I) +
      projectiveHilbertPolynomial k ι (P.obj (cokernel a)) at h₂
  have hc₁ := congrArg (fun Q : ℚ[X] => Q.coeff d) h₁
  have hc₂ := congrArg (fun Q : ℚ[X] => Q.coeff d) h₂
  change (projectiveHilbertPolynomial k ι (P.obj (kernel p))).coeff d = 0 at hKzero
  change (projectiveHilbertPolynomial k ι (P.obj (cokernel a))).coeff d = 0 at hCzero
  simp only [Polynomial.coeff_add, hKzero, zero_add] at hc₁
  simp only [Polynomial.coeff_add, hCzero, add_zero] at hc₂
  exact hc₁.trans hc₂.symm

/-- Isomorphic coherent restrictions on a generic-point neighbourhood give
the same top-dimensional coefficient under the original projective embedding.
The coherent comparison span is chosen only inside this proof. -/
theorem coeff_projectiveHilbertPolynomial_pushforward_eq_of_restrictIso
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (M N : X.Modules) (hM : affineLocallyFiniteType X M) (hN : affineLocallyFiniteType X N)
    (U : X.Opens) (hη : genericPoint X ∈ U) (eU : M.restrict U.ι ≅ N.restrict U.ι)
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : ℕ)) :
    (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj M)).coeff d =
      (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj N)).coeff d := by
  obtain ⟨H, a, b, hH, _, ha, hb⟩ :=
    Scheme.Modules.Coherent.exists_coherent_common_comparison U.ι M N hM hN eU
  let : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) := ha
  let : IsIso ((Scheme.Modules.restrictFunctor U.ι).map b) := hb
  have hA := coeff_projectiveHilbertPolynomial_pushforward_eq_of_restrict_isIso
    k ι n e j H M hH hM a U hη d hd
  have hB := coeff_projectiveHilbertPolynomial_pushforward_eq_of_restrict_isIso
    k ι n e j H N hH hN b U hη d hd
  exact hA.symm.trans hB

end AlgebraicGeometry.Scheme.Cohomology
