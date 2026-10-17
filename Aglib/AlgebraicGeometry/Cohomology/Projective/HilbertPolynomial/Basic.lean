/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Difference
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Coordinate
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic

/-!
# The Hilbert polynomial of a coherent module on projective space over a field

For a field `k`, a coordinate labeling `ι ≃ Fin (n + 1)` and a coherent module `F` on the
actual polynomial projective space `ProjectiveSpace k ι`, the Hilbert function
`m ↦ χ(O(m) ⊗ F)` agrees at every integer with a rational polynomial (Stacks, Tag 08AC;
Nitsure, arXiv:math/0504590v1, §1, p. 4). Here `O(m) ⊗ F` is the native tensor twist and `χ` the
alternating sum of the dimensions of the original `Sheaf.H` over `k`.

The proof stays on projective space. If `F` is killed by the coordinates in `S` and `j ∉ S`,
multiplication by `Xⱼ` gives `F → O(1 + 0) ⊗ F` with kernel `K` and cokernel `C` killed by
`S ∪ {j}`; additivity of `χ` gives `χ(F(m + 1)) - χ(F(m)) = χ(C(m)) - χ(K(m))`, and a module
killed by every coordinate is zero. No infinite field or hyperplane section is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u)

/-- The Hilbert function `m ↦ χ(O(m) ⊗ F)` of a module on projective space over a field.
Native `finrank` and `finsum` in `χ` are zero outside finite dimension and finite support.
For coherent `F`, every `H^q(O(m) ⊗ F)` is finite-dimensional by
`projectiveCohomology_finite` (`Cohomology/Projective/Finiteness.lean`) and vanishes for
`q > n` by `projectiveCohomology_subsingleton_of_gt` (`Cohomology/Projective/Vanishing.lean`),
so `χ(O(m) ⊗ F)` is the genuine finite alternating sum. -/
def projectiveHilbertFunction (F : (ProjectiveSpace k ι).Modules) (m : ℤ) : ℤ :=
  projectiveEulerChar k ι
    ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).obj F)

/-- The Hilbert function of a coherent module killed by the coordinates in `S` is polynomial,
by induction on the number of remaining coordinates. -/
theorem isPolynomialOnInt_projectiveHilbertFunction_of_killed [Fintype ι] [DecidableEq ι]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : ℕ) :
    ∀ (S : Finset ι) (F : (ProjectiveSpace k ι).Modules), (Finset.univ \ S).card = N →
      affineLocallyFiniteType (ProjectiveSpace k ι) F →
      (∀ i ∈ S, IsKilledByTwistSection k ι ((1 : ℕ) : ℤ) (coordinateSection k ι i) F) →
      Polynomial.IsPolynomialOnInt (projectiveHilbertFunction k ι F) := by
  induction N with
  | zero =>
    intro S F hcard _ hkill
    have hS (i : ι) : i ∈ S := by
      by_contra hi
      have hmem : i ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      rw [Finset.card_eq_zero.mp hcard] at hmem
      simp at hmem
    have hzero : IsZero F :=
      isZero_of_coordinate_eq_zero k ι F (fun i => hkill i (hS i) (-1))
    refine (Polynomial.IsPolynomialOnInt.const 0).congr (fun m => ?_)
    exact (projectiveEulerChar_of_isZero k ι (Functor.map_isZero _ hzero)).symm
  | succ N ih =>
    intro S F hcard hF hkill
    obtain ⟨j, hj⟩ : (Finset.univ \ S).Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    have hjS : j ∉ S := (Finset.mem_sdiff.mp hj).2
    have hcard' : (Finset.univ \ insert j S).card = N := by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem hj, hcard]
      rfl
    let := Finite.of_fintype ι
    let τ := twistingTensorMultiply k ι ((1 : ℕ) : ℤ) 0 (coordinateSection k ι j)
    let ν : F ⟶ (moduleTensorLeftFunctor (ProjectiveSpace k ι)
        (twistingSheaf k ι (((1 : ℕ) : ℤ) + 0))).obj F :=
      (twistingTensorZeroIso k ι).inv.app F ≫ τ.app F
    let p := Abelian.factorThruImage ν
    let i := Abelian.image.ι ν
    have hpi : p ≫ i = ν := Abelian.image.fac ν
    have hG : affineLocallyFiniteType (ProjectiveSpace k ι) ((moduleTensorLeftFunctor
        (ProjectiveSpace k ι) (twistingSheaf k ι (((1 : ℕ) : ℤ) + 0))).obj F) :=
      twistingTensor_affineLocallyFiniteType k ι _ F hF
    have hI : affineLocallyFiniteType (ProjectiveSpace k ι) (Abelian.image ν) :=
      (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_kernel (cokernel.π ν) hG
        ((affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel ν hF hG)
    have hK : affineLocallyFiniteType (ProjectiveSpace k ι) (kernel p) :=
      (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_kernel p hF hI
    have hC : affineLocallyFiniteType (ProjectiveSpace k ι) (cokernel i) :=
      (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel i hI hG
    have hS₁ : (ShortComplex.kernelSequence p).ShortExact :=
      { exact := ShortComplex.kernelSequence_exact p, epi_g := inferInstanceAs (Epi p) }
    have hS₂ : (ShortComplex.cokernelSequence i).ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact i, mono_f := inferInstanceAs (Mono i) }
    have hKkill (i' : ι) (hi' : i' ∈ insert j S) :
        IsKilledByTwistSection k ι ((1 : ℕ) : ℤ) (coordinateSection k ι i') (kernel p) := by
      rcases Finset.mem_insert.mp hi' with rfl | hi'
      · apply IsKilledByTwistSection.of_comp_eq_zero (kernel.ι p)
        change kernel.ι p ≫ ν = 0
        have h : kernel.ι p ≫ p ≫ i = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
        rwa [hpi] at h
      · exact (hkill i' hi').of_mono (kernel.ι p)
    have hCkill (i' : ι) (hi' : i' ∈ insert j S) :
        IsKilledByTwistSection k ι ((1 : ℕ) : ℤ) (coordinateSection k ι i') (cokernel i) := by
      rcases Finset.mem_insert.mp hi' with rfl | hi'
      · apply IsKilledByTwistSection.of_cokernel (cokernel.π i)
        have hτ : τ.app F = (twistingTensorZeroIso k ι).hom.app F ≫ ν := by
          simp only [ν, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
        change τ.app F ≫ cokernel.π i = 0
        have h : p ≫ i ≫ cokernel.π i = 0 := by rw [cokernel.condition, comp_zero]
        rw [← Category.assoc, hpi] at h
        refine (congrArg (fun x => x ≫ cokernel.π i) hτ).trans ?_
        rw [Category.assoc, h, comp_zero]
      · exact ((hkill i' hi').tensor _).of_epi (cokernel.π i)
    have hKpoly := ih (insert j S) (kernel p) hcard' hK hKkill
    have hCpoly := ih (insert j S) (cokernel i) hcard' hC hCkill
    apply Polynomial.IsPolynomialOnInt.of_fwdDiff
    refine (hCpoly.sub hKpoly).congr (fun m => ?_)
    have hfin := twistingSheaf_isFiniteLocallyFree k ι m
    have h₁ := projectiveEulerChar_add_of_shortExact k ι n e _
      (tensor_shortExact_finiteLocallyFree (twistingSheaf k ι m) _ hS₁)
      (twistingTensor_affineLocallyFiniteType k ι m _ hK)
      (twistingTensor_affineLocallyFiniteType k ι m _ hF)
      (twistingTensor_affineLocallyFiniteType k ι m _ hI)
    have h₂ := projectiveEulerChar_add_of_shortExact k ι n e _
      (tensor_shortExact_finiteLocallyFree (twistingSheaf k ι m) _ hS₂)
      (twistingTensor_affineLocallyFiniteType k ι m _ hI)
      (twistingTensor_affineLocallyFiniteType k ι m _ hG)
      (twistingTensor_affineLocallyFiniteType k ι m _ hC)
    have hcomp := projectiveEulerChar_congr k ι
      ((twistingTensorCompIso k ι m (((1 : ℕ) : ℤ) + 0)).app F)
    rw [show m + (((1 : ℕ) : ℤ) + 0) = m + 1 by push_cast; ring] at hcomp
    simp only [Functor.comp_obj] at hcomp
    simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
      ShortComplex.kernelSequence_X₁, ShortComplex.kernelSequence_X₂,
      ShortComplex.kernelSequence_X₃, ShortComplex.cokernelSequence_X₁,
      ShortComplex.cokernelSequence_X₂, ShortComplex.cokernelSequence_X₃] at h₁ h₂
    unfold projectiveHilbertFunction
    linarith

/-- **Hilbert polynomial.** For a coherent module `F` on projective `n`-space over a field,
the function `m ↦ χ(O(m) ⊗ F)` agrees at every integer with a rational polynomial. -/
theorem isPolynomialOnInt_projectiveHilbertFunction (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) :
    Polynomial.IsPolynomialOnInt (projectiveHilbertFunction k ι F) := by
  classical
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  exact isPolynomialOnInt_projectiveHilbertFunction_of_killed k ι n e _ ∅ F rfl hF
    (fun i hi => absurd hi (Finset.notMem_empty i))

/-- The Hilbert polynomial of a module on projective space over a field: the rational
polynomial of its Hilbert function (`0` when the function is not polynomial). -/
def projectiveHilbertPolynomial (F : (ProjectiveSpace k ι).Modules) : ℚ[X] :=
  Polynomial.polynomialOnInt (projectiveHilbertFunction k ι F)

/-- The Hilbert polynomial computes `χ(O(m) ⊗ F)` at every integer `m`. -/
theorem projectiveHilbertFunction_eq_eval (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F)
    (m : ℤ) : (projectiveHilbertFunction k ι F m : ℚ) =
      (projectiveHilbertPolynomial k ι F).eval (m : ℚ) :=
  (isPolynomialOnInt_projectiveHilbertFunction k ι n e F hF).eval_polynomialOnInt m

/-- A rational polynomial computing `χ(O(m) ⊗ F)` at every integer is the Hilbert
polynomial. -/
theorem projectiveHilbertPolynomial_eq_of_eval (F : (ProjectiveSpace k ι).Modules)
    {Φ : ℚ[X]} (hΦ : ∀ m : ℤ, (projectiveHilbertFunction k ι F m : ℚ) = Φ.eval (m : ℚ)) :
    projectiveHilbertPolynomial k ι F = Φ :=
  Polynomial.IsPolynomialOnInt.polynomialOnInt_eq hΦ

/-- Isomorphic modules have the same Hilbert function. -/
theorem projectiveHilbertFunction_congr {M N : (ProjectiveSpace k ι).Modules} (e : M ≅ N) :
    projectiveHilbertFunction k ι M = projectiveHilbertFunction k ι N :=
  funext fun m => projectiveEulerChar_congr k ι
    ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).mapIso e)

/-- Isomorphic modules have the same Hilbert polynomial. -/
theorem projectiveHilbertPolynomial_congr {M N : (ProjectiveSpace k ι).Modules} (e : M ≅ N) :
    projectiveHilbertPolynomial k ι M = projectiveHilbertPolynomial k ι N := by
  unfold projectiveHilbertPolynomial
  rw [projectiveHilbertFunction_congr k ι e]

/-- Hilbert polynomials are additive on short exact sequences of coherent modules. -/
theorem projectiveHilbertPolynomial_add_of_shortExact (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace k ι).Modules) (hS : S.ShortExact)
    (h₁ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₁)
    (h₂ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₂)
    (h₃ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₃) :
    projectiveHilbertPolynomial k ι S.X₂ =
      projectiveHilbertPolynomial k ι S.X₁ + projectiveHilbertPolynomial k ι S.X₃ := by
  have : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  apply projectiveHilbertPolynomial_eq_of_eval
  intro m
  have hfin := twistingSheaf_isFiniteLocallyFree k ι m
  have h := projectiveEulerChar_add_of_shortExact k ι n e _
    (tensor_shortExact_finiteLocallyFree (twistingSheaf k ι m) S hS)
    (twistingTensor_affineLocallyFiniteType k ι m _ h₁)
    (twistingTensor_affineLocallyFiniteType k ι m _ h₂)
    (twistingTensor_affineLocallyFiniteType k ι m _ h₃)
  simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃] at h
  rw [Polynomial.eval_add, ← projectiveHilbertFunction_eq_eval k ι n e _ h₁,
    ← projectiveHilbertFunction_eq_eval k ι n e _ h₃]
  unfold projectiveHilbertFunction
  rw [h]
  push_cast
  ring

end AlgebraicGeometry.Scheme.Cohomology
