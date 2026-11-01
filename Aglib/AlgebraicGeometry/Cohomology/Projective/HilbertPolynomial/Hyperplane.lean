/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.LeadingCoefficient
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.GeneralHyperplane

/-!
# The native Hilbert polynomial of a hyperplane cokernel

An actual monomorphism `F → O(a) ⊗ F` has cokernel polynomial
`P_F(X + a) - P_F(X)`. Over an infinite field the existing general
hyperplane constructor supplies a section of `O(1)` for which the original
section-multiplication map is monic. This is the exact finite-difference
identity needed by support-dimension induction. The support-dimension drop
is a separate geometric assertion and is not assumed or claimed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u)

/-- The Hilbert polynomial of the cokernel of an actual injection into a
tensor twist is the corresponding difference of the original polynomial. -/
theorem projectiveHilbertPolynomial_cokernel_mono_twist
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace k ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : ℤ)
    (ν : F ⟶ (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι a)).obj F)
    [Mono ν] :
    projectiveHilbertPolynomial k ι (cokernel ν) =
      (projectiveHilbertPolynomial k ι F).comp (Polynomial.X + Polynomial.C (a : ℚ)) -
        projectiveHilbertPolynomial k ι F := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  have hG := twistingTensor_affineLocallyFiniteType k ι a F hF
  have hC := (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel ν hF hG
  have hS : (ShortComplex.cokernelSequence ν).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact ν, mono_f := inferInstanceAs (Mono ν) }
  have h := projectiveHilbertPolynomial_add_of_shortExact k ι n e _ hS hF hG hC
  change projectiveHilbertPolynomial k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι a)).obj F) =
    projectiveHilbertPolynomial k ι F + projectiveHilbertPolynomial k ι (cokernel ν) at h
  rw [projectiveHilbertPolynomial_twistingTensor k ι n e F hF a] at h
  exact (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans h.symm)

/-- A general section over an infinite field gives the native monic
hyperplane map and its exact Hilbert-polynomial finite difference. -/
theorem exists_mono_hyperplane_hilbertDifference [Infinite k]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace k ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) :
    ∃ s : (twistingSheaf k ι ((1 : ℕ) : ℤ)).val.obj (op ⊤),
      let ν := (twistingTensorZeroIso k ι).inv.app F ≫
        (twistingTensorMultiply k ι ((1 : ℕ) : ℤ) 0 s).app F
      Mono ν ∧ projectiveHilbertPolynomial k ι (cokernel ν) =
        (projectiveHilbertPolynomial k ι F).comp (Polynomial.X + 1) -
          projectiveHilbertPolynomial k ι F := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  obtain ⟨s, hs⟩ := exists_forall_frameCoefficient_isSMulRegular k ι
    (fun _ : PUnit.{1} => F) (fun _ => hF)
  let ν := (twistingTensorZeroIso k ι).inv.app F ≫
    (twistingTensorMultiply k ι ((1 : ℕ) : ℤ) 0 s).app F
  let : Mono ν := mono_twistingTensorMultiply_of_isSMulRegular k ι s F (hs PUnit.unit)
  refine ⟨s, inferInstance, ?_⟩
  simpa [ν] using projectiveHilbertPolynomial_cokernel_mono_twist k ι n e F hF
    (((1 : ℕ) : ℤ) + 0) ν

end AlgebraicGeometry.Scheme.Cohomology
