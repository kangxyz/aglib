/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.FinitePullback
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.RankScaling
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.SupportDegree
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Support
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Fibres

/-!
# Actual locally free rank from a projective pullback scaling

For an original finite locally free endomorphism of an integral projective
field scheme, scaling the pulled O(1) class by c forces actual locally free
rank c^d, where d is the original scheme dimension. The rank witness is
chosen from the actual direct-image module; its top coefficient is compared
with the proved polynomial reparametrization. The native support theorem
identifies the polynomial degree with the original scheme dimension.

This is a general scaling criterion. Multiplication on a field group must
discharge its scaling law and actual dimension in the group-specific owner.
No polynomial-degree or numerical-rank premise is used here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original finite locally free endomorphism has rank c^d when its
actual pulled O(1) class scales by positive c and its source has dimension d. -/
theorem hasLocallyFreeRank_pow_of_projective_pullback_scaling
    (k : Type u) [Field k] [Infinite k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {X : Scheme.{u}} [IsIntegral X] (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (f : X ⟶ X) (hfree : Scheme.Hom.FiniteLocallyFree f)
    (hbase : f ≫ (j ≫ toSpec k ι) = j ≫ toSpec k ι) (c : ℕ) (hc : 0 < c)
    (hscale : pullbackClass f (pullbackClass j (classOf _ (twistingLineBundle k ι 1))) =
      c • pullbackClass j (classOf _ (twistingLineBundle k ι 1)))
    (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    Scheme.Hom.HasLocallyFreeRank f (c ^ d) := by
  let : IsAffineHom f := hfree.1
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let E := pushforwardStructureSheaf f
  let P := projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj O)
  let Q := projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj E)
  have hO :=
    Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward j
      (affineLocallyFiniteType_structureModule X)
  have hP : P ≠ 0 := by
    intro hz
    exact not_isZero_pushforward_unit j
      (isZero_of_projectiveHilbertPolynomial_eq_zero k ι n e hO hz)
  have hdegree : P.natDegree = d := by
    have h := topologicalKrullDim_support_eq_natDegree_projectiveHilbertPolynomial k ι n e
      ((Scheme.Modules.pushforward j).obj O) hO (not_isZero_pushforward_unit j)
    rw [topologicalKrullDim_support_pushforward_unit, hd] at h
    exact_mod_cast h.symm
  obtain ⟨r, hr⟩ := Scheme.Hom.exists_hasLocallyFreeRank f hfree
  have hcoeff := coeff_projectiveHilbertPolynomial_pushforward_of_sheafHasRank
    k ι n e j E r hr.2 d hd.le
  have hpoly : Q = P.comp (Polynomial.C (c : ℚ) * Polynomial.X) :=
    projectiveHilbertPolynomial_pushforwardStructure_eq_comp_mul k ι n e j f hbase c hscale
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
  have hdegreeQ : (P.comp (Polynomial.C (c : ℚ) * Polynomial.X)).natDegree = d := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X (c : ℚ) hcQ,
      mul_one, hdegree]
  have hleading : (P.comp (Polynomial.C (c : ℚ) * Polynomial.X)).leadingCoeff =
      (r : ℚ) * P.leadingCoeff := by
    change Q.coeff d = (r : ℚ) * P.coeff d at hcoeff
    rw [hpoly] at hcoeff
    have hPcoeff : P.coeff d = P.leadingCoeff := by
      rw [← hdegree, Polynomial.coeff_natDegree]
    have hQcoeff : (P.comp (Polynomial.C (c : ℚ) * Polynomial.X)).coeff d =
        (P.comp (Polynomial.C (c : ℚ) * Polynomial.X)).leadingCoeff := by
      rw [← hdegreeQ, Polynomial.coeff_natDegree]
    simpa only [hPcoeff, hQcoeff] using hcoeff
  have hrank := Polynomial.nat_eq_pow_of_leadingCoeff_comp_C_mul_X hP c r d hc hdegree hleading
  exact hrank ▸ hr

end AlgebraicGeometry.Scheme.Cohomology
