/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.FieldTheory.Galois.FiniteStabilizers
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Finite dependence on algebraic scalar coefficients

Source: `R5Lab.Aglib.FieldTheory.Galois.SimplexFiniteCoefficients`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v
variable {R : Type u} [CommSemiring R] {ι : Type v}

/-- A scalar endomorphism fixing the actual nonzero coefficients fixes the polynomial. -/
theorem map_eq_self_of_fixed_coeffs (p : MvPolynomial ι R) (f : R →+* R)
    (hf : ∀ a ∈ p.coeffs, f a = a) : map f p = p := by
  ext m
  rw [coeff_map]
  by_cases h : p.coeff m = 0
  · simp only [h, map_zero]
  · exact hf _ (coeff_mem_coeffs m h)

end MvPolynomial

namespace Field.absoluteGaloisGroup

universe u v
variable (K : Type u) [Field K]

/-- Every polynomial over the chosen closure depends on finitely many actual scalars. -/
theorem exists_finite_fixed_polynomial {ι : Type v}
    (p : MvPolynomial ι (AlgebraicClosure K)) :
    ∃ s : Finset (AlgebraicClosure K), ∀ g : Field.absoluteGaloisGroup K,
      (∀ a ∈ s, g.toRingHom a = a) → MvPolynomial.map g.toRingHom p = p :=
  ⟨p.coeffs, fun g hg => MvPolynomial.map_eq_self_of_fixed_coeffs p g.toRingHom hg⟩

/-- The ordinary monoid algebra has the same finite scalar-dependence property. -/
theorem exists_finite_fixed_monoidAlgebra {M : Type v} [Monoid M]
    (p : MonoidAlgebra (AlgebraicClosure K) M) :
    ∃ s : Finset (AlgebraicClosure K), ∀ g : Field.absoluteGaloisGroup K,
      (∀ a ∈ s, g.toRingHom a = a) → MonoidAlgebra.mapRingHom M g.toRingHom p = p := by
  classical
  refine ⟨p.coeff.support.image p.coeff, ?_⟩
  intro g hg
  ext m
  rw [MonoidAlgebra.coeff_mapRingHom]
  by_cases hm : m ∈ p.coeff.support
  · exact hg _ (Finset.mem_image_of_mem _ hm)
  · have hz : p.coeff m = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hm
    simp only [hz, map_zero]

end Field.absoluteGaloisGroup
