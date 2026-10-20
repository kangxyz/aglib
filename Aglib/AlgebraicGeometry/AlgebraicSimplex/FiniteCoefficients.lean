/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AlgebraicSimplex.CoefficientEquiv
public import Aglib.FieldTheory.Galois.FiniteCoefficientDependence

/-!
# Finite scalar dependence on algebraic simplices

Every individual coordinate-quotient or Laurent element depends on finitely many
actual scalars of the chosen algebraic closure. An automorphism fixing those
scalars fixes the original element through the displayed coefficient map. This
statement does not itself choose a finite field model or a geometric cover.

The two geometric-algebra suffixes of
`R5Lab.Aglib.FieldTheory.Galois.SimplexFiniteCoefficients` at revision
`f8a3314ddecffcada2ec721d26d56a937bed9690` are separated from the generic field
helpers. No finite-correspondence, cycle or K-group implementation is imported.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.AlgebraicSimplex

universe u
variable (K : Type u) [Field K]

/-- An actual simplex element depends on finitely many scalars of the chosen closure. -/
theorem exists_finite_fixed_scalars (d : ℕ)
    (x : AlgebraicSimplex.CoordinateRing (AlgebraicClosure K) d) :
    ∃ s : Finset (AlgebraicClosure K), ∀ g : Field.absoluteGaloisGroup K,
      (∀ a ∈ s, g.toRingHom a = a) → AlgebraicSimplex.coefficientMap g.toRingHom d x = x := by
  classical
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨{a}, ?_⟩
    intro g hg
    change AlgebraicSimplex.coefficientMap g.toRingHom d
      (algebraMap (AlgebraicClosure K)
        (AlgebraicSimplex.CoordinateRing (AlgebraicClosure K) d) a) = _
    rw [AlgebraicSimplex.coefficientMap_algebraMap, hg a (by simp)]
    rfl
  | add p q hp hq =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, ht⟩ := hq
    refine ⟨s ∪ t, ?_⟩
    intro g hg
    simp only [map_add]
    rw [hs g (fun a ha => hg a (Finset.mem_union_left _ ha)),
      ht g (fun a ha => hg a (Finset.mem_union_right _ ha))]
  | mul_X p i hp =>
    obtain ⟨s, hs⟩ := hp
    refine ⟨s, ?_⟩
    intro g hg
    change AlgebraicSimplex.coefficientMap g.toRingHom d
      (Ideal.Quotient.mk _ p * AlgebraicSimplex.coordinate (AlgebraicClosure K) d i) =
        Ideal.Quotient.mk _ p * AlgebraicSimplex.coordinate (AlgebraicClosure K) d i
    rw [map_mul, hs g hg, AlgebraicSimplex.coefficientMap_coordinate]

/-- The same finite scalar dependence holds for the actual two-variable Laurent carrier. -/
theorem exists_finite_fixed_laurent_scalars (d : ℕ)
    (x : MonoidAlgebra (CoordinateRing (AlgebraicClosure K) d) (Multiplicative (ℤ × ℤ))) :
    ∃ s : Finset (AlgebraicClosure K), ∀ g : Field.absoluteGaloisGroup K,
      (∀ a ∈ s, g.toRingHom a = a) → laurentCoefficientEquiv g.toRingEquiv d x = x := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨∅, fun g _ => map_zero _⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, ?_⟩
    intro g hg
    rw [map_add, hs g (fun a ha => hg a (Finset.mem_union_left _ ha)),
      ht g (fun a ha => hg a (Finset.mem_union_right _ ha))]
  | single m a =>
    obtain ⟨s, hs⟩ := exists_finite_fixed_scalars K d a
    refine ⟨s, ?_⟩
    intro g hg
    rw [laurentCoefficientEquiv_single, hs g hg]

end AlgebraicGeometry.AlgebraicSimplex
