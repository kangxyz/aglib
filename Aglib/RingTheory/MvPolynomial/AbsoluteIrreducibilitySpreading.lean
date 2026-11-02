/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.GenericEmpty
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Actual finite coefficient algebras for polynomial factorizations

The polynomial is not replaced by a coordinate transform. For any fixed finite
list of monomials, the original coefficient equations and two inverted
coefficients define a finite-type quotient algebra. Its points are exactly
factorizations with those supports and those two coefficients invertible.
This is the finite factorization-algebra construction used in Stacks Tag 0557.
-/

@[expose] public noncomputable section

namespace MvPolynomial.FactorizationAlgebra

universe u v w

variable {R : Type u} [CommRing R] {σ : Type v} {ι : Type w} [Fintype ι]

/-- The actual coefficient variables of two factors, followed by their two
inverse variables. -/
abbrev Variables (ι : Type w) := (Bool × ι) ⊕ Bool

/-- A polynomial with the specified finite list of monomials. -/
def polynomial {S : Type*} [CommRing S] (m : ι → σ →₀ ℕ) (a : ι → S) :
    MvPolynomial σ S := ∑ i, monomial (m i) (a i)

/-- Coefficient mapping preserves the same finite list of monomials. -/
theorem map_polynomial {S T : Type*} [CommRing S] [CommRing T]
    (m : ι → σ →₀ ℕ) (a : ι → S) (g : S →+* T) :
    map g (polynomial m a) = polynomial m (fun i => g (a i)) := by
  simp only [polynomial, map_sum, map_monomial]

/-- One of the two universal factors, before imposing its actual equations. -/
def universal (m : ι → σ →₀ ℕ) (side : Bool) :
    MvPolynomial σ (MvPolynomial (Variables ι) R) :=
  polynomial m (fun i => X (Sum.inl (side, i)))

/-- The difference of the original polynomial and the product of the two
universal factors. -/
def difference (P : MvPolynomial σ R) (m : ι → σ →₀ ℕ) :
    MvPolynomial σ (MvPolynomial (Variables ι) R) :=
  map C P - universal m false * universal m true

/-- The relation asserting that the chosen coefficient has its own inverse. -/
def inverseRelation (side : Bool) (i : ι) : MvPolynomial (Variables ι) R :=
  X (Sum.inr side) * X (Sum.inl (side, i)) - 1

/-- All original coefficient equations, and exactly the two inverse equations. -/
def relations (P : MvPolynomial σ R) (m : ι → σ →₀ ℕ) (i j : ι) :
    Ideal (MvPolynomial (Variables ι) R) :=
  Ideal.span (Set.range (fun d => (difference P m).coeff d) ∪
    {inverseRelation false i, inverseRelation true j})

/-- The actual finite-type algebra representing this factorization chart. -/
abbrev Algebra (P : MvPolynomial σ R) (m : ι → σ →₀ ℕ) (i j : ι) :=
  MvPolynomial (Variables ι) R ⧸ relations P m i j

instance (P : MvPolynomial σ R) (m : ι → σ →₀ ℕ) (i j : ι) :
    _root_.Algebra.FiniteType R (Algebra P m i j) := inferInstance

/-- An original coefficient homomorphism kills the defining ideal exactly
when it kills the polynomial difference and the two inverse relations. -/
theorem relations_le_ker_iff {S : Type*} [CommRing S]
    (P : MvPolynomial σ R) (m : ι → σ →₀ ℕ) (i j : ι)
    (g : MvPolynomial (Variables ι) R →+* S) :
    relations P m i j ≤ RingHom.ker g ↔
      map g (difference P m) = 0 ∧
        g (inverseRelation false i) = 0 ∧ g (inverseRelation true j) = 0 := by
  rw [relations, Ideal.span_le]
  constructor
  · intro h
    refine ⟨?_, h (Set.mem_union_right _ (Set.mem_insert _ _)),
      h (Set.mem_union_right _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
    ext d
    have hd := h (Set.mem_union_left _ ⟨d, rfl⟩)
    change g ((difference P m).coeff d) = 0 at hd
    simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hd
  · rintro ⟨h, hi, hj⟩ z (⟨d, rfl⟩ | hz)
    · have hd := congrArg (fun Q : MvPolynomial σ S => Q.coeff d) h
      change g ((difference P m).coeff d) = 0
      simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hd
    · rcases hz with rfl | rfl
      · exact hi
      · exact hj

/-- Evaluate the original polynomial difference without changing the original
coefficient map or either finite monomial family. -/
theorem map_difference {S : Type*} [CommRing S] [_root_.Algebra R S]
    (P : MvPolynomial σ R) (m : ι → σ →₀ ℕ)
    (g : MvPolynomial (Variables ι) R →ₐ[R] S) :
    map g.toRingHom (difference P m) = map (algebraMap R S) P -
      polynomial m (fun i => g (X (Sum.inl (false, i)))) *
        polynomial m (fun i => g (X (Sum.inl (true, i)))) := by
  have hg : g.toRingHom.comp (C : R →+* MvPolynomial (Variables ι) R) =
      algebraMap R S := g.comp_algebraMap
  simp only [difference, map_sub, map_mul, map_map, universal, map_polynomial, hg]
  rfl

/-- Points of the actual quotient are precisely original factorizations with
the prescribed monomials and the two specified inverse coefficients. -/
theorem nonempty_algHom_iff {S : Type*} [CommRing S] [_root_.Algebra R S]
    (P : MvPolynomial σ R) (m : ι → σ →₀ ℕ) (i j : ι) :
    Nonempty (Algebra P m i j →ₐ[R] S) ↔
      ∃ (a b : ι → S) (u v : S),
        map (algebraMap R S) P = polynomial m a * polynomial m b ∧
          u * a i = 1 ∧ v * b j = 1 := by
  constructor
  · rintro ⟨f⟩
    let g := f.comp (Ideal.Quotient.mkₐ R (relations P m i j))
    have hg : relations P m i j ≤ RingHom.ker g.toRingHom := by
      intro x hx
      change f (Ideal.Quotient.mk _ x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    obtain ⟨hp, hi, hj⟩ := (relations_le_ker_iff P m i j g.toRingHom).mp hg
    refine ⟨fun k => g (X (Sum.inl (false, k))),
      fun k => g (X (Sum.inl (true, k))),
      g (X (Sum.inr false)), g (X (Sum.inr true)), ?_, ?_, ?_⟩
    · rw [map_difference, sub_eq_zero] at hp
      exact hp
    · change g (inverseRelation false i) = 0 at hi
      simpa only [inverseRelation, map_sub, map_mul, map_one, sub_eq_zero] using hi
    · change g (inverseRelation true j) = 0 at hj
      simpa only [inverseRelation, map_sub, map_mul, map_one, sub_eq_zero] using hj
  · rintro ⟨a, b, u, v, hp, hi, hj⟩
    let values : Variables ι → S := Sum.elim
      (fun p => if p.1 then b p.2 else a p.2) (fun side => if side then v else u)
    let g : MvPolynomial (Variables ι) R →ₐ[R] S := aeval values
    have hg : relations P m i j ≤ RingHom.ker g.toRingHom := by
      apply (relations_le_ker_iff P m i j g.toRingHom).mpr
      refine ⟨?_, ?_, ?_⟩
      · rw [map_difference]
        simpa only [g, aeval_X, values, Sum.elim_inl, Bool.false_eq_true,
          ↓reduceIte, sub_eq_zero] using hp
      · change g (inverseRelation false i) = 0
        simpa only [inverseRelation, map_sub, map_mul, map_one, g, aeval_X,
          values, Sum.elim_inr, Sum.elim_inl, Bool.false_eq_true, ↓reduceIte,
          sub_eq_zero] using hi
      · change g (inverseRelation true j) = 0
        simpa only [inverseRelation, map_sub, map_mul, map_one, g, aeval_X,
          values, Sum.elim_inr, Sum.elim_inl, ↓reduceIte, sub_eq_zero] using hj
    exact ⟨Ideal.Quotient.liftₐ (relations P m i j) g (fun x hx => hg hx)⟩

end MvPolynomial.FactorizationAlgebra
