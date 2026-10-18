/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.FiniteMixedGeneration
public import Aglib.KTheory.MilnorK.Norm.Polynomial.One
public import Aglib.RingTheory.AdjoinRootCoefficientEquiv

/-!
# Finite coefficient comparison of polynomial norms

Actual polynomial-presentation norms agree on the mixed span under a specified
base-field algebra equivalence. The irreducible coefficient-image case of
base change has exactly one actual target factor. These formulas are used with
finite classwise mixed generation, preserving the original quotient maps.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial PolynomialResidue Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L]

/-- An actual base-field equivalence preserves the literal mixed tuple. -/
theorem map_mixed_symbol_algEquiv (m : ℕ) (p q : MonicIrreducible k)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (a : SymbolTuple k m) (b : (AdjoinRoot p.val)ˣ) :
    MilnorK.map (m + 1) e.toRingHom
      (symbol (Fin.snoc (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ a) b)) =
        symbol (Fin.snoc (Units.map (algebraMap k (AdjoinRoot q.val)).toMonoidHom ∘ a)
          (Units.map e.toRingHom.toMonoidHom b)) := by
  rw [MilnorK.map_symbol, Fin.comp_snoc]
  congr 2
  funext i
  apply Units.ext
  exact e.commutes (a i)

/-- Norm agreement on each mixed symbol uses the actual ordinary field norm. -/
theorem polynomialNorm_map_algEquiv_mixed_symbol [CharZero k]
    (m : ℕ) (p q : MonicIrreducible k) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (a : SymbolTuple k m) (b : (AdjoinRoot p.val)ˣ) :
    polynomialNorm (m + 1) q (MilnorK.map (m + 1) e.toRingHom
      (symbol (Fin.snoc (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ a) b))) =
        polynomialNorm (m + 1) p
          (symbol (Fin.snoc (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom ∘ a) b)) := by
  rw [map_mixed_symbol_algEquiv, polynomialNorm_symbol_constants_unit,
    polynomialNorm_symbol_constants_unit]
  congr 2
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv e b

/-- The two actual presentation norms agree on the original mixed span. -/
theorem polynomialNorm_map_algEquiv_of_mem_mixedSpan [CharZero k]
    (m : ℕ) (p q : MonicIrreducible k) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (x : K (AdjoinRoot p.val) (m + 1))
    (hx : x ∈ mixedSpan (algebraMap k (AdjoinRoot p.val)) m) :
    polynomialNorm (m + 1) q (MilnorK.map (m + 1) e.toRingHom x) =
      polynomialNorm (m + 1) p x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, rfl⟩ := hy
    exact polynomialNorm_map_algEquiv_mixed_symbol m p q e a b
  | zero => simp only [map_zero]
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | smul a y _ hy => simp only [LinearMap.map_smul, hy]

/-- If the entire coefficient image is irreducible, there is exactly one
actual target place. -/
theorem placesAbove_eq_singleton (φ : k →+* L) (p : MonicIrreducible k)
    (q : MonicIrreducible L) (hq : q.val = p.val.map φ) :
    placesAbove φ p = {q} := by
  classical
  ext r
  rw [mem_placesAbove, Finset.mem_singleton]
  constructor
  · intro h
    apply Subtype.ext
    exact eq_of_monic_of_associated r.property.1 q.property.1
      (r.property.2.associated_of_dvd q.property.2 (hq.symm ▸ h))
  · rintro rfl
    rw [hq]

/-- Base change at an irreducible whole coefficient image has one summand,
with the original literal root-field quotient map. -/
theorem polynomialNorm_restrict_irreducible [CharZero k]
    (φ : k →+* L) (n : ℕ) (p : MonicIrreducible k) (q : MonicIrreducible L)
    (hq : q.val = p.val.map φ) (z : K (AdjoinRoot p.val) n) :
    MilnorK.map n φ (polynomialNorm n p z) =
      polynomialNorm n q
        (MilnorK.map n (adjoinRootMap φ p.val q.val (hq ▸ dvd_rfl)) z) := by
  classical
  rw [polynomialNorm_restrict]
  have hmem : q ∈ placesAbove φ p := (mem_placesAbove φ p q).mpr (hq ▸ dvd_rfl)
  let q' : {q // q ∈ placesAbove φ p} := ⟨q, hmem⟩
  rw [Finset.sum_eq_single q']
  · intro r _ hr
    have heq : r = q' := Subtype.ext (by
      simpa only [placesAbove_eq_singleton φ p q hq, Finset.mem_singleton]
        using r.property)
    exact (hr heq).elim
  · intro h
    exact (h (Finset.mem_attach _ _)).elim

/-- Algebra-equivalent root fields have exactly the same polynomial degree. -/
theorem natDegree_eq_of_root_algEquiv (p q : MonicIrreducible k)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) : p.val.natDegree = q.val.natDegree := by
  have h := e.toLinearEquiv.finrank_eq
  rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank,
    (AdjoinRoot.powerBasis q.property.2.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, AdjoinRoot.powerBasis_dim] at h
  exact h

/-- The polynomial-local quotient map is the same coefficient map used by
literal scalar extension of root-algebra equivalences. -/
theorem adjoinRootMap_eq_coefficientMap [Algebra k L] (p : k[X])
    [Fact (Irreducible p)] [Fact (Irreducible (p.map (algebraMap k L)))] :
    adjoinRootMap (algebraMap k L) p (p.map (algebraMap k L)) dvd_rfl =
      (AdjoinRoot.coefficientMap (L := L) p).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change adjoinRootMap (algebraMap k L) p (p.map (algebraMap k L)) dvd_rfl
      (algebraMap k (AdjoinRoot p) a) =
        AdjoinRoot.coefficientMap p (algebraMap k (AdjoinRoot p) a)
    rw [adjoinRootMap_algebraMap, AlgHom.commutes]
    rfl
  · exact (adjoinRootMap_root (algebraMap k L) p _ dvd_rfl).trans
      (AdjoinRoot.coefficientMap_root p).symm

universe u

/-- Two prime-degree presentations of the same extension give the same value
on a specified class after some actual finite separable coefficient extension
of degree coprime to that prime. No torsion-detection or norm-tower hypothesis
is used in this restricted equality. -/
theorem exists_coprime_restriction_eq_of_algEquiv {k : Type u} [Field k] [CharZero k]
    (p q : MonicIrreducible k) (hp : p.val.natDegree.Prime)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (m : ℕ) (x : K (AdjoinRoot p.val) (m + 1)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      p.val.natDegree.Coprime (Module.finrank k L) ∧
      MilnorK.map (m + 1) (algebraMap k L)
          (polynomialNorm (m + 1) q (MilnorK.map (m + 1) e.toRingHom x)) =
        MilnorK.map (m + 1) (algebraMap k L) (polynomialNorm (m + 1) p x) := by
  obtain ⟨L, hL, hA, hfd, hsep, hcop, pL, heq, hdiv, c, hc⟩ :=
    exists_finite_coprime_mixed_expansion p hp m x
  let := hfd
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  rcases pL with ⟨pL, hpL⟩
  change pL = p.val.map (algebraMap k L) at heq
  subst pL
  let : Fact (Irreducible (p.val.map (algebraMap k L))) := ⟨hpL.2⟩
  let p' : MonicIrreducible L := ⟨p.val.map (algebraMap k L), hpL⟩
  have hcopq : q.val.natDegree.Coprime (Module.finrank k L) := by
    rw [← natDegree_eq_of_root_algEquiv p q e]
    exact hcop
  let q' : MonicIrreducible L := ⟨q.val.map (algebraMap k L),
    q.property.1.map _, q.property.1.irreducible_map_of_natDegree_coprime q.property.2 hcopq⟩
  let : Fact (Irreducible q'.val) := ⟨q'.property.2⟩
  let e' : AdjoinRoot p'.val ≃ₐ[L] AdjoinRoot q'.val :=
    AdjoinRoot.coefficientEquiv (L := L) e
  have hmixed : MilnorK.map (m + 1)
      (adjoinRootMap (algebraMap k L) p.val p'.val dvd_rfl) x ∈
        mixedSpan (algebraMap L (AdjoinRoot p'.val)) m := by
    rw [← hc]
    exact Submodule.sum_mem _ fun ab _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨ab.1, ab.2, rfl⟩)
  have hsquare : (adjoinRootMap (algebraMap k L) q.val q'.val dvd_rfl).comp
      e.toRingHom = e'.toRingHom.comp
        (adjoinRootMap (algebraMap k L) p.val p'.val dvd_rfl) := by
    rw [adjoinRootMap_eq_coefficientMap, adjoinRootMap_eq_coefficientMap]
    apply RingHom.ext
    intro a
    exact (AdjoinRoot.coefficientEquiv_coefficientMap (L := L) e a).symm
  refine ⟨L, hL, hA, hfd, hsep, hcop, ?_⟩
  rw [polynomialNorm_restrict_irreducible (algebraMap k L) (m + 1) q q' rfl,
    polynomialNorm_restrict_irreducible (algebraMap k L) (m + 1) p p' rfl]
  have hmaps : MilnorK.map (m + 1)
      (adjoinRootMap (algebraMap k L) q.val q'.val dvd_rfl)
      (MilnorK.map (m + 1) e.toRingHom x) =
        MilnorK.map (m + 1) e'.toRingHom
          (MilnorK.map (m + 1) (adjoinRootMap (algebraMap k L) p.val p'.val dvd_rfl) x) := by
    rw [← LinearMap.comp_apply, ← MilnorK.map_comp, hsquare, MilnorK.map_comp,
      LinearMap.comp_apply]
  rw [hmaps]
  exact polynomialNorm_map_algEquiv_of_mem_mixedSpan m p' q' e' _ hmixed

end MilnorK.PolynomialNorm
