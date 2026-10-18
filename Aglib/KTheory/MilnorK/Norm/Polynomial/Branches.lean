/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootScalarBranches
public import Aglib.RingTheory.AdjoinRootCoefficientEquiv

/-!
# Actual branch reindexing under a change of polynomial presentation

An equivalence of whole polynomial quotient algebras identifies their literal
irreducible branches and their quotient fields. The comparison commutes with
both quotient maps. Applied after coefficient extension, it retains the original
maps from the old root fields, even when the coefficient images are reducible.
No Milnor norm independence or norm tower law is assumed here.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial AdjoinRoot

variable {k L : Type*} [Field k] [Field L]

/-- The actual maximal quotients of two equivalent whole root algebras correspond. -/
def rootMaximalEquiv {p q : k[X]} (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) :
    MaximalSpectrum (AdjoinRoot p) ≃ MaximalSpectrum (AdjoinRoot q) where
  toFun m := ⟨m.asIdeal.comap e.symm.toRingHom,
    m.isMaximal.comap_bijective e.symm.toRingHom e.symm.bijective⟩
  invFun m := ⟨m.asIdeal.comap e.toRingHom,
    m.isMaximal.comap_bijective e.toRingHom e.bijective⟩
  left_inv m := by
    apply MaximalSpectrum.ext
    ext a
    change e.symm (e a) ∈ m.asIdeal ↔ a ∈ m.asIdeal
    rw [e.symm_apply_apply]
  right_inv m := by
    apply MaximalSpectrum.ext
    ext a
    change e (e.symm a) ∈ m.asIdeal ↔ a ∈ m.asIdeal
    rw [e.apply_symm_apply]

/-- All actual irreducible factors are matched, without omitting nonsplit factors. -/
def polynomialBranchEquiv (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) :
    IrreducibleBranch p ≃ IrreducibleBranch q :=
  (branchEquivMaximal p hp).trans
    ((rootMaximalEquiv e).trans (branchEquivMaximal q hq).symm)

/-- The matched branch ideal is exactly the image under the given equivalence. -/
theorem polynomialBranchEquiv_ideal (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) (r : IrreducibleBranch p) :
    (branchMaximal q (polynomialBranchEquiv p q hp hq e r)).asIdeal =
      (branchMaximal p r).asIdeal.map e.toRingHom := by
  have h := (branchEquivMaximal q hq).apply_symm_apply
    (rootMaximalEquiv e (branchEquivMaximal p hp r))
  change branchMaximal q (polynomialBranchEquiv p q hp hq e r) =
    rootMaximalEquiv e (branchMaximal p r) at h
  rw [h]
  exact Ideal.comap_symm e.toRingEquiv

/-- Matched literal branch fields have a base-field algebra equivalence. -/
def polynomialBranchAlgEquiv (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) (r : IrreducibleBranch p) :
    AdjoinRoot r.val.val ≃ₐ[k]
      AdjoinRoot (polynomialBranchEquiv p q hp hq e r).val.val :=
  (branchQuotientAlgEquiv p r).symm.trans
    ((Ideal.quotientEquivAlg (branchMaximal p r).asIdeal
      (branchMaximal q (polynomialBranchEquiv p q hp hq e r)).asIdeal e
      (polynomialBranchEquiv_ideal p q hp hq e r)).trans
      (branchQuotientAlgEquiv q (polynomialBranchEquiv p q hp hq e r)))

/-- The field equivalence commutes with the original whole-algebra quotient maps. -/
theorem polynomialBranchAlgEquiv_divisorMap (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) (r : IrreducibleBranch p)
    (x : AdjoinRoot p) :
    polynomialBranchAlgEquiv p q hp hq e r (divisorMap p r.val.val r.property x) =
      divisorMap q (polynomialBranchEquiv p q hp hq e r).val.val
        (polynomialBranchEquiv p q hp hq e r).property (e x) := by
  rw [← branchQuotientEquiv_mk p r x]
  change polynomialBranchAlgEquiv p q hp hq e r
    (branchQuotientAlgEquiv p r (Ideal.Quotient.mk _ x)) = _
  simp only [polynomialBranchAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  exact branchQuotientEquiv_mk _ _ _

/-- Matching factors have the same actual polynomial degree. -/
theorem polynomialBranchEquiv_natDegree (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) (r : IrreducibleBranch p) :
    r.val.val.natDegree = (polynomialBranchEquiv p q hp hq e r).val.val.natDegree := by
  have h := (polynomialBranchAlgEquiv p q hp hq e r).toLinearEquiv.finrank_eq
  simpa only [(AdjoinRoot.powerBasis r.val.property.2.ne_zero).finrank,
    (AdjoinRoot.powerBasis
      (polynomialBranchEquiv p q hp hq e r).val.property.2.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim] using h

/-- Once a nonlinear whole polynomial has a root, every irreducible branch
has strictly smaller degree. This includes the branch containing that root. -/
theorem polynomialBranch_natDegree_lt_of_root (p : k[X]) (hp : p.Monic)
    (hdeg : 1 < p.natDegree) {a : k} (ha : p.IsRoot a) (r : IrreducibleBranch p) :
    r.val.val.natDegree < p.natDegree := by
  have hle := natDegree_le_of_dvd r.property hp.ne_zero
  by_contra hlt
  have heq : p = r.val.val := eq_of_monic_of_dvd_of_natDegree_le
    r.val.property.1 hp r.property (by omega)
  have hirr : Irreducible p := heq.symm ▸ r.val.property.2
  exact hirr.not_isRoot_of_natDegree_ne_one (by omega) ha

section Coefficients

variable [Algebra k L]

/-- The two existing whole-algebra coefficient maps are literally the same map. -/
theorem coefficientMap_eq_scalarMap (p : k[X]) :
    (coefficientMap (L := L) p).toRingHom = scalarMap (algebraMap k L) p := by
  rw [scalarMap_eq_map]
  rfl

/-- The actual scalar-extended equivalence commutes with the original scalar maps. -/
theorem coefficientEquiv_scalarMap {p q : k[X]}
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) (x : AdjoinRoot p) :
    coefficientEquiv (L := L) e (scalarMap (algebraMap k L) p x) =
      scalarMap (algebraMap k L) q (e x) := by
  rw [← coefficientMap_eq_scalarMap, ← coefficientMap_eq_scalarMap]
  exact coefficientEquiv_coefficientMap e x

/-- After arbitrary coefficient extension, the matched branch fields commute
with the literal original polynomial residue-field homomorphisms. In particular,
no irreducibility of the whole coefficient image is required. -/
theorem scalarBranchAlgEquiv_adjoinRootMap (p q : k[X])
    [Fact (Irreducible p)] [Fact (Irreducible q)]
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q)
    (r : IrreducibleBranch (p.map (algebraMap k L))) (x : AdjoinRoot p) :
    let hp := Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero
    let hq := Polynomial.map_ne_zero (Fact.out : Irreducible q).ne_zero
    let E := coefficientEquiv (L := L) e
    let s := polynomialBranchEquiv _ _ hp hq E r
    polynomialBranchAlgEquiv _ _ hp hq E r
        (Polynomial.LocalResidue.adjoinRootMap (algebraMap k L) p r.val.val r.property x) =
      Polynomial.LocalResidue.adjoinRootMap (algebraMap k L) q s.val.val s.property (e x) := by
  dsimp only
  rw [← divisorMap_comp_scalarMap, RingHom.comp_apply,
    polynomialBranchAlgEquiv_divisorMap, coefficientEquiv_scalarMap]
  exact congrArg (fun f : AdjoinRoot q →+* _ => f (e x))
    (divisorMap_comp_scalarMap (algebraMap k L) q _ _)

/-- Any specified embedding of the original root field supplies the degree
decrease for every branch of its scalar extension. No normality is needed. -/
theorem scalarBranch_natDegree_lt_of_rootHom (p : k[X]) (hp : p.Monic)
    [Fact (Irreducible p)] (hdeg : 1 < p.natDegree)
    (f : AdjoinRoot p →ₐ[k] L) (r : IrreducibleBranch (p.map (algebraMap k L))) :
    r.val.val.natDegree < p.natDegree := by
  have hroot : (p.map (algebraMap k L)).IsRoot (f (root p)) := by
    change eval (f (root p)) (p.map (algebraMap k L)) = 0
    rw [eval_map]
    exact AdjoinRoot.aeval_algHom_eq_zero p f
  have h := polynomialBranch_natDegree_lt_of_root (p.map (algebraMap k L))
    (hp.map _) (by simpa only [natDegree_map] using hdeg) hroot r
  simpa only [natDegree_map] using h

end Coefficients

end MilnorK.PolynomialNorm
