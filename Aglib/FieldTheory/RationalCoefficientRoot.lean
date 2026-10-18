/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.RatFuncCoefficientMap
public import Aglib.RingTheory.AdjoinRootCoefficientEquiv
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The literal root field after rational-function coefficient extension

A monic irreducible remains irreducible over the rational-function field.
The resulting root field is canonically the rational-function field of the
original root field, with literal formulas on constants and the chosen root.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc

attribute [local instance] Polynomial.algebra

variable {k : Type*} [Field k]

/-- A monic irreducible polynomial remains irreducible over `k(X)`. -/
theorem Polynomial.Monic.irreducible_map_ratFunc_C {p : k[X]} (hp : p.Monic)
    (hirr : Irreducible p) : Irreducible (p.map (RatFunc.C : k →+* RatFunc k)) := by
  have hpoly : Irreducible (p.map (Polynomial.C : k →+* k[X])) := by
    apply Polynomial.Monic.irreducible_of_irreducible_map (Polynomial.evalRingHom 0)
      _ (hp.map _)
    have hcomp : (Polynomial.evalRingHom (0 : k)).comp Polynomial.C = RingHom.id k := by
      ext x
      simp
    simpa only [Polynomial.map_map, hcomp, Polynomial.map_id] using hirr
  have hfrac := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc k) (hp.map (Polynomial.C : k →+* k[X]))).mp hpoly
  simpa only [Polynomial.map_map, RatFunc.algebraMap_comp_C] using hfrac

/-- Rational inversion fixes every polynomial whose coefficients are literal constants. -/
theorem Polynomial.map_ratFunc_C_inversion (p : k[X]) :
    (p.map (RatFunc.C : k →+* RatFunc k)).map (RatFunc.inversion k).toRingHom =
      p.map (RatFunc.C : k →+* RatFunc k) := by
  rw [Polynomial.map_map]
  congr 1
  ext a
  exact RatFunc.inversion_C k a

namespace Polynomial.LocalResidue

variable {L : Type*} [Field L] [Algebra k L]

/-- The native rational-function scalar algebra uses the original coefficient map. -/
theorem ratFunc_algebraMap_eq_fractionMap :
    algebraMap (RatFunc k) (RatFunc L) = fractionMap (algebraMap k L) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
    fractionMap_polynomial]
  rfl

end Polynomial.LocalResidue

namespace AdjoinRoot

variable (p : k[X]) [Fact (Irreducible p)]

local instance : Module.Finite k (AdjoinRoot p) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible p).ne_zero).finite

/-- Evaluate the new root at the literal constant rational function of the old root. -/
def rationalCoefficientAlgHom :
    AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k)) →ₐ[RatFunc k]
      RatFunc (AdjoinRoot p) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
    (RatFunc.C (AdjoinRoot.root p)) (by
      change aeval _ (p.map (algebraMap k (RatFunc k))) = 0
      rw [aeval_map_algebraMap]
      exact AdjoinRoot.aeval_algHom_eq_zero p
        (IsScalarTower.toAlgHom k (AdjoinRoot p) (RatFunc (AdjoinRoot p))))

@[simp]
theorem rationalCoefficientAlgHom_root :
    rationalCoefficientAlgHom p (AdjoinRoot.root (p.map RatFunc.C)) =
      RatFunc.C (AdjoinRoot.root p) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Every original root-field element maps to its literal constant rational function. -/
theorem rationalCoefficientAlgHom_coefficientMap (x : AdjoinRoot p) :
    rationalCoefficientAlgHom p (AdjoinRoot.coefficientMap (L := RatFunc k) p x) =
      RatFunc.C x := by
  have h : ((rationalCoefficientAlgHom p).restrictScalars k).comp
      (AdjoinRoot.coefficientMap (L := RatFunc k) p) =
      IsScalarTower.toAlgHom k (AdjoinRoot p) (RatFunc (AdjoinRoot p)) := by
    apply AdjoinRoot.algHom_ext
    change rationalCoefficientAlgHom p
      (AdjoinRoot.coefficientMap (L := RatFunc k) p (AdjoinRoot.root p)) =
        RatFunc.C (AdjoinRoot.root p)
    rw [coefficientMap_root]
    exact rationalCoefficientAlgHom_root p
  exact AlgHom.congr_fun h x

/-- Rational coefficient extension preserves the finite degree of the literal root field. -/
theorem finrank_ratFunc_adjoinRoot :
    Module.finrank (RatFunc k) (RatFunc (AdjoinRoot p)) = p.natDegree := by
  rw [RatFunc.finrank_ratFunc_ratFunc,
    (AdjoinRoot.powerBasis (Fact.out : Irreducible p).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim]

/-- The actual rational coefficient root map is an equivalence, by its finite degree. -/
def rationalCoefficientAlgEquiv (hp : p.Monic) :
    AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k)) ≃ₐ[RatFunc k]
      RatFunc (AdjoinRoot p) := by
  let : Fact (Irreducible (p.map (RatFunc.C : k →+* RatFunc k))) :=
    ⟨hp.irreducible_map_ratFunc_C Fact.out⟩
  let : Module.Finite (RatFunc k) (AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k))) :=
    (hp.map _).finite_adjoinRoot
  have : Module.Finite (RatFunc k) (RatFunc (AdjoinRoot p)) :=
    FiniteDimensional.of_finrank_pos (by
      rw [RatFunc.finrank_ratFunc_ratFunc]
      exact Module.finrank_pos)
  let f := rationalCoefficientAlgHom p
  apply AlgEquiv.ofBijective f
  refine ⟨f.injective, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) ?_).mp f.injective
  rw [(AdjoinRoot.powerBasis (hp.irreducible_map_ratFunc_C Fact.out).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, Polynomial.natDegree_map,
    finrank_ratFunc_adjoinRoot]

@[simp]
theorem rationalCoefficientAlgEquiv_root (hp : p.Monic) :
    rationalCoefficientAlgEquiv p hp (AdjoinRoot.root (p.map RatFunc.C)) =
      RatFunc.C (AdjoinRoot.root p) :=
  rationalCoefficientAlgHom_root p

/-- The equivalence retains the original coefficient map on every old field element. -/
theorem rationalCoefficientAlgEquiv_coefficientMap (hp : p.Monic) (x : AdjoinRoot p) :
    rationalCoefficientAlgEquiv p hp
      (AdjoinRoot.coefficientMap (L := RatFunc k) p x) = RatFunc.C x :=
  rationalCoefficientAlgHom_coefficientMap p x

/-- The base-field square is the original rational coefficient extension. -/
theorem rationalCoefficientAlgEquiv_algebraMap (hp : p.Monic) (x : RatFunc k) :
    rationalCoefficientAlgEquiv p hp
      (algebraMap (RatFunc k) (AdjoinRoot (p.map RatFunc.C)) x) =
      Polynomial.LocalResidue.fractionMap (algebraMap k (AdjoinRoot p)) x := by
  rw [AlgEquiv.commutes, Polynomial.LocalResidue.ratFunc_algebraMap_eq_fractionMap]

/-- The literal quotient map induced by coefficient inversion becomes rational inversion. -/
theorem rationalCoefficientAlgEquiv_comp_inversion (hp : p.Monic) :
    letI : Fact (Irreducible (p.map (RatFunc.C : k →+* RatFunc k))) :=
      ⟨hp.irreducible_map_ratFunc_C Fact.out⟩
    (rationalCoefficientAlgEquiv p hp).toRingHom.comp
        (Polynomial.LocalResidue.adjoinRootMap (RatFunc.inversion k).toRingHom
          (p.map RatFunc.C) (p.map RatFunc.C) (by rw [Polynomial.map_ratFunc_C_inversion])) =
      (RatFunc.inversion (AdjoinRoot p)).toRingHom.comp
        (rationalCoefficientAlgEquiv p hp).toRingHom := by
  let : Fact (Irreducible (p.map (RatFunc.C : k →+* RatFunc k))) :=
    ⟨hp.irreducible_map_ratFunc_C Fact.out⟩
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro x
    change rationalCoefficientAlgEquiv p hp
      (Polynomial.LocalResidue.adjoinRootMap (RatFunc.inversion k).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C) _
        (algebraMap (RatFunc k) (AdjoinRoot (p.map RatFunc.C)) x)) =
      RatFunc.inversion (AdjoinRoot p) (rationalCoefficientAlgEquiv p hp
        (algebraMap (RatFunc k) (AdjoinRoot (p.map RatFunc.C)) x))
    rw [Polynomial.LocalResidue.adjoinRootMap_algebraMap,
      rationalCoefficientAlgEquiv_algebraMap, rationalCoefficientAlgEquiv_algebraMap]
    exact Polynomial.LocalResidue.fractionMap_inversion _ x
  · change rationalCoefficientAlgEquiv p hp
      (Polynomial.LocalResidue.adjoinRootMap (RatFunc.inversion k).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C) _ (AdjoinRoot.root (p.map RatFunc.C))) =
      RatFunc.inversion (AdjoinRoot p)
        (rationalCoefficientAlgEquiv p hp (AdjoinRoot.root (p.map RatFunc.C)))
    rw [Polynomial.LocalResidue.adjoinRootMap_root, rationalCoefficientAlgEquiv_root,
      RatFunc.inversion_C]

end AdjoinRoot
