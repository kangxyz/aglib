/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Polynomial relations, dimension and projectivity


Source: `R5Lab.Aglib.RingTheory.Polynomial.GraphRelations`.
Packet SHA-256:
`799526c9a2641879f352e659e836feb6a5232f9551ce72071a76aca908d3f76d`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
universe u v
namespace Polynomial

/-- A nonzero relation on a polynomial chart over a noetherian integral curve
bounds the dimension of the corresponding quotient chart by one. -/
theorem graphChart_ringKrullDim_le_one
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {B : Type v} [CommRing B]
    (f : A[X] →+* B) (hf : Function.Surjective f)
    (hA : ringKrullDim A ≤ 1)
    {r : A[X]} (hr : r ≠ 0) (hfr : f r = 0) :
    ringKrullDim B ≤ 1 := by
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  calc
    ringKrullDim B + 1 ≤ ringKrullDim A[X] :=
      ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_iff_ne_zero.mpr hr) hfr
    _ = ringKrullDim A + 1 := Polynomial.ringKrullDim_of_isNoetherianRing
    _ ≤ 1 + 1 := by simpa only [add_comm] using add_le_add_right hA 1

/-- The cleared-denominator equation of a rational-function graph is nonzero. -/
theorem graphChart_relation_ne_zero
    {A : Type u} [CommRing A] {b c : A} (hb : b ≠ 0) :
    C b * X - C c ≠ 0 := by
  intro h
  apply hb
  simpa using congrArg (fun p : A[X] => p.coeff 1) h
/-- A finite integral-domain algebra with faithful polynomial coordinates is
projective over the polynomial chart, with its given algebra scalar action. -/
theorem finitePolynomialAlgebra_projective
    {K : Type u} [Field K] {B : Type v} [CommRing B] [IsDomain B]
    [Algebra K[X] B] [Module.Finite K[X] B]
    (h : Function.Injective (algebraMap K[X] B)) : Module.Projective K[X] B := by
  let : Module.IsTorsionFree K[X] B := Module.isTorsionFree_iff_algebraMap_injective.mpr h
  infer_instance

lemma exists_polynomial_relation_of_fractionRing
    {A B F : Type u} [CommRing A] [IsDomain A] [CommRing B] [Field F]
    [Algebra A F] [IsFractionRing A F]
    (f : A[X] →+* B) (E : B →+* F) (hE : Function.Injective E)
    (hc : ∀ a : A, E (f (C a)) = algebraMap A F a) :
    ∃ r : A[X], r ≠ 0 ∧ f r = 0 := by
  obtain ⟨⟨a,b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) (E (f X))
  refine ⟨C b.val * X - C a, graphChart_relation_ne_zero
    (mem_nonZeroDivisors_iff_ne_zero.mp b.property), ?_⟩
  apply hE
  simp only [map_sub, map_mul, map_zero, hc]
  exact sub_eq_zero.mpr ((mul_comm _ _).trans hab)


end Polynomial
