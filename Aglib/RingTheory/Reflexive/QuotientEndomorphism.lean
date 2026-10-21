/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dual.Defs

/-! Actual endomorphism reduction modulo a scalar and its double-dual action. -/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace QuotSMulTop

variable {R : Type*} [CommRing R] (a : R) (M : Type*) [AddCommGroup M] [Module R M]

/-- The original endomorphism acts on the actual quotient, over the quotient ring. -/
def endomorphismReduction : Module.End R M →ₗ[R]
    Module.End (R ⧸ Ideal.span {a}) (QuotSMulTop a M) :=
  (LinearMap.extendScalarsOfSurjectiveEquiv Ideal.Quotient.mk_surjective).toLinearMap.comp
    (QuotSMulTop.map a)

@[simp]
theorem endomorphismReduction_apply_mk (f : Module.End R M) (x : M) :
    endomorphismReduction a M f (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f x) : QuotSMulTop a M) := rfl

/-- Scalar multiples act trivially on the corresponding quotient. -/
theorem smul_top_le_ker_endomorphismReduction :
    a • (⊤ : Submodule R (Module.End R M)) ≤ (endomorphismReduction a M).ker := by
  intro f hf
  obtain ⟨g, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hf
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.smul_mem_pointwise_smul (g x) a ⊤ trivial)

/-- A regular scalar divides an endomorphism precisely when its quotient action is zero. -/
theorem ker_endomorphismReduction (ha : IsSMulRegular M a) :
    (endomorphismReduction a M).ker = a • (⊤ : Submodule R (Module.End R M)) := by
  apply le_antisymm _ (smul_top_le_ker_endomorphismReduction a M)
  intro f hf
  let i : M →ₗ[R] M := a • LinearMap.id
  have hi : Function.Injective i := ha
  have hmem (x : M) : f x ∈ i.range := by
    have hz := DFunLike.congr_fun hf (Submodule.Quotient.mk x : QuotSMulTop a M)
    have hx : f x ∈ a • (⊤ : Submodule R M) :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact ⟨y, hy⟩
  let g := f.codRestrictOfInjective i hi hmem
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨g, trivial, ?_⟩
  ext x
  exact LinearMap.codRestrictOfInjective_comp_apply f i hi hmem x

/-- Endomorphism reduction factors through the actual quotient of the endomorphism module. -/
def quotientEndomorphism : QuotSMulTop a (Module.End R M) →ₗ[R ⧸ Ideal.span {a}]
    Module.End (R ⧸ Ideal.span {a}) (QuotSMulTop a M) :=
  ((a • (⊤ : Submodule R (Module.End R M))).liftQ (endomorphismReduction a M)
    (smul_top_le_ker_endomorphismReduction a M)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective

@[simp]
theorem quotientEndomorphism_apply_mk (f : Module.End R M) :
    quotientEndomorphism a M (Submodule.Quotient.mk f) = endomorphismReduction a M f := rfl

/-- Reduction of endomorphisms is injective after quotienting by a regular scalar. -/
theorem quotientEndomorphism_injective (ha : IsSMulRegular M a) :
    Function.Injective (quotientEndomorphism a M) := by
  change Function.Injective ((a • (⊤ : Submodule R (Module.End R M))).liftQ
    (endomorphismReduction a M) (smul_top_le_ker_endomorphismReduction a M))
  apply (LinearMap.ker_eq_bot).mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_endomorphismReduction a M ha).le

/-- Every endomorphism of the quotient lifts when the original module is projective. -/
theorem quotientEndomorphism_surjective [Module.Projective R M] :
    Function.Surjective (quotientEndomorphism a M) := by
  intro g
  let q : M →ₗ[R] QuotSMulTop a M := (a • (⊤ : Submodule R M)).mkQ
  obtain ⟨f, hf⟩ := Module.projective_lifting_property q ((g.restrictScalars R).comp q)
    (Submodule.mkQ_surjective _)
  refine ⟨(Submodule.Quotient.mk f : QuotSMulTop a (Module.End R M)), ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change q (f x) = g (q x)
  exact DFunLike.congr_fun hf x

/-- The canonical action of the endomorphism quotient on the actual bidual of `M/aM`. -/
def quotientEndomorphismDoubleDual : QuotSMulTop a (Module.End R M) →ₗ[R ⧸ Ideal.span {a}]
    Module.End (R ⧸ Ideal.span {a})
      (Module.Dual (R ⧸ Ideal.span {a}) (Module.Dual (R ⧸ Ideal.span {a}) (QuotSMulTop a M))) :=
  (Module.Dual.transpose.comp Module.Dual.transpose).comp (quotientEndomorphism a M)

/-- The action on the bidual extends the original quotient action through evaluation. -/
@[simp]
theorem quotientEndomorphismDoubleDual_eval (f : QuotSMulTop a (Module.End R M))
    (x : QuotSMulTop a M) :
    quotientEndomorphismDoubleDual a M f
      (Module.Dual.eval (R ⧸ Ideal.span {a}) (QuotSMulTop a M) x) =
    Module.Dual.eval (R ⧸ Ideal.span {a}) (QuotSMulTop a M)
      (quotientEndomorphism a M f x) := rfl

end QuotSMulTop
