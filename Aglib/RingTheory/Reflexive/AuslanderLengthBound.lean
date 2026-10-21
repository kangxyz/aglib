/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Ext.FinitePi
public import Aglib.Algebra.Category.ModuleCat.Tensor.ExtOne
public import Aglib.LinearAlgebra.TensorProduct.DualInjectivity
public import Aglib.RingTheory.LocalRing.ProjectiveDimension
public import Aglib.RingTheory.Reflexive.ProjectiveDimension
public import Aglib.RingTheory.RegularLocalRing.FiniteLengthExtComparison
public import Mathlib.RingTheory.Length

/-!
# The dimension-three self-Ext length bound

This is the numerical upper bound in the dimension-three Auslander argument,
not the freeness conclusion. Its finite-defect map from `M ⊗ M*` to `End(M)`
is an actual supplied linear map with explicit finite-length kernel and cokernel.
For the canonical evaluation map these premises are discharged separately by
punctured freeness and localization. No global Hom base-change is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

namespace ModuleCat

/-- In dimension three, a finite reflexive module with the stated actual
finite-defect endomorphism map satisfies the self-Ext length upper bound.
This statement alone does not assert freeness. -/
theorem length_ext_self_le_of_endomorphism_equiv
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R = 3) (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (eEnd : Module.End R M ≃ₗ[R] (Fin r → M))
    (e : M ⊗[R] Module.Dual R M →ₗ[R] Module.End R M)
    (hker : IsFiniteLength R (LinearMap.ker e))
    (hcoker : IsFiniteLength R (Module.End R M ⧸ LinearMap.range e)) :
    Module.length R (Ext M M 1) ≤ r * Module.length R (Ext M (ModuleCat.of R R) 1) := by
  have hpd : projectiveDimension M ≤ 1 :=
    Module.projectiveDimension_le_of_isReflexive R 1 (by simp [hd]) M
  obtain ⟨P₁, P₀, _, _, _, _, _, _, _, _, f, g, hf, hg, hex⟩ :=
    exists_finite_free_shortExact_of_projectiveDimension_le_one R M hpd
  let S := ModuleCat.shortComplexOfCompEqZero f g hex.linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hex hf hg
  have htf : Function.Injective (f.rTensor (Module.Dual R M)) :=
    LinearMap.rTensor_dual_injective_of_flat M f hf
  let ev := Ext.postcompLinearEquiv R (Module.evalEquiv R M).toModuleIso M 1
  let j : Ext M M 1 →ₗ[R]
      Ext (ModuleCat.of R (M ⊗[R] Module.Dual R M)) (ModuleCat.of R R) 1 :=
    (ModuleCat.extOneDualTensorLinearMap (Module.Dual R M) hS htf).comp ev.toLinearMap
  have hj : Function.Injective j :=
    (ModuleCat.extOneDualTensorLinearMap_injective (Module.Dual R M) hS htf).comp
      ev.injective
  let ed := IsRegularLocalRing.extOneLinearEquivOfIsFiniteLength R
    (ModuleCat.ofHom e) hker hcoker 3 hd le_rfl
  let ee := Ext.precompLinearEquiv R eEnd.toModuleIso.symm (ModuleCat.of R R) 1
  let k : Ext M M 1 →ₗ[R]
      Ext (ModuleCat.of R (Fin r → M)) (ModuleCat.of R R) 1 :=
    ee.toLinearMap.comp (ed.symm.toLinearMap.comp j)
  have hk : Function.Injective k := ee.injective.comp (ed.symm.injective.comp hj)
  calc
    Module.length R (Ext M M 1) ≤
        Module.length R (Ext (ModuleCat.of R (Fin r → M)) (ModuleCat.of R R) 1) :=
      Module.length_le_of_injective k hk
    _ = r * Module.length R (Ext M (ModuleCat.of R R) 1) :=
      ModuleCat.length_ext_finPi R M (ModuleCat.of R R) r 1

end ModuleCat
