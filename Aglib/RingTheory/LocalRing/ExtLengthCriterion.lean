/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Tensor.ExtOneCoefficient
public import Aglib.RingTheory.FiniteLength.EulerObstruction
public import Aglib.RingTheory.FiniteLength.TensorInjectivity
public import Aglib.RingTheory.LocalRing.ExtCriterion

/-!
# A local freeness criterion from degree-one Ext lengths

For an actual finite-free length-one resolution, a finite-length first Ext
module and the stated numerical upper bound force freeness. If this Ext
module is zero, dual splitting applies. Otherwise the Euler identity forces
tensor injectivity, and its residue-field socle detects freeness. The basis
cardinality relation is explicit and is not inferred from an unstated rank
or endomorphism hypothesis.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

namespace ModuleCat

/-- The finite-length Ext obstruction for an actual finite-free resolution
over a Noetherian local ring. -/
theorem free_of_ext_length_le
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    {ι₁ : Type*} {ι₀ : Type*} [Fintype ι₁] [Fintype ι₀]
    (b₁ : Module.Basis ι₁ R S.X₁) (b₀ : Module.Basis ι₀ R S.X₂)
    (hC : IsFiniteLength R (Ext S.X₃ (ModuleCat.of R R) 1))
    (r : ℕ) (hr : Fintype.card ι₀ = Fintype.card ι₁ + r)
    (hlen : Module.length R (Ext S.X₃ S.X₃ 1) ≤
      r * Module.length R (Ext S.X₃ (ModuleCat.of R R) 1)) :
    Module.Free R S.X₃ := by
  have : Module.Free R S.X₁ := Module.Free.of_basis b₁
  have : Module.Finite R S.X₁ := Module.Finite.of_basis b₁
  have : Module.Free R S.X₂ := Module.Free.of_basis b₀
  have : Module.Finite R S.X₂ := Module.Finite.of_basis b₀
  have : Module.Finite R S.X₃ :=
    Module.Finite.of_surjective S.g.hom hS.moduleCat_surjective_g
  have hex : Function.Exact S.f.hom S.g.hom := by
    rw [LinearMap.exact_iff]
    exact hS.exact.moduleCat_range_eq_ker.symm
  let C := Ext S.X₃ (ModuleCat.of R R) 1
  rcases subsingleton_or_nontrivial C with hzero | hnonzero
  · have : Subsingleton C := hzero
    have hpd : projectiveDimension S.X₃ ≤ 1 := by
      apply (projectiveDimension_le_iff _ _).mpr
      exact hS.hasProjectiveDimensionLT_X₃ 1 inferInstance
        (hasProjectiveDimensionLT_of_ge S.X₂ 1 2 (by omega))
    exact free_of_projectiveDimension_le_one_of_subsingleton_ext R S.X₃ hpd
  · have : Nontrivial C := hnonzero
    have : IsArtinian R C := (isFiniteLength_iff_isNoetherian_isArtinian.mp hC).2
    have hlength : Module.length R (C ⊗[R] S.X₃) ≤ r * Module.length R C := by
      rw [(extOneTensorCoefficientLinearEquiv S.X₃ hS).length_eq]
      exact hlen
    have hinj : Function.Injective (S.f.hom.lTensor C) :=
      TensorProduct.injective_lTensor_of_length_le b₁ b₀ S.f.hom S.g.hom
        hS.moduleCat_surjective_g hex hC r hr hlength
    exact IsArtinian.free_of_lTensor_injective S.f.hom S.g.hom
      hS.moduleCat_surjective_g hex hinj

end ModuleCat
