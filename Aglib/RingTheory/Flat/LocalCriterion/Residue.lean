/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.LocalCriterion.Adic
public import Aglib.RingTheory.Flat.LocalCriterion.ResidueSyzygies

/-!
# Residue-fibre injectivity and flatness of an actual cokernel or ideal quotient

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 482–636.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Module.Flat
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

section BaseChangeSource
variable (I : Ideal R)
local notation "A" => R ⧸ I
local notation "B" => A ⊗[R] S
local notation "M₀" => A ⊗[R] M
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The right-factor module action on the quotient-base tensor product. -/
local instance (priority := low) tensorQuotientRightModule : Module S M₀ :=
  ResidueSyzygies.tensorRightModule (R := R) (S := S) (M := M) A

lemma right_smul_tmul (s : S) (a : A) (m : M) :
    s • (a ⊗ₜ[R] m : M₀) = a ⊗ₜ[R] (s • m) := rfl

local instance : IsScalarTower R S M₀ where
  smul_assoc r s x := by
    induction x with
    | tmul a m =>
      simp only [right_smul_tmul, smul_tmul', smul_assoc]
      exact (smul_tmul r a (s • m)).symm
    | add x y hx hy => simp_all [smul_add]

local instance : SMulCommClass A S M₀ where
  smul_comm a s x := by
    induction x with
    | tmul b m => simp only [right_smul_tmul, smul_tmul']
    | add x y hx hy => simp_all [smul_add]

local instance : IsScalarTower R A M₀ := TensorProduct.isScalarTower_left

/-- The tensor-product algebra action on the quotient-base tensor product. -/
local instance tensorQuotientAlgebraModule : Module B M₀ := TensorProduct.Algebra.module

lemma baseChange_smul (a : A) (s : S) (m : M₀) :
    (a ⊗ₜ[R] s : B) • m = a • s • m := rfl

local instance : IsScalarTower A B M₀ where
  smul_assoc a b m := by
    induction b with
    | tmul c s =>
      rw [smul_tmul', baseChange_smul, baseChange_smul, smul_assoc]
    | add b c hb hc => simp_all [add_smul, smul_add]

local instance : IsScalarTower S B M₀ where
  smul_assoc s b m := by
    induction b with
    | tmul a t =>
      change (((1 : A) ⊗ₜ[R] s) * (a ⊗ₜ[R] t)) • m = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, baseChange_smul, baseChange_smul,
        mul_smul, smul_comm a s]
    | add b c hb hc =>
      change (((1 : A) ⊗ₜ[R] s) * (b + c)) • m = _
      rw [mul_add, add_smul, add_smul, smul_add]
      exact congrArg₂ (· + ·) hb hc

theorem cyclicBaseChange_source_finite [Module.Finite S M] : Module.Finite B M₀ := by
  let j : M →ₗ[S] M₀ :=
    { toFun := fun m ↦ (1 : A) ⊗ₜ[R] m
      map_add' := by intro x y; exact tmul_add _ _ _
      map_smul' := by intro s m; rfl }
  have hj : Function.Surjective j := by
    intro x
    obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective M (I.mkQ_surjective) x
    obtain ⟨m, rfl⟩ := (TensorProduct.lid R M).symm.surjective y
    exact ⟨m, rfl⟩
  have : Module.Finite S M₀ := Module.Finite.of_surjective j hj
  exact Module.Finite.of_restrictScalars_finite S B M₀

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- Residue injectivity lifts through every proper cyclic base change. -/
theorem lTensor_quotient_injective_of_residue_injective_noetherian
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing S] [Module.Finite S M] [Module.Flat R N]
    (hI : I ≠ ⊤) (f : M →ₗ[R] N)
    (hf : Function.Injective (f.lTensor (R ⧸ IsLocalRing.maximalIdeal R))) :
    Function.Injective (f.lTensor A) := by
  let K := R ⧸ IsLocalRing.maximalIdeal R
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  have hIle : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  let : Algebra A K := (Ideal.Quotient.factor hIle).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq (fun r ↦ rfl)
  have hK : Function.Surjective (algebraMap A K) := Ideal.Quotient.factor_surjective hIle
  have : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing A := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hIS : I.map (algebraMap R S) ≠ ⊤ := ne_of_lt
    ((Ideal.map_mono hIle).trans_lt (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)))
  have : Nontrivial (S ⧸ I.map (algebraMap R S)) := Ideal.Quotient.nontrivial_iff.mpr hIS
  have : Nontrivial B :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toEquiv.nontrivial
  let j : S →ₐ[R] B := Algebra.TensorProduct.includeRight
  have hj : Function.Surjective j :=
    Algebra.TensorProduct.includeRight_surjective S (Ideal.Quotient.mk_surjective (I := I))
  have : IsNoetherianRing B := isNoetherianRing_of_surjective S B j.toRingHom hj
  have : IsLocalRing B := IsLocalRing.of_surjective' j.toRingHom hj
  have : IsLocalHom j.toRingHom := IsLocalHom.of_surjective j.toRingHom hj
  have : IsLocalHom (algebraMap A B) := by
    constructor
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply IsUnit.map (Ideal.Quotient.mk I)
    apply (isUnit_map_iff (algebraMap R S) r).mp
    apply (isUnit_map_iff j.toRingHom (algebraMap R S r)).mp
    have he : j (algebraMap R S r) = algebraMap A B (Ideal.Quotient.mk I r) :=
      (j.commutes r).trans (IsScalarTower.algebraMap_apply R A B r)
    change IsUnit (j (algebraMap R S r))
    rwa [he]
  have : Module.Finite B M₀ := cyclicBaseChange_source_finite (S := S) (M := M) I
  have hfa : Function.Injective ((f.baseChange A).lTensor K) := by
    let eM := AlgebraTensorModule.cancelBaseChange R A K K M
    let eN := AlgebraTensorModule.cancelBaseChange R A K K N
    have hc := AlgebraTensorModule.lTensor_comp_cancelBaseChange R A K (M := K) f
    intro x y hxy
    apply eM.injective
    apply hf
    exact (LinearMap.congr_fun hc x).trans
      ((congrArg eN hxy).trans (LinearMap.congr_fun hc y).symm)
  exact injective_of_field_fibre_injective_of_noetherian B K hK (f.baseChange A) hfa

end BaseChangeSource

variable {N Q : Type*} [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q]

/-- The full local cokernel-flatness criterion with a Noetherian algebra acting
finitely on the source. The target module need only be flat over the local base. -/
theorem injective_and_flat_of_residue_injective_noetherian
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing S] [Module.Finite S M] [Module.Flat R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] Q) (hex : Function.Exact f g)
    (hg : Function.Surjective g)
    (hf : Function.Injective (f.lTensor (R ⧸ IsLocalRing.maximalIdeal R))) :
    Function.Injective f ∧ Module.Flat R Q := by
  apply (injective_and_flat_iff_lTensor_quotient_injective f g hex hg).mpr
  intro I
  by_cases hI : I = ⊤
  · subst I
    intro x y _
    exact Subsingleton.elim _ _
  exact lTensor_quotient_injective_of_residue_injective_noetherian
    (S := S) I hI f hf


/-- The local flatness criterion for the actual quotient by an ideal. -/
theorem flat_quotient_of_residue_subtype_injective_noetherian
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing S] [Module.Flat R S] (J : Ideal S)
    (hf : Function.Injective ((J.subtype.restrictScalars R).lTensor
      (R ⧸ IsLocalRing.maximalIdeal R))) : Module.Flat R (S ⧸ J) :=
  (injective_and_flat_of_residue_injective_noetherian (S := S)
    (J.subtype.restrictScalars R) (Ideal.Quotient.mkₐ R J).toLinearMap
    (LinearMap.exact_subtype_mkQ J) (Ideal.Quotient.mk_surjective) hf).2

end Module.Flat
