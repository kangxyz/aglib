/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.LocalCriterion.Adic
public import Aglib.RingTheory.Flat.PrincipalQuotient.BaseChange

/-!
# Noetherian local-target residue criterion for regular equations and flat principal quotients

## Extraction basis

Transferred from `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`
at frozen dirty R5Lab revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
Source line ranges: 410–480.
The original rings, modules, canonical maps, universes and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open TensorProduct LinearMap

namespace Algebra
open TensorProduct LinearMap Module.Flat
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing S] [Module.Flat R S]

/-- The local regular-element criterion of Stacks 00MF. Only the Noetherian
local target is an explicit premise; flat locality already forces the base
to be Noetherian. The conclusion uses the actual principal-ideal quotient. -/
theorem regular_and_flat_of_residue_regular_noetherian (a : S)
    (ha : Function.Injective ((LinearMap.mulLeft R a).lTensor
      (R ⧸ IsLocalRing.maximalIdeal R))) :
    IsSMulRegular S a ∧ Module.Flat R (S ⧸ Ideal.span {a}) := by
  apply (regular_and_flat_principal_quotient_iff a).mpr
  intro I
  by_cases hI : I = ⊤
  · subst I
    intro x y _
    exact Subsingleton.elim _ _
  let A := R ⧸ I
  let B := A ⊗[R] S
  let K := R ⧸ IsLocalRing.maximalIdeal R
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  have hIle : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  let : Algebra A K := (Ideal.Quotient.factor hIle).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq (fun r ↦ rfl)
  have hK : Function.Surjective (algebraMap A K) := Ideal.Quotient.factor_surjective hIle
  have : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing A := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Nontrivial B :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left
      (R := R) (M := A) (N := S)).mpr inferInstance
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
  let aI : B := (1 : A) ⊗ₜ[R] a
  have hreg : IsSMulRegular (K ⊗[R] S) ((1 : K) ⊗ₜ[R] a) := by
    change Function.Injective (LinearMap.mulLeft R ((1 : K) ⊗ₜ[R] a))
    rwa [← lTensor_mulLeft K a]
  let e := Algebra.TensorProduct.cancelBaseChange R A K K S
  have he : IsSMulRegular (K ⊗[A] B) ((1 : K) ⊗ₜ[A] aI) ↔
      IsSMulRegular (K ⊗[R] S) ((1 : K) ⊗ₜ[R] a) :=
    Equiv.isSMulRegular_congr (e := e.toEquiv) fun x ↦ by
      change e (_ * x) = _ * e x
      rw [map_mul]
      change ((((1 : A) • (1 : K)) ⊗ₜ[R] a) * e x) = _
      rw [one_smul]
  have hfa : Function.Injective ((LinearMap.mulLeft A aI).lTensor K) := by
    rw [lTensor_mulLeft]
    exact he.mpr hreg
  have hma : Function.Injective (LinearMap.mulLeft A aI) :=
    injective_of_field_fibre_injective_of_noetherian B K hK (LinearMap.mulLeft A aI) hfa
  rw [lTensor_mulLeft]
  exact hma

end Algebra
