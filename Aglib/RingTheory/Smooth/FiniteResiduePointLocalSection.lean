/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalRing.FiniteFreeResidueLift
public import Aglib.RingTheory.Smooth.RationalPointEtaleLocal
public import Mathlib.RingTheory.Unramified.LocalRing

/-! # An actual local section through a finite residue point

The finite-free residue lift first rationalizes the original point on the
original tensor base change. Its canonical residue-field comparison is kept,
including its value on every original residue class. The rational-point
etale-local construction then supplies a section. The final local base is
flat and essentially of finite type, with the literal extended maximal ideal.
The composite coefficient map is not asserted etale: the original finite
residue extension can be inseparable.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v

namespace Algebra.Smooth.FiniteResiduePointLocalSection

section ResidueComparison

variable (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  (L : Type v) [Field L] [Algebra (ResidueField R) L]
  [Algebra R L] [IsScalarTower R (ResidueField R) L]
  (hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
  (e : ResidueField R ⊗[R] S ≃ₐ[ResidueField R] L)

/-- The original residue tensor comparison identifies the actual residue
field of the same lifted ring, using only the literal maximal-ideal equality. -/
def residueFieldEquiv : ResidueField S ≃ₐ[ResidueField R] L := by
  let eR : ResidueField S ≃ₐ[R] L :=
    (Ideal.quotientEquivAlgOfEq R hm.symm).trans
      (((Algebra.TensorProduct.quotIdealMapEquivQuotTensor S
        (maximalIdeal R)).restrictScalars R).trans (e.restrictScalars R))
  exact { eR.toRingEquiv with
    commutes' := fun r => by
      obtain ⟨r, rfl⟩ := residue_surjective r
      rw [ResidueField.algebraMap_residue]
      change eR (algebraMap R (ResidueField S) r) =
        algebraMap (ResidueField R) L (algebraMap R (ResidueField R) r)
      rw [eR.commutes, ← IsScalarTower.algebraMap_apply] }

/-- The residue comparison retains precisely the original tensor coefficient
map on every original element of S. -/
theorem residueFieldEquiv_residue (s : S) :
    residueFieldEquiv R S L hm e (residue S s) = e (1 ⊗ₜ[R] s) := by
  change e ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R))
    ((Ideal.quotientEquivAlgOfEq R hm.symm)
      (Ideal.Quotient.mk (maximalIdeal S) s))) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  rfl

end ResidueComparison

/-- A finite residue point of a smooth algebra lifts to one actual flat local
base with unchanged puncture preimage. The given residue map is recovered by
the displayed algebra-map composition. No separability or normality premise
is introduced, and the total map is not asserted etale. -/
theorem exists_local_section
    (R B : Type u) [CommRing R] [CommRing B] [IsLocalRing R]
    [Algebra R B] [Algebra.Smooth R B]
    (L : Type v) [Field L] [Algebra (ResidueField R) L]
    [Algebra R L] [IsScalarTower R (ResidueField R) L]
    [FiniteDimensional (ResidueField R) L] (ψ : B →ₐ[R] L) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : IsLocalRing T),
      Module.Flat R T ∧ Algebra.EssFiniteType R T ∧ IsLocalHom (algebraMap R T) ∧
        (maximalIdeal R).map (algebraMap R T) = maximalIdeal T ∧
          ∃ (ε : B →ₐ[R] T) (l : T →ₐ[R] L),
            Function.Surjective l ∧ IsLocalHom l.toRingHom ∧ l.comp ε = ψ := by
  obtain ⟨S, hS, hRS, hlocalS, hfin, hfree, hlocalRS, hmRS, ⟨e⟩⟩ :=
    IsLocalRing.exists_finite_free_local_residue_lift R L
  let : CommRing S := hS
  let : Algebra R S := hRS
  let : IsLocalRing S := hlocalS
  let : Module.Finite R S := hfin
  let : Module.Free R S := hfree
  let : IsLocalHom (algebraMap R S) := hlocalRS
  let eκ := residueFieldEquiv R S L hmRS e
  let ψκ : B →ₐ[R] ResidueField S := (eκ.symm.restrictScalars R).toAlgHom.comp ψ
  let B₁ := S ⊗[R] B
  let ψ₁ : B₁ →ₐ[S] ResidueField S :=
    Algebra.TensorProduct.lift (Algebra.ofId S (ResidueField S)) ψκ
      (fun _ _ => .all _ _)
  have hψ₁ (b : B) : eκ (ψ₁ (1 ⊗ₜ[R] b)) = ψ b := by
    have h : ψ₁ (1 ⊗ₜ[R] b) = ψκ b := by
      exact (Algebra.TensorProduct.lift_tmul (Algebra.ofId S (ResidueField S))
        ψκ (fun _ _ => .all _ _) 1 b).trans (by rw [map_one, one_mul])
    rw [h]
    exact eκ.apply_symm_apply (ψ b)
  obtain ⟨T, hT, hST, hlocalT, het, hft, hflatST, hlocalST, ε₁, l₁,
      hsurj₁, hlocal₁, hcomp₁⟩ :=
    RationalPointEtaleLocal.exists_local_lift S B₁ ψ₁
  let : CommRing T := hT
  let : Algebra S T := hST
  let : IsLocalRing T := hlocalT
  let : Algebra R T := Algebra.restrictScalars R S T
  let : IsScalarTower R S T := .of_algebraMap_eq' rfl
  let : Algebra.FormallyEtale S T := het
  let : Algebra.EssFiniteType S T := hft
  let : Module.Flat S T := hflatST
  let : IsLocalHom (algebraMap S T) := hlocalST
  let : IsLocalHom l₁.toRingHom := hlocal₁
  have hflatRT : Module.Flat R T := Module.Flat.trans R S T
  have hftRT : Algebra.EssFiniteType R T := Algebra.EssFiniteType.comp R S T
  have hlocalRT : IsLocalHom (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R S T]
    infer_instance
  have hmST : (maximalIdeal S).map (algebraMap S T) = maximalIdeal T :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hmRT : (maximalIdeal R).map (algebraMap R T) = maximalIdeal T := by
    rw [IsScalarTower.algebraMap_eq R S T, ← Ideal.map_map, hmRS, hmST]
  let ε : B →ₐ[R] T := (ε₁.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[R] B₁)
  let l : T →ₐ[R] L := (eκ.restrictScalars R).toAlgHom.comp (l₁.restrictScalars R)
  have hsurj : Function.Surjective l := eκ.surjective.comp hsurj₁
  have hlocal : IsLocalHom l.toRingHom := by
    change IsLocalHom (eκ.toRingHom.comp l₁.toRingHom)
    infer_instance
  have hcomp : l.comp ε = ψ := by
    ext b
    change eκ (l₁ (ε₁ (1 ⊗ₜ[R] b))) = ψ b
    rw [show l₁ (ε₁ (1 ⊗ₜ[R] b)) = ψ₁ (1 ⊗ₜ[R] b) from
      DFunLike.congr_fun hcomp₁ (1 ⊗ₜ[R] b)]
    exact hψ₁ b
  exact ⟨T, inferInstance, inferInstance, inferInstance, hflatRT, hftRT,
    hlocalRT, hmRT, ε, l, hsurj, hlocal, hcomp⟩

end Algebra.Smooth.FiniteResiduePointLocalSection
