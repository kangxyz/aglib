/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.Inertia.Compactness
public import Aglib.RingTheory.IntegralClosure.Inertia.Finite

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.Inertia.Absolute`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`f381c6fa16e08ac749689b2961eb38997ff1de89bb0b847f47c68c0b66fb494a`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace integralClosure.Inertia.AbsoluteRestriction

open FiniteRestriction

variable (R K Ω : Type*) [CommRing R] [Field K] [Field Ω]
  [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω]

instance subfieldAmbientTower (L : FiniteGaloisIntermediateField K Ω) : IsScalarTower R L Ω :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The same chosen prime, contracted to a finite Galois subextension. -/
def contractedPrime (Q : Ideal (integralClosure R Ω))
    (L : FiniteGaloisIntermediateField K Ω) : Ideal (integralClosure R L) :=
  Q.comap (modelMap R L Ω)

instance contractedPrimeIsPrime (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    (L : FiniteGaloisIntermediateField K Ω) : (contractedPrime R K Ω Q L).IsPrime :=
  Ideal.comap_isPrime _ Q

/-- Every finite collection of literal residue conditions has an absolute
Galois lift with the prescribed finite inertia restriction. -/
theorem finite_conditions (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    (L : FiniteGaloisIntermediateField K Ω) (τ : L ≃ₐ[K] L)
    (hτ : τ ∈ (contractedPrime R K Ω Q L).inertia (L ≃ₐ[K] L))
    (s : Finset (integralClosure R Ω)) :
    ∃ σ : Ω ≃ₐ[K] Ω, AlgEquiv.restrictNormalHom L σ = τ ∧
      ∀ x ∈ s, σ • x - x ∈ Q := by
  classical
  let M := (s.sup fun x => FiniteGaloisIntermediateField.adjoin K {(x : Ω)}) ⊔ L
  have hLM : L ≤ M := le_sup_right
  letI : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq' rfl
  let QM := contractedPrime R K Ω Q M
  have hcontract : QM.comap (modelMap R L M) = contractedPrime R K Ω Q L := rfl
  have himage : τ ∈ (QM.inertia (M ≃ₐ[K] M)).map (AlgEquiv.restrictNormalHom L) := by
    rw [FiniteRestriction.map_inertia_eq R K L M QM, hcontract]
    exact hτ
  obtain ⟨τM, hτM, hτML⟩ := himage
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective Ω τM
  refine ⟨σ, ?_, fun x hx => ?_⟩
  · rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L M σ, hσ]
    exact hτML
  · have hxM : (x : Ω) ∈ M.toIntermediateField :=
      FiniteGaloisIntermediateField.adjoin_simple_le_iff.mp
        (show FiniteGaloisIntermediateField.adjoin K {(x : Ω)} ≤ M from
          le_sup_of_le_left (Finset.le_sup
            (f := fun y : integralClosure R Ω =>
              FiniteGaloisIntermediateField.adjoin K {(y : Ω)}) hx))
    let xM : integralClosure R M := ⟨⟨(x : Ω), hxM⟩,
      (isIntegral_algebraMap_iff (B := Ω)).mp x.property⟩
    have hbase : modelMap R M Ω xM = x := rfl
    have hact : modelMap R M Ω (τM • xM) = σ • x := by
      apply Subtype.ext
      change (τM ⟨(x : Ω), hxM⟩ : Ω) = σ (x : Ω)
      rw [← hσ]
      exact AlgEquiv.restrictNormalHom_apply M.toIntermediateField σ ⟨(x : Ω), hxM⟩
    have hres := Ideal.mem_inertia.mp hτM xM
    change modelMap R M Ω (τM • xM - xM) ∈ Q at hres
    simpa only [map_sub, hact, hbase] using hres

/-- Actual absolute integral-closure inertia surjects onto every finite
Galois inertia group at the contraction of the same prime. -/
theorem map_inertia_eq (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    (L : FiniteGaloisIntermediateField K Ω) :
    (Q.inertia (Ω ≃ₐ[K] Ω)).map (AlgEquiv.restrictNormalHom L) =
      (contractedPrime R K Ω Q L).inertia (L ≃ₐ[K] L) := by
  apply le_antisymm
  · rintro τ ⟨σ, hσ, rfl⟩
    rw [Ideal.mem_inertia]
    intro x
    have hx := Ideal.mem_inertia.mp hσ (modelMap R L Ω x)
    change modelMap R L Ω ((AlgEquiv.restrictNormalHom L σ) • x - x) ∈ Q
    rw [map_sub]
    convert hx using 1
    congr 1
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes σ L (x : L)
  · intro τ hτ
    obtain ⟨σ, hσ, he⟩ :=
      Compactness.exists_inertia_lift_of_finite_conditions R K Ω Q L τ
        (finite_conditions R K Ω Q L τ hτ)
    exact ⟨σ, hσ, he⟩

end integralClosure.Inertia.AbsoluteRestriction
