/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
Extraction source: `R5Lab.Aglib.RingTheory.IntegralClosure.Inertia.Finite`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`55aca5a4c6ae8622d439d174d318b928b088828de4a569d96f83a1478a8e13b7`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace integralClosure.Inertia.FiniteRestriction

variable (R K L M : Type*) [CommRing R] [Field K] [Field L] [Field M]
  [Algebra R K] [Algebra K L] [Algebra K M] [Algebra L M]
  [Algebra R L] [Algebra R M] [IsScalarTower R K L] [IsScalarTower R K M]
  [IsScalarTower K L M] [IsScalarTower R L M]

/-- The actual inclusion between the two integral closures in a tower. -/
def modelMap : integralClosure R L →ₐ[R] integralClosure R M :=
  (IsScalarTower.toAlgHom R L M).mapIntegralClosure

@[simp] theorem modelMap_val (x : integralClosure R L) :
    (modelMap R L M x : M) = algebraMap L M (x : L) := rfl

variable [IsGalois K M] [Normal K L]

omit [IsScalarTower R K L] in
/-- Fixed integral elements of the finite restriction kernel come from the
actual lower integral closure. This derives the invariant-extension input. -/
theorem kernelInvariant :
    letI := (modelMap R L M).toAlgebra
    Algebra.IsInvariant (integralClosure R L) (integralClosure R M)
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).ker := by
  letI := (modelMap R L M).toAlgebra
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  refine ⟨fun b hb => ?_⟩
  have hfixed : ∀ σ : M ≃ₐ[L] M, σ (b : M) = b := by
    intro σ
    let σK : M ≃ₐ[K] M := σ.restrictScalars K
    have hker : σK ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).ker := by
      apply AlgEquiv.ext
      intro x
      apply (algebraMap L M).injective
      exact (AlgEquiv.restrictNormal_commutes σK L x).trans (σ.commutes x)
    have hbσ := congrArg Subtype.val (hb ⟨σK, hker⟩)
    exact hbσ
  obtain ⟨l, hl⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (K := M) (b : M)).mpr hfixed
  have hint : IsIntegral R l := by
    apply (isIntegral_algebraMap_iff (B := M)).mp
    rw [hl]
    exact b.property
  refine ⟨⟨l, hint⟩, ?_⟩
  exact Subtype.ext hl

/-- Inertia restricts surjectively in a finite Galois tower, for the literal
contraction of the same prime of the actual integral closure. -/
theorem map_inertia_eq [FiniteDimensional K M]
    (Q : Ideal (integralClosure R M)) [Q.IsPrime] :
    (Q.inertia (M ≃ₐ[K] M)).map (AlgEquiv.restrictNormalHom L) =
      (Q.comap (modelMap R L M)).inertia (L ≃ₐ[K] L) := by
  letI := (modelMap R L M).toAlgebra
  let p : Ideal (integralClosure R L) := Q.comap (modelMap R L M)
  haveI : Q.LiesOver p := ⟨rfl⟩
  haveI := kernelInvariant R K L M
  apply Ideal.map_inertia_of_surjective (AlgEquiv.restrictNormalHom L)
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).ker p Q
    (AlgEquiv.restrictNormalHom_surjective M) le_rfl
  intro σ x
  apply Subtype.ext
  exact AlgEquiv.restrictNormal_commutes σ L (x : L)

end integralClosure.Inertia.FiniteRestriction
