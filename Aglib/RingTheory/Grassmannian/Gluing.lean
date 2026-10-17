/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.Descent

/-!
# Zariski gluing of points of the Grassmannian functor

Let `s : ι → A` be a finite family generating the unit ideal and let `N i` be points of the
Grassmannian over the localizations `A_{s i}` whose base changes to the overlaps agree. Then
the submodule `N₀ = {v | ∀ i, v ↦ N i}` of `A ⊗[R] M` is a point of the Grassmannian over `A`
whose base change to each `A_{s i}` is `N i`. Together with
`Module.Grassmannian.eq_of_map_localization_eq` this is the sheaf property of the Grassmannian
functor for standard Zariski covers (Stacks, Tag 089T: "`F` satisfies the sheaf property for the
Zariski topology").

The overlap of `A_{s i}` and `A_{s j}` is any localization `C i j` of `A_{s j}` away from `s i`,
with an `R`-algebra map `e i j : A_{s i} → C i j` compatible with the maps from `A`.

## Main results

- `Module.Grassmannian.exists_smul_eq_rTensor`: every element of `B ⊗[R] M`, for a localization
  `B` of `A` away from `r`, is a unit multiple of the image of an element of `A ⊗[R] M`.
- `Module.Grassmannian.rTensor_mem_ker_baseChangeMkQ_iff`: the submodule form of
  `rTensor_mem_map_iff_of_isLocalization`.
- `Module.Grassmannian.exists_map_localization_eq`: compatible points over a finite standard
  cover glue to a point over `A`.
-/

@[expose] public section

noncomputable section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
variable {A : Type w} [CommRing A] [Algebra R A]

section Localization

variable {B : Type w} [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem rTensor_toAlgHom_smul (a : A) (v : A ⊗[R] M) :
    LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap (a • v) =
      algebraMap A B a • LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap v := by
  induction v using TensorProduct.inductionOn with
  | tmul b m =>
    simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | add v w hv hw => rw [smul_add, map_add, hv, hw, map_add, smul_add]

/-- Every element of `B ⊗[R] M`, for a localization `B` of `A` away from `r`, becomes the image of
an element of `A ⊗[R] M` after multiplication by a power of `r`. -/
theorem exists_smul_eq_rTensor (r : A) [IsLocalization.Away r B] (w : B ⊗[R] M) :
    ∃ (n : ℕ) (v : A ⊗[R] M), algebraMap A B (r ^ n) • w =
      LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap v := by
  induction w using TensorProduct.inductionOn with
  | tmul b m =>
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers r) b
    refine ⟨n, a ⊗ₜ m, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm]
    simp only at h
    rw [h, LinearMap.rTensor_tmul]
    rfl
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨n₁, v₁, e₁⟩ := h₁
    obtain ⟨n₂, v₂, e₂⟩ := h₂
    refine ⟨n₁ + n₂, r ^ n₂ • v₁ + r ^ n₁ • v₂, ?_⟩
    rw [map_add, rTensor_toAlgHom_smul, rTensor_toAlgHom_smul, ← e₁, ← e₂]
    simp only [smul_add, smul_smul, ← map_mul, ← pow_add, add_comm n₂ n₁]

/-- Let `B` be a localization of `A` away from `r`. The image of `v` lies in the kernel of the
base change of `A ⊗[R] M → (A ⊗[R] M) ⧸ N` to `B` if and only if some power of `r` multiplies
`v` into `N`. -/
theorem rTensor_mem_ker_baseChangeMkQ_iff [BaseChangeMkQFormula.{u, v, w} R M] (r : A)
    [IsLocalization.Away r B]
    (N : Submodule A (A ⊗[R] M)) (v : A ⊗[R] M) :
    LinearMap.rTensor M (IsScalarTower.toAlgHom R A B).toLinearMap v ∈
        LinearMap.ker (baseChangeMkQ B N) ↔ ∃ m : ℕ, r ^ m • v ∈ N := by
  let Q := (A ⊗[R] M) ⧸ N
  have hloc : IsLocalizedModule (Submonoid.powers r) (TensorProduct.mk A B Q 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) B _).mpr
      (TensorProduct.isBaseChange A Q B)
  rw [LinearMap.mem_ker, baseChangeMkQ_rTensor]
  constructor
  · intro h1
    obtain ⟨⟨_, m, rfl⟩, hc⟩ :=
      (IsLocalizedModule.eq_zero_iff (Submonoid.powers r) (TensorProduct.mk A B Q 1)).mp h1
    refine ⟨m, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [Submonoid.smul_def] using hc
  · rintro ⟨m, hm⟩
    have hu : IsUnit (algebraMap A B (r ^ m)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit r).pow m
    have h0 : (r ^ m) • ((1 : B) ⊗ₜ[A] N.mkQ v) = 0 := by
      rw [← TensorProduct.tmul_smul, ← map_smul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero _).mpr hm, TensorProduct.tmul_zero]
    rw [← algebraMap_smul B] at h0
    exact hu.smul_eq_zero.mp h0

end Localization

/-- The image of an element of a point under base change lies in the base change of the
point. -/
theorem rTensor_mem_map_of_mem [BaseChangeMkQFormula.{u, v, w} R M] {B C : Type w}
    [CommRing B] [Algebra R B] [CommRing C]
    [Algebra R C] (e : B →ₐ[R] C) (K : G(k, B ⊗[R] M; B)) {w : B ⊗[R] M}
    (hw : w ∈ K.toSubmodule) :
    LinearMap.rTensor M e.toLinearMap w ∈ (map e K).toSubmodule := by
  let : Algebra B C := e.toAlgebra
  let : IsScalarTower R B C :=
    IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R B C
  have h1 : (map e K).toSubmodule = LinearMap.ker (baseChangeMkQ C K.toSubmodule) :=
    map_toSubmodule e K
  have h2 : baseChangeMkQ C K.toSubmodule (LinearMap.rTensor M e.toLinearMap w) =
      (1 : C) ⊗ₜ[B] K.toSubmodule.mkQ w :=
    baseChangeMkQ_rTensor K.toSubmodule w
  rw [h1, LinearMap.mem_ker, h2, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hw,
    TensorProduct.tmul_zero]

/-- Zariski gluing for the Grassmannian functor: points over a finite standard cover of `Spec A`
whose base changes agree on the overlaps glue to a point over `A`. The overlap of `A_{s i}`
and `A_{s j}` is a localization `C i j` of `A_{s j}` away from `s i`, with an algebra map
`e i j : A_{s i} → C i j` compatible with the maps from `A`. -/
theorem exists_map_localization_eq [BaseChangeMkQFormula.{u, v, w} R M] {ι : Type*} [Finite ι]
    (s : ι → A)
    (hs : Ideal.span (Set.range s) = ⊤)
    (N : ∀ i, G(k, Localization.Away (s i) ⊗[R] M; Localization.Away (s i)))
    (C : ι → ι → Type w) [∀ i j, CommRing (C i j)] [∀ i j, Algebra R (C i j)]
    [∀ i j, Algebra (Localization.Away (s j)) (C i j)]
    [∀ i j, IsScalarTower R (Localization.Away (s j)) (C i j)]
    [∀ i j, IsLocalization.Away (algebraMap A (Localization.Away (s j)) (s i)) (C i j)]
    (e : ∀ i j, Localization.Away (s i) →ₐ[R] C i j)
    (he : ∀ i j, (e i j).comp (IsScalarTower.toAlgHom R A (Localization.Away (s i))) =
      (IsScalarTower.toAlgHom R (Localization.Away (s j)) (C i j)).comp
        (IsScalarTower.toAlgHom R A (Localization.Away (s j))))
    (hN : ∀ i j, map (e i j) (N i) =
      map (IsScalarTower.toAlgHom R (Localization.Away (s j)) (C i j)) (N j)) :
    ∃ N₀ : G(k, A ⊗[R] M; A),
      ∀ i, map (IsScalarTower.toAlgHom R A (Localization.Away (s i))) N₀ = N i := by
  classical
  have := Fintype.ofFinite ι
  let N₀ : Submodule A (A ⊗[R] M) :=
    { carrier := {v | ∀ i, LinearMap.rTensor M
        (IsScalarTower.toAlgHom R A (Localization.Away (s i))).toLinearMap v ∈ (N i).toSubmodule}
      add_mem' := fun hv hw i ↦ by
        rw [map_add]
        exact add_mem (hv i) (hw i)
      zero_mem' := fun i ↦ by
        rw [map_zero]
        exact zero_mem _
      smul_mem' := fun a v hv i ↦ by
        rw [rTensor_toAlgHom_smul]
        exact Submodule.smul_mem _ _ (hv i) }
  have key : ∀ i, LinearMap.ker (baseChangeMkQ (Localization.Away (s i)) N₀) =
      (N i).toSubmodule := by
    intro i
    ext w
    obtain ⟨n, v, hv⟩ := exists_smul_eq_rTensor (B := Localization.Away (s i)) (s i) w
    have hu : ∀ m : ℕ, IsUnit (algebraMap A (Localization.Away (s i)) (s i ^ m)) := fun m ↦ by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (s i)).pow m
    rw [← Submodule.smul_mem_iff_of_isUnit _ (hu n), hv,
      ← Submodule.smul_mem_iff_of_isUnit (N i).toSubmodule (hu n), hv,
      rTensor_mem_ker_baseChangeMkQ_iff (s i) N₀ v]
    constructor
    · rintro ⟨m, hm⟩
      have h := hm i
      rw [rTensor_toAlgHom_smul] at h
      exact (Submodule.smul_mem_iff_of_isUnit _ (hu m)).mp h
    · intro hv'
      have hc : ∀ j, ∃ c : ℕ, LinearMap.rTensor M
          (IsScalarTower.toAlgHom R A (Localization.Away (s j))).toLinearMap (s i ^ c • v) ∈
            (N j).toSubmodule := by
        intro j
        have h1 := rTensor_mem_map_of_mem (e i j) (N i) hv'
        rw [hN i j] at h1
        have hcomp : LinearMap.rTensor M (e i j).toLinearMap
            (LinearMap.rTensor M
              (IsScalarTower.toAlgHom R A (Localization.Away (s i))).toLinearMap v) =
            LinearMap.rTensor M
              (IsScalarTower.toAlgHom R (Localization.Away (s j)) (C i j)).toLinearMap
              (LinearMap.rTensor M
                (IsScalarTower.toAlgHom R A (Localization.Away (s j))).toLinearMap v) := by
          rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← LinearMap.comp_apply,
            ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap, ← AlgHom.comp_toLinearMap,
            he i j]
        rw [hcomp] at h1
        obtain ⟨c, hc⟩ := (rTensor_mem_map_iff_of_isLocalization (B := C i j)
          (algebraMap A (Localization.Away (s j)) (s i)) (N j) _).mp h1
        refine ⟨c, ?_⟩
        rw [rTensor_toAlgHom_smul, map_pow]
        exact hc
      choose c hc using hc
      refine ⟨∑ j, c j, fun j ↦ ?_⟩
      have hle : c j ≤ ∑ j, c j :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      change LinearMap.rTensor M
          (IsScalarTower.toAlgHom R A (Localization.Away (s j))).toLinearMap
          (s i ^ (∑ j, c j) • v) ∈ (N j).toSubmodule
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, rTensor_toAlgHom_smul]
      exact Submodule.smul_mem _ _ (hc j)
  let Q := (A ⊗[R] M) ⧸ N₀
  let E : ∀ i, LocalizedModule.Away (s i) Q ≃ₗ[Localization.Away (s i)]
      ((Localization.Away (s i) ⊗[R] M) ⧸ (N i).toSubmodule) := fun i ↦
    (LocalizedModule.isBaseChange (Submonoid.powers (s i)) Q).equiv.symm ≪≫ₗ
      (baseChangeMkQQuotEquiv (B := Localization.Away (s i)) N₀).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (key i)
  obtain ⟨hfin, hproj, hrank⟩ := finite_projective_rankAtStalk_of_localizationSpan
    (k := k) (Q := Q) (Set.range s) hs
    (fun g ↦ by
      rcases g with ⟨_, i, rfl⟩
      exact Module.Finite.equiv (E i).symm)
    (fun g ↦ by
      rcases g with ⟨_, i, rfl⟩
      exact Module.Projective.of_equiv (E i).symm)
    (fun g p ↦ by
      rcases g with ⟨_, i, rfl⟩
      rw [rankAtStalk_eq_of_equiv (E i)]
      exact (N i).rankAtStalk_eq p)
  refine ⟨⟨N₀, hfin, hproj, hrank⟩, fun i ↦ ?_⟩
  ext : 1
  rw [map_toSubmodule_of_algebraMap _ (fun _ ↦ rfl)]
  exact key i

end Module.Grassmannian
