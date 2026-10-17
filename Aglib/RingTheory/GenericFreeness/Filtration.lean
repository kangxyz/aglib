/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Freeness of filtered modules and of their localizations

These are the linear-algebra inputs of generic freeness
(`Aglib.RingTheory.GenericFreeness.Noetherian`).

* `Module.free_of_filtration`: a module with an exhaustive increasing `ℕ`-filtration
  `F 0 = ⊥ ≤ F 1 ≤ ⋯` whose graded pieces `F (j + 1) / F j` are free is free.
* `Module.free_localizedModule_of_filtration`: the same after localization at a submonoid
  `S`; only the localized graded pieces have to be free.
* `Module.free_of_isLocalizedModule_of_free_isLocalizedModule`,
  `Module.free_localizedModule_of_linearEquiv` and
  `Module.free_localizedModule_away_of_dvd`: freeness of a localization is independent of the
  chosen localization, is transported along linear equivalences, and passes from
  `M[1/a]` to `M[1/b]` when `a ∣ b`.

The graded pieces are written `↥(F (j + 1)) ⧸ (F j).comap (F (j + 1)).subtype`.
-/

@[expose] public section

open DirectSum

namespace Module

variable {R : Type*} [CommRing R]

section Filtration

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A module with an exhaustive increasing `ℕ`-filtration starting at `⊥` whose graded pieces
`F (j + 1) / F j` are free is free. Sections of the graded projections identify the module with
the direct sum of its graded pieces. -/
theorem free_of_filtration (F : ℕ → Submodule R M) (hF : Monotone F) (h0 : F 0 = ⊥)
    (htop : ⨆ j, F j = ⊤)
    (hfree : ∀ j, Module.Free R (↥(F (j + 1)) ⧸ (F j).comap (F (j + 1)).subtype)) :
    Module.Free R M := by
  classical
  choose σ hσ using fun j =>
    have := hfree j
    Module.projective_lifting_property ((F j).comap (F (j + 1)).subtype).mkQ LinearMap.id
      (Submodule.mkQ_surjective _)
  have hσ_apply : ∀ j g, ((F j).comap (F (j + 1)).subtype).mkQ (σ j g) = g :=
    fun j g => LinearMap.congr_fun (hσ j) g
  let Φ : (⨁ j, ↥(F (j + 1)) ⧸ (F j).comap (F (j + 1)).subtype) →ₗ[R] M :=
    DirectSum.toModule R ℕ M fun j => (F (j + 1)).subtype ∘ₗ σ j
  have hΦ_of : ∀ j g, Φ (DirectSum.of _ j g) = (σ j g : M) := fun j g => by
    rw [← DirectSum.lof_eq_of R]
    exact DirectSum.toModule_lof (M := fun j => ↥(F (j + 1)) ⧸ (F j).comap (F (j + 1)).subtype)
      R j g
  -- an element of the direct sum supported below `n` maps into `F n`
  have hΦ_mem : ∀ n (d : ⨁ j, ↥(F (j + 1)) ⧸ (F j).comap (F (j + 1)).subtype),
      (∀ k, n ≤ k → d k = 0) → Φ d ∈ F n := by
    intro n d hd
    rw [← DirectSum.sum_support_of d, map_sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have hkn : k + 1 ≤ n := by
      by_contra h
      exact (DFinsupp.mem_support_iff.mp hk) (hd k (by omega))
    rw [hΦ_of]
    exact hF hkn (σ k (d k)).2
  have hΦ_inj : Function.Injective Φ := by
    have key : ∀ n (d : ⨁ j, ↥(F (j + 1)) ⧸ (F j).comap (F (j + 1)).subtype),
        (∀ k, n ≤ k → d k = 0) → Φ d = 0 → d = 0 := by
      intro n
      induction n with
      | zero =>
        intro d hd _
        ext k
        exact hd k (Nat.zero_le k)
      | succ n ih =>
        intro d hd hΦd
        have hd' : ∀ k, n ≤ k → (d.erase n) k = 0 := by
          intro k hk
          rcases eq_or_ne k n with rfl | hne
          · exact DFinsupp.erase_same
          · rw [DFinsupp.erase_ne hne]
            exact hd k (by omega)
        have hmem : Φ (d.erase n) ∈ F n := hΦ_mem n _ hd'
        have hsplit : Φ (d.erase n) + (σ n (d n) : M) = 0 := by
          rw [← hΦ_of, ← map_add, ← hΦd]
          congr 1
          exact DFinsupp.erase_add_single n d
        have hn : d n = 0 := by
          have h1 : (⟨Φ (d.erase n), hF (Nat.le_succ n) hmem⟩ : F (n + 1)) + σ n (d n) = 0 :=
            Subtype.ext hsplit
          have h2 := congrArg ((F n).comap (F (n + 1)).subtype).mkQ h1
          have h3 : ((F n).comap (F (n + 1)).subtype).mkQ
              ⟨Φ (d.erase n), hF (Nat.le_succ n) hmem⟩ = 0 :=
            LinearMap.mem_ker.mp (by rw [Submodule.ker_mkQ]; exact hmem)
          rwa [map_add, hσ_apply, map_zero, h3, zero_add] at h2
        have hde : d.erase n = d := by
          ext k
          rcases eq_or_ne k n with rfl | hne
          · rw [DFinsupp.erase_same, hn]
          · rw [DFinsupp.erase_ne hne]
        rw [← hde]
        exact ih _ hd' (by rw [hde]; exact hΦd)
    intro d₁ d₂ h
    rw [← sub_eq_zero]
    obtain ⟨n, hn⟩ : ∃ n, ∀ k, n ≤ k → (d₁ - d₂) k = 0 := by
      refine ⟨(d₁ - d₂).support.sup id + 1, fun k hk => ?_⟩
      by_contra hne
      have := Finset.le_sup (f := id) (DFinsupp.mem_support_iff.mpr hne)
      simp only [id_eq] at this
      omega
    exact key n _ hn (by rw [map_sub, h, sub_self])
  have hΦ_surj : Function.Surjective Φ := by
    have key : ∀ n, F n ≤ LinearMap.range Φ := by
      intro n
      induction n with
      | zero => rw [h0]; exact bot_le
      | succ n ih =>
        intro m hm
        have hdiff : (⟨m, hm⟩ - σ n (((F n).comap (F (n + 1)).subtype).mkQ ⟨m, hm⟩) :
            F (n + 1)) ∈ (F n).comap (F (n + 1)).subtype := by
          have h := LinearMap.mem_ker.mpr (show ((F n).comap (F (n + 1)).subtype).mkQ
              (⟨m, hm⟩ - σ n (((F n).comap (F (n + 1)).subtype).mkQ ⟨m, hm⟩)) = 0 by
            rw [map_sub, hσ_apply, sub_self])
          rwa [Submodule.ker_mkQ] at h
        have h1 : m - (σ n (((F n).comap (F (n + 1)).subtype).mkQ ⟨m, hm⟩) : M) ∈
            LinearMap.range Φ := ih hdiff
        have h2 : (σ n (((F n).comap (F (n + 1)).subtype).mkQ ⟨m, hm⟩) : M) ∈
            LinearMap.range Φ := ⟨DirectSum.of _ n _, hΦ_of n _⟩
        simpa using add_mem h1 h2
    rw [← LinearMap.range_eq_top, eq_top_iff, ← htop]
    exact iSup_le key
  exact Module.Free.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦ_inj, hΦ_surj⟩)

end Filtration

section Localization

variable (S : Submonoid R)

/-- Freeness of a localization of `P` at `S` over `Rₛ` does not depend on the chosen
localization. -/
theorem free_of_isLocalizedModule_of_free_isLocalizedModule
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
    [IsLocalization S Rₛ] {P P' P'' : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P'] [Module Rₛ P'] [IsScalarTower R Rₛ P']
    [AddCommGroup P''] [Module R P''] [Module Rₛ P''] [IsScalarTower R Rₛ P'']
    (f : P →ₗ[R] P') (g : P →ₗ[R] P'') [IsLocalizedModule S f] [IsLocalizedModule S g]
    [Module.Free Rₛ P'] : Module.Free Rₛ P'' :=
  Module.Free.of_equiv ((IsLocalizedModule.linearEquiv S f g).extendScalarsOfIsLocalization S Rₛ)

/-- Freeness of the localization `P_S` is transported along a linear equivalence `P ≃ Q`. -/
theorem free_localizedModule_of_linearEquiv {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q)
    [Module.Free (Localization S) (LocalizedModule S P)] :
    Module.Free (Localization S) (LocalizedModule S Q) :=
  free_of_isLocalizedModule_of_free_isLocalizedModule S (Localization S)
    (LocalizedModule.mkLinearMap S P) ((LocalizedModule.mkLinearMap S Q) ∘ₗ e.toLinearMap)

/-- If `P[1/a]` is free over `R[1/a]` and `a ∣ b`, then `P[1/b]` is free over `R[1/b]`: the
latter is the base change of the former along `R[1/a] → R[1/b]`. -/
theorem free_localizedModule_away_of_dvd {P : Type*} [AddCommGroup P] [Module R P] {a b : R}
    (hab : a ∣ b) [Module.Free (Localization.Away a) (LocalizedModule.Away a P)] :
    Module.Free (Localization.Away b) (LocalizedModule.Away b P) := by
  obtain ⟨c, rfl⟩ := hab
  let : Algebra (Localization.Away a) (Localization.Away (a * c)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away a) a c).toAlgebra
  have : IsScalarTower R (Localization.Away a) (Localization.Away (a * c)) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away a) a c r).symm
  let : Module (Localization.Away a) (LocalizedModule.Away (a * c) P) :=
    Module.compHom _ (algebraMap (Localization.Away a) (Localization.Away (a * c)))
  have : IsScalarTower (Localization.Away a) (Localization.Away (a * c))
      (LocalizedModule.Away (a * c) P) :=
    ⟨fun x y m => by
      change (x • y) • m = algebraMap _ (Localization.Away (a * c)) x • y • m
      rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower R (Localization.Away a) (LocalizedModule.Away (a * c) P) :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      change algebraMap _ (Localization.Away (a * c)) (algebraMap R (Localization.Away a) r) • m =
        r • m
      rw [← IsScalarTower.algebraMap_apply, algebraMap_smul]
  have hunit : ∀ s : Submonoid.powers a,
      IsUnit (algebraMap R (Module.End R (LocalizedModule.Away (a * c) P)) s) := by
    rintro ⟨_, k, rfl⟩
    rw [← (Algebra.lsmul R (A := Localization.Away (a * c)) R
      (LocalizedModule.Away (a * c) P)).commutes]
    refine IsUnit.map _ ?_
    exact (IsLocalization.Away.algebraMap_isUnit_iff (a * c)).mpr ⟨k, by
      rw [mul_pow]; exact dvd_mul_right _ _⟩
  let ℓ : LocalizedModule.Away a P →ₗ[R] LocalizedModule.Away (a * c) P :=
    LocalizedModule.lift _ (LocalizedModule.mkLinearMap _ P) hunit
  let h : LocalizedModule.Away a P →ₗ[Localization.Away a] LocalizedModule.Away (a * c) P :=
    ℓ.extendScalarsOfIsLocalization (Submonoid.powers a) (Localization.Away a)
  have hcomp : (h : LocalizedModule.Away a P →ₗ[R] LocalizedModule.Away (a * c) P) ∘ₗ
      LocalizedModule.mkLinearMap (Submonoid.powers a) P =
        LocalizedModule.mkLinearMap (Submonoid.powers (a * c)) P :=
    LocalizedModule.lift_comp _ _ hunit
  have hc : IsBaseChange (Localization.Away (a * c))
      ((h : LocalizedModule.Away a P →ₗ[R] LocalizedModule.Away (a * c) P) ∘ₗ
        LocalizedModule.mkLinearMap (Submonoid.powers a) P) := by
    rw [hcomp]
    exact LocalizedModule.isBaseChange _ P
  exact (IsBaseChange.of_comp (LocalizedModule.isBaseChange _ P) hc).free

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The localization of the `ℓ`-th member of a filtration, as an element of the localized
module, is the localization of the underlying element. -/
private theorem coe_mk'_toLocalized (P : Submodule R M) (m : P) (s : S) :
    ((IsLocalizedModule.mk' (P.toLocalized S) m s : P.localized S) : LocalizedModule S M) =
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) (m : M) s := by
  symm
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← Submodule.coe_smul_of_tower,
    ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
  rfl

/-- A filtered module whose graded pieces become free after localization at `S` becomes free
after localization at `S`: the localized filtration has the localized graded pieces. -/
theorem free_localizedModule_of_filtration (F : ℕ → Submodule R M) (hF : Monotone F)
    (h0 : F 0 = ⊥) (htop : ⨆ j, F j = ⊤)
    (hfree : ∀ j, Module.Free (Localization S)
      (LocalizedModule S (↥(F (j + 1)) ⧸ (F j).comap (F (j + 1)).subtype))) :
    Module.Free (Localization S) (LocalizedModule S M) := by
  refine free_of_filtration (fun j => (F j).localized S) (fun i j hij => ?_) ?_ ?_ fun j => ?_
  · rintro _ ⟨m, hm, s, rfl⟩
    exact ⟨m, hF hij hm, s, rfl⟩
  · simp only [h0]
    exact Submodule.localized'_bot _ _ _
  · simp only [← Submodule.localized'_iSup, htop]
    exact Submodule.localized'_top _ _ _
  · let K : Submodule R (F (j + 1)) := (F j).comap (F (j + 1)).subtype
    have hK : K.localized' (Localization S) S ((F (j + 1)).toLocalized S) =
        ((F j).localized S).comap ((F (j + 1)).localized S).subtype := by
      ext ⟨x, hx⟩
      simp only [Submodule.mem_localized', Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · rintro ⟨m, hm, s, hms⟩
        exact ⟨m, hm, s, (coe_mk'_toLocalized S (F (j + 1)) m s).symm.trans
          (congrArg Subtype.val hms)⟩
      · rintro ⟨m, hm, s, hms⟩
        refine ⟨⟨m, hF (Nat.le_succ j) hm⟩, hm, s, Subtype.ext ?_⟩
        rw [coe_mk'_toLocalized]
        exact hms
    have := hfree j
    have : IsLocalizedModule S
        (((Submodule.quotEquivOfEq _ _ hK).restrictScalars R).toLinearMap ∘ₗ
          K.toLocalizedQuotient' (Localization S) S ((F (j + 1)).toLocalized S)) :=
      IsLocalizedModule.of_linearEquiv S _ _
    exact free_of_isLocalizedModule_of_free_isLocalizedModule S (Localization S)
      (LocalizedModule.mkLinearMap S (F (j + 1) ⧸ K))
      (((Submodule.quotEquivOfEq _ _ hK).restrictScalars R).toLinearMap ∘ₗ
        K.toLocalizedQuotient' (Localization S) S ((F (j + 1)).toLocalized S))

/-- Variant of `Module.free_localizedModule_of_filtration` for a filtration by submodules over
an `R`-algebra `C`; the graded pieces are the `C`-module quotients, regarded as `R`-modules. -/
theorem free_localizedModule_of_filtration_of_isScalarTower {C : Type*} [CommRing C]
    [Algebra R C] [Module C M] [IsScalarTower R C M] (F : ℕ → Submodule C M) (hF : Monotone F)
    (h0 : F 0 = ⊥) (htop : ⨆ j, F j = ⊤)
    (hfree : ∀ j, Module.Free (Localization S)
      (LocalizedModule S (↥(F (j + 1)) ⧸ (F j).comap (F (j + 1)).subtype))) :
    Module.Free (Localization S) (LocalizedModule S M) := by
  refine free_localizedModule_of_filtration S (fun j => (F j).restrictScalars R)
    (fun i j h => Submodule.restrictScalars_mono R (hF h)) (by simp [h0]) ?_ fun j => ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨j, hj⟩ := (Submodule.mem_iSup_of_directed F hF.directed_le).mp
      (htop ▸ Submodule.mem_top : x ∈ ⨆ j, F j)
    exact Submodule.mem_iSup_of_mem (p := fun j => (F j).restrictScalars R) j hj
  · let e : ↥((F (j + 1)).restrictScalars R) ≃ₗ[R] ↥(F (j + 1)) :=
      { AddEquiv.refl _ with map_smul' := fun _ _ => rfl }
    have he : (((F j).restrictScalars R).comap ((F (j + 1)).restrictScalars R).subtype).map
        (e : ↥((F (j + 1)).restrictScalars R) →ₗ[R] ↥(F (j + 1))) =
          ((F j).comap (F (j + 1)).subtype).restrictScalars R := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have := hfree j
    exact free_localizedModule_of_linearEquiv S ((Submodule.Quotient.equiv _ _ e he).trans
      (Submodule.Quotient.restrictScalarsEquiv R _)).symm

end Localization

end Module
