/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Adic completion and inverse towers

The canonical quotient maps give a linear map from native adic completion to the
native sections of a module-valued inverse tower. A shifted kernel bound and an
eventual range bound make this map an equivalence. The two bounds may have different
shifts. No finiteness, Noetherianity, or surjectivity of tower transitions is needed.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AdicCompletion

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable (I : Ideal R) (Q : ℕᵒᵖ ⥤ ModuleCat.{w} R)

/-- The actual transition map of a module-valued inverse tower. -/
abbrev towerTransition {m n : ℕ} (h : m ≤ n) : Q.obj (op n) →ₗ[R] Q.obj (op m) :=
  (Q.map (homOfLE h).op).hom

variable (uMap : ∀ n : ℕ, M →ₗ[R] Q.obj (op n))
variable (hu : ∀ {m n : ℕ} (h : m ≤ n),
  (towerTransition Q h).comp (uMap n) = uMap m)
variable (hpow : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R M) ≤ (uMap n).ker)

/-- The quotient factor of the original map at stage `n`. -/
def quotientToTower (n : ℕ) :
    (M ⧸ (I ^ n • ⊤ : Submodule R M)) →ₗ[R] Q.obj (op n) :=
  (I ^ n • ⊤ : Submodule R M).liftQ (uMap n) (hpow n)

@[simp] theorem quotientToTower_mk (n : ℕ) (x : M) :
    quotientToTower I Q uMap hpow n (Submodule.Quotient.mk x) = uMap n x := rfl

include hu in
/-- The quotient factors commute with the actual tower transitions. -/
theorem towerTransition_quotientToTower {m n : ℕ} (h : m ≤ n)
    (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    towerTransition Q h (quotientToTower I Q uMap hpow n x) =
      quotientToTower I Q uMap hpow m (transitionMap I M h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact LinearMap.congr_fun (hu h) x

/-- The canonical map from adic completion to the compatible sections of a tower. -/
def completionToSections : AdicCompletion I M →ₗ[R] ModuleCat.sectionsSubmodule Q where
  toFun x := ⟨fun j => quotientToTower I Q uMap hpow j.unop (x.val j.unop), by
    intro j k f
    have h : k.unop ≤ j.unop := leOfHom f.unop
    have hf : f = (homOfLE h).op := Subsingleton.elim _ _
    change (Q.map f).hom _ = _
    rw [hf]
    exact (towerTransition_quotientToTower I Q uMap hu hpow h _).trans
      (congrArg (quotientToTower I Q uMap hpow k.unop) (x.property h))⟩
  map_add' x y := by
    apply Subtype.ext
    funext j
    exact (quotientToTower I Q uMap hpow j.unop).map_add
      (x.val j.unop) (y.val j.unop)
  map_smul' r x := by
    apply Subtype.ext
    funext j
    exact (quotientToTower I Q uMap hpow j.unop).map_smul r (x.val j.unop)

/-- Each coordinate is the original quotient factor composed with completion evaluation. -/
@[simp] theorem completionToSections_apply (x : AdicCompletion I M) (n : ℕ) :
    (completionToSections I Q uMap hu hpow x).val (op n) =
      quotientToTower I Q uMap hpow n (eval I M n x) := rfl

/-- On the original module the comparison is the given compatible family. -/
@[simp] theorem completionToSections_of (x : M) (n : ℕ) :
    (completionToSections I Q uMap hu hpow (of I M x)).val (op n) = uMap n x := rfl

/-- The shifted kernel bound alone makes the canonical comparison injective. -/
theorem completionToSections_injective (a : ℕ)
    (hker : ∀ n, (uMap (n + a)).ker ≤ (I ^ n • ⊤ : Submodule R M)) :
    Function.Injective (completionToSections I Q uMap hu hpow) := by
  intro x y hxy
  apply AdicCompletion.ext
  intro n
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective
    (p := (I ^ (n + a) • ⊤ : Submodule R M)) (x.val (n + a))
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective
    (p := (I ^ (n + a) • ⊤ : Submodule R M)) (y.val (n + a))
  have heq : uMap (n + a) s = uMap (n + a) t := by
    have hh := congrArg (fun z : ModuleCat.sectionsSubmodule Q => z.val (op (n + a))) hxy
    change quotientToTower I Q uMap hpow (n + a) (x.val (n + a)) =
      quotientToTower I Q uMap hpow (n + a) (y.val (n + a)) at hh
    simpa only [← hs, ← ht, quotientToTower_mk] using hh
  have hmem : s - t ∈ (I ^ n • ⊤ : Submodule R M) :=
    hker n (by change uMap (n + a) (s - t) = 0; rw [map_sub, heq, sub_self])
  have h := (Submodule.Quotient.eq (I ^ n • ⊤ : Submodule R M)).2 hmem
  have hx := x.property (Nat.le_add_right n a)
  have hy := y.property (Nat.le_add_right n a)
  rw [← hs] at hx
  rw [← ht] at hy
  exact hx.symm.trans (h.trans hy)

/-- Every compatible tower section lifts if the kernels and transition ranges have
uniform (possibly different) shifts. -/
theorem completionToSections_surjective (a b : ℕ)
    (hker : ∀ n, (uMap (n + a)).ker ≤ (I ^ n • ⊤ : Submodule R M))
    (hrange : ∀ n, LinearMap.range (towerTransition Q (Nat.le_add_right n b)) ≤
      LinearMap.range (uMap n)) :
    Function.Surjective (completionToSections I Q uMap hu hpow) := by
  intro y
  have hy (m n : ℕ) (h : m ≤ n) :
      towerTransition Q h (y.val (op n)) = y.val (op m) :=
    y.property (homOfLE h).op
  have hlift (n : ℕ) : ∃ s : M, uMap (n + a) s = y.val (op (n + a)) := by
    apply hrange (n + a)
    exact ⟨y.val (op ((n + a) + b)), hy _ _ (Nat.le_add_right (n + a) b)⟩
  choose s hs using hlift
  have hs' {m n : ℕ} (h : m ≤ n) : uMap (m + a) (s n) = y.val (op (m + a)) := by
    rw [← LinearMap.congr_fun (hu (Nat.add_le_add_right h a)) (s n),
      LinearMap.comp_apply, hs]
    exact hy _ _ _
  let x : AdicCompletion I M := ⟨fun n => Submodule.Quotient.mk (s n), by
    intro m n h
    change (Submodule.Quotient.mk (s n) : M ⧸ (I ^ m • ⊤ : Submodule R M)) =
      Submodule.Quotient.mk (s m)
    apply (Submodule.Quotient.eq _).2
    apply hker m
    change uMap (m + a) (s n - s m) = 0
    rw [map_sub, hs' h, hs m, sub_self]⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext j
  change uMap j.unop (s j.unop) = y.val j
  rw [← LinearMap.congr_fun (hu (Nat.le_add_right j.unop a)) (s j.unop),
    LinearMap.comp_apply, hs]
  exact hy _ _ _

/-- Shifted kernel and eventual range bounds imply bijectivity of the canonical map. -/
theorem completionToSections_bijective (a b : ℕ)
    (hker : ∀ n, (uMap (n + a)).ker ≤ (I ^ n • ⊤ : Submodule R M))
    (hrange : ∀ n, LinearMap.range (towerTransition Q (Nat.le_add_right n b)) ≤
      LinearMap.range (uMap n)) :
    Function.Bijective (completionToSections I Q uMap hu hpow) :=
  ⟨completionToSections_injective I Q uMap hu hpow a hker,
    completionToSections_surjective I Q uMap hu hpow a b hker hrange⟩

/-- The canonical completion equivalence under shifted kernel and eventual range bounds. -/
def completionToSectionsEquiv (a b : ℕ)
    (hker : ∀ n, (uMap (n + a)).ker ≤ (I ^ n • ⊤ : Submodule R M))
    (hrange : ∀ n, LinearMap.range (towerTransition Q (Nat.le_add_right n b)) ≤
      LinearMap.range (uMap n)) :
    AdicCompletion I M ≃ₗ[R] ModuleCat.sectionsSubmodule Q :=
  LinearEquiv.ofBijective (completionToSections I Q uMap hu hpow)
    (completionToSections_bijective I Q uMap hu hpow a b hker hrange)

@[simp] theorem completionToSectionsEquiv_apply (a b : ℕ)
    (hker : ∀ n, (uMap (n + a)).ker ≤ (I ^ n • ⊤ : Submodule R M))
    (hrange : ∀ n, LinearMap.range (towerTransition Q (Nat.le_add_right n b)) ≤
      LinearMap.range (uMap n)) (x : AdicCompletion I M) (n : ℕ) :
    (completionToSectionsEquiv I Q uMap hu hpow a b hker hrange x).val (op n) =
      quotientToTower I Q uMap hpow n (eval I M n x) := rfl

/-- The inverse coordinate is the class of any lift at the shifted stage. In particular,
it does not depend on a choice of lift or on the eventual-range shift. -/
theorem eval_completionToSectionsEquiv_symm (a b : ℕ)
    (hker : ∀ n, (uMap (n + a)).ker ≤ (I ^ n • ⊤ : Submodule R M))
    (hrange : ∀ n, LinearMap.range (towerTransition Q (Nat.le_add_right n b)) ≤
      LinearMap.range (uMap n)) (y : ModuleCat.sectionsSubmodule Q) (n : ℕ)
    (s : M) (hs : uMap (n + a) s = y.val (op (n + a))) :
    eval I M n ((completionToSectionsEquiv I Q uMap hu hpow a b hker hrange).symm y) =
      Submodule.Quotient.mk s := by
  let e := completionToSectionsEquiv I Q uMap hu hpow a b hker hrange
  let x := e.symm y
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective
    (p := (I ^ (n + a) • ⊤ : Submodule R M)) (x.val (n + a))
  have heq : uMap (n + a) t = uMap (n + a) s := by
    have hh := congrArg (fun z : ModuleCat.sectionsSubmodule Q => z.val (op (n + a)))
      (e.apply_symm_apply y)
    change quotientToTower I Q uMap hpow (n + a) (x.val (n + a)) =
      y.val (op (n + a)) at hh
    simpa only [← ht, quotientToTower_mk, hs] using hh
  have hmem : t - s ∈ (I ^ n • ⊤ : Submodule R M) :=
    hker n (by change uMap (n + a) (t - s) = 0; rw [map_sub, heq, sub_self])
  have h := (Submodule.Quotient.eq (I ^ n • ⊤ : Submodule R M)).2 hmem
  have hx := x.property (Nat.le_add_right n a)
  rw [← ht] at hx
  exact hx.symm.trans h

end AdicCompletion
