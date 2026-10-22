/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystemCorrection
public import Aglib.RingTheory.AdicCompletion.CompatibleSystemGenerators
public import Aglib.RingTheory.AdicCompletion.TowerComparison
public import Aglib.Algebra.Category.ModuleCat.NatTowerExactUniverses
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Completed presentations of compatible finite systems

A compatible stagewise-surjective presentation induces a surjection from the
native completion to the native inverse limit. Kernel transitions are proved
surjective by correcting the error in the precise defining ideal multiple.
The presentation module and stage modules have independent universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace AdicCompletion

universe u v w

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (P : Type w) [AddCommGroup P] [Module R P]

/-- The diagram of original ideal-power quotients of a module. -/
def moduleQuotientTower : ℕᵒᵖ ⥤ ModuleCat.{w} R where
  obj n := ModuleCat.of R (P ⧸ (I ^ n.unop • ⊤ : Submodule R P))
  map f := ModuleCat.ofHom (Submodule.factorPow I P (leOfHom f.unop))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    induction x using Submodule.Quotient.induction_on
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    induction x using Submodule.Quotient.induction_on
    rfl

/-- Native completion is the native compatible-section module of its quotient diagram. -/
def completionSectionsEquiv :
    AdicCompletion I P ≃ₗ[R] ModuleCat.sectionsSubmodule (moduleQuotientTower I P) where
  toFun x := ⟨fun j => x.val j.unop, fun {_ _} f => x.property (leOfHom f.unop)⟩
  invFun x := ⟨fun n => x.val (op n), fun h => x.property (homOfLE h).op⟩
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    funext j
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {P}
variable (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (hF : IsCompatibleSystem I F)
variable (uMap : ∀ n : ℕ, P →ₗ[R] F.obj (op n))
variable (hu : ∀ {m n : ℕ} (h : m ≤ n),
  (towerTransition F h).comp (uMap n) = uMap m)
variable (hpow : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R P) ≤ (uMap n).ker)
variable (hsurj : ∀ n : ℕ, Function.Surjective (uMap n))

include hsurj in
/-- The quotient factors of a stagewise surjective presentation are surjective. -/
theorem quotientToTower_surjective (n : ℕ) :
    Function.Surjective (quotientToTower I F uMap hpow n) := by
  intro y
  obtain ⟨x, hx⟩ := hsurj n y
  exact ⟨Submodule.Quotient.mk x, hx⟩

include hF hu hsurj in
/-- The actual kernels of the quotient-level presentation have surjective transitions. -/
theorem quotientToTower_kernel_lift (n : ℕ)
    (x : P ⧸ (I ^ n • ⊤ : Submodule R P))
    (hx : quotientToTower I F uMap hpow n x = 0) :
    ∃ y : P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P),
      quotientToTower I F uMap hpow (n + 1) y = 0 ∧
        Submodule.factorPow I P (Nat.le_succ n) y = x := by
  apply LinearMap.exists_ker_lift_of_smul (I ^ n)
    (quotientToTower I F uMap hpow n) (quotientToTower I F uMap hpow (n + 1))
    (Submodule.factorPow I P (Nat.le_succ n)) (towerTransition F (Nat.le_succ n))
    (Submodule.factor_surjective _) (quotientToTower_surjective I F uMap hpow hsurj (n + 1))
    _ _ _ x hx
  · apply LinearMap.ext
    intro z
    exact towerTransition_quotientToTower I F uMap hu hpow (Nat.le_succ n) z
  · exact le_of_eq (hF.ker_transition n)
  · apply Submodule.smul_le.mpr
    intro a ha z _
    change Submodule.factorPow I P (Nat.le_succ n) (a • z) = 0
    rw [map_smul]
    exact Module.isTorsionBySet_quotient_ideal_smul P (I ^ n)
      (x := Submodule.factorPow I P (Nat.le_succ n) z) (a := ⟨a, ha⟩)

include hF hsurj in
/-- Stagewise compatible surjections yield a surjection from the actual completed
presentation module. No completeness of the original coefficient ring is used. -/
theorem completionToSections_surjective_of_compatibleSystem :
    Function.Surjective (completionToSections I F uMap hu hpow) := by
  let q : ∀ j : ℕᵒᵖ, (moduleQuotientTower I P).obj j →ₗ[R] F.obj j :=
    fun j => quotientToTower I F uMap hpow j.unop
  have hq : ∀ {j k : ℕᵒᵖ} (f : j ⟶ k) (x : (moduleQuotientTower I P).obj j),
      q k ((moduleQuotientTower I P).map f x) = F.map f (q j x) := by
    intro j k f x
    exact (towerTransition_quotientToTower I F uMap hu hpow (leOfHom f.unop) x).symm
  have hs := ModuleCat.sectionsMapOfLinearMaps_surjective q hq
    (quotientToTower_surjective I F uMap hpow hsurj)
    (quotientToTower_kernel_lift I F hF uMap hu hpow hsurj)
  intro y
  obtain ⟨x, hx⟩ := hs y
  refine ⟨(completionSectionsEquiv I P).symm x, ?_⟩
  apply Subtype.ext
  funext j
  exact congrArg (fun s : ModuleCat.sectionsSubmodule F => s.val j) hx

end AdicCompletion
