/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompatibleSystemPresentation
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Exact kernels of projections from compatible-system limits -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace AdicCompletion

universe u v w

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {P : Type w} [AddCommGroup P] [Module R P]
variable (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (hF : IsCompatibleSystem I F)
variable (uMap : ∀ n : ℕ, P →ₗ[R] F.obj (op n))
variable (hu : ∀ {m n : ℕ} (h : m ≤ n),
  (towerTransition F h).comp (uMap n) = uMap m)
variable (hpow : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R P) ≤ (uMap n).ker)
variable (hsurj : ∀ n : ℕ, Function.Surjective (uMap n))

/-- The actual kernel modules of a compatible quotient presentation. These
kernels are not asserted to be an adic system. -/
def presentationKernelTower : ℕᵒᵖ ⥤ ModuleCat.{w} R where
  obj n := ModuleCat.of R (quotientToTower I F uMap hpow n.unop).ker
  map f := ModuleCat.ofHom
    { toFun x := ⟨Submodule.factorPow I P (leOfHom f.unop) x.val, by
        change quotientToTower I F uMap hpow _ _ = 0
        rw [← towerTransition_quotientToTower I F uMap hu hpow,
          x.property, _root_.map_zero]⟩
      map_add' x y := Subtype.ext (map_add _ x.val y.val)
      map_smul' r x := Subtype.ext (map_smul _ r x.val) }
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change Submodule.factorPow I P (le_refl n.unop) x.val = x.val
    induction x.val using Submodule.Quotient.induction_on
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change Submodule.factorPow I P _ x.val =
      Submodule.factorPow I P _ (Submodule.factorPow I P _ x.val)
    induction x.val using Submodule.Quotient.induction_on
    rfl

include hF hsurj in
/-- Every kernel vector at a fixed stage lifts to an actual completed vector
which maps to zero in the system limit. -/
theorem exists_completion_kernel_lift (n : ℕ)
    (x : P ⧸ (I ^ n • ⊤ : Submodule R P))
    (hx : quotientToTower I F uMap hpow n x = 0) :
    ∃ z : AdicCompletion I P, completionToSections I F uMap hu hpow z = 0 ∧
      eval I P n z = x := by
  let T := presentationKernelTower I F uMap hu hpow
  have hT : ∀ k, Function.Surjective (T.map (homOfLE (Nat.le_succ k)).op) := by
    intro k a
    obtain ⟨b, hb, hab⟩ := quotientToTower_kernel_lift I F hF uMap hu hpow hsurj
      k a.val a.property
    exact ⟨⟨b, hb⟩, Subtype.ext hab⟩
  obtain ⟨s, hs⟩ := ModuleCat.sectionsEval_surjective T hT n ⟨x, hx⟩
  let z : AdicCompletion I P := ⟨fun k => (s.val (op k)).val, fun h =>
    congrArg Subtype.val (s.property (homOfLE h).op)⟩
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.ext
    funext j
    exact (s.val j).property
  · exact congrArg Subtype.val hs

include hF hu hpow hsurj in
/-- The precise projection kernel is the original ideal-power multiple in the
native inverse-limit module. This is stronger than just surjectivity. -/
theorem sectionsEval_ker_eq_of_presentation (hI : I.FG) (n : ℕ) :
    (ModuleCat.sectionsEval F n).ker =
      I ^ n • (⊤ : Submodule R (ModuleCat.sectionsSubmodule F)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy⟩ := completionToSections_surjective_of_compatibleSystem
      I F hF uMap hu hpow hsurj x
    have hq : quotientToTower I F uMap hpow n (eval I P n y) = 0 := by
      have hp := congrArg (ModuleCat.sectionsEval F n) hy
      exact hp.trans hx
    obtain ⟨z, hz, hn⟩ := exists_completion_kernel_lift I F hF uMap hu hpow hsurj n _ hq
    have hd : y - z ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I P)) := by
      rw [pow_smul_top_eq_ker_eval (M := P) hI]
      change eval I P n (y - z) = 0
      rw [map_sub, hn, sub_self]
    have hm : completionToSections I F uMap hu hpow (y - z) ∈
        I ^ n • (⊤ : Submodule R (ModuleCat.sectionsSubmodule F)) := by
      have ht := Submodule.mem_map_of_mem (f := completionToSections I F uMap hu hpow) hd
      rw [Submodule.map_smul''] at ht
      exact Submodule.smul_mono le_rfl le_top ht
    rwa [map_sub, hy, hz, sub_zero] at hm
  · apply Submodule.smul_le.mpr
    intro a ha x _
    change ModuleCat.sectionsEval F n (a • x) = 0
    rw [map_smul]
    exact hF.annihilated n ⟨a, ha⟩ _

end AdicCompletion
