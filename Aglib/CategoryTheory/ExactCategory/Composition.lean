/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.BaseChange
/-! # Kernels and cokernels of composites of admissible maps

The relevant kernel is a pullback, and the relevant cokernel a pushout.
These formulas use only the exact-category axioms.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

lemma composite_deflation_conflation {X Y Z A B : C}
    {i : A ⟶ X} {p : X ⟶ Y} {j : B ⟶ Y} {q : Y ⟶ Z}
    {hi : i ≫ p = 0} {hj : j ≫ q = 0}
    (hS : E.conflation (ShortComplex.mk i p hi))
    (hT : E.conflation (ShortComplex.mk j q hj)) [HasPullback p j] :
    E.conflation (ShortComplex.mk (pullback.fst p j) (p ≫ q) (by
      rw [← Category.assoc, pullback.condition, Category.assoc, hj, comp_zero])) := by
  let hk := E.kernel (ShortComplex.mk j q hj) hT
  let : Mono j := Fork.IsLimit.mono hk
  apply E.conflation_of_isKernel _ _
    (E.deflation_comp p q (E.deflation_of_conflation hS) (E.deflation_of_conflation hT))
  refine KernelFork.IsLimit.ofι _ _ (fun {W} a ha =>
    pullback.lift a (hk.lift (KernelFork.ofι (a ≫ p) (by simpa only [Category.assoc] using ha)))
      (by simpa using (hk.fac
        (KernelFork.ofι (a ≫ p) (by simpa only [Category.assoc] using ha))
        WalkingParallelPair.zero).symm)) (fun _ _ => by simp) ?_
  intro W a ha m hm
  apply pullback.hom_ext
  · simpa using hm
  · apply (cancel_mono j).1
    simp only [Category.assoc, pullback.lift_snd]
    rw [← pullback.condition, ← Category.assoc, hm]
    exact (hk.fac (KernelFork.ofι (a ≫ p) (by simpa only [Category.assoc] using ha))
      WalkingParallelPair.zero).symm

lemma composite_inflation_conflation {X Y Z A B : C}
    {i : X ⟶ Y} {p : Y ⟶ A} {j : Y ⟶ Z} {q : Z ⟶ B}
    {hi : i ≫ p = 0} {hj : j ≫ q = 0}
    (hS : E.conflation (ShortComplex.mk i p hi))
    (hT : E.conflation (ShortComplex.mk j q hj)) [HasPushout j p] :
    E.conflation (ShortComplex.mk (i ≫ j) (pushout.inl j p) (by
      rw [Category.assoc, pushout.condition, ← Category.assoc, hi, zero_comp])) := by
  let hc := E.cokernel (ShortComplex.mk i p hi) hS
  let : Epi p := Cofork.IsColimit.epi hc
  apply E.conflation_of_inflation_of_isCokernel
    (E.inflation_comp i j (E.inflation_of_conflation hS) (E.inflation_of_conflation hT))
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {W} a ha =>
    pushout.desc a (hc.desc (CokernelCofork.ofπ (j ≫ a) (by simpa only [Category.assoc] using ha)))
      (by simpa using (hc.fac
        (CokernelCofork.ofπ (j ≫ a) (by simpa only [Category.assoc] using ha))
        WalkingParallelPair.one).symm)) (fun _ _ => by simp) ?_
  intro W a ha m hm
  apply pushout.hom_ext
  · simpa using hm
  · apply (cancel_epi p).1
    simp only [← Category.assoc, pushout.inr_desc]
    trans j ≫ a
    · calc
        (p ≫ pushout.inr j p) ≫ m = (j ≫ pushout.inl j p) ≫ m :=
          congrArg (fun k => k ≫ m) pushout.condition.symm
        _ = j ≫ a := by rw [Category.assoc, hm]
    exact (hc.fac (CokernelCofork.ofπ (j ≫ a) (by simpa only [Category.assoc] using ha))
      WalkingParallelPair.one).symm

end CategoryTheory.ExactCategory.ExactStructure
