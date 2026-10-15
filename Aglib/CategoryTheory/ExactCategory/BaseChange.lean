/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Functor
/-!
# Actual base changes of exact-category conflations

Pullback of a deflation retains its original kernel object, and pushout of an
inflation retains its original cokernel object. Both assertions are proved
from actual universal properties and the exact axioms, without abelianness.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Any chosen cokernel of an admissible inclusion belongs to the exact
structure, by uniqueness of cokernels. -/
lemma conflation_of_inflation_of_isCokernel {S : ShortComplex C}
    (hf : E.inflation S.f) (hg : IsColimit (CokernelCofork.ofπ S.g S.zero)) :
    E.conflation S := by
  obtain ⟨Z, p, hp, hT⟩ := hf
  let hTg := E.cokernel (ShortComplex.mk S.f p hp) hT
  let e := hTg.coconePointUniqueUpToIso hg
  let eS : ShortComplex.mk S.f p hp ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by
      simpa using (hTg.comp_coconePointUniqueUpToIso_hom hg WalkingParallelPair.one).symm)
  exact E.iso_closed eS hT

/-- The biproduct inclusions are admissible in every exact structure. -/
lemma inflation_biprod_inl (X Y : C) : E.inflation (biprod.inl : X ⟶ X ⊞ Y) := by
  have h : IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr := by
    have h := IsPushout.of_is_coproduct (BinaryBiproduct.isColimit X Y)
      (isZero_zero C).isInitial
    change IsPushout ((isZero_zero C).isInitial.to X) ((isZero_zero C).isInitial.to Y)
      (biprod.inl : X ⟶ X ⊞ Y) biprod.inr at h
    have hX : (isZero_zero C).isInitial.to X = (0 : 0 ⟶ X) := Subsingleton.elim _ _
    have hY : (isZero_zero C).isInitial.to Y = (0 : 0 ⟶ Y) := Subsingleton.elim _ _
    simpa only [hX, hY] using h
  exact E.inflation.of_isPushout h (E.inflation_zero Y)

/-- The second biproduct inclusion is admissible as well. -/
lemma inflation_biprod_inr (X Y : C) : E.inflation (biprod.inr : Y ⟶ X ⊞ Y) := by
  have h : IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr := by
    have h := IsPushout.of_is_coproduct (BinaryBiproduct.isColimit X Y)
      (isZero_zero C).isInitial
    change IsPushout ((isZero_zero C).isInitial.to X) ((isZero_zero C).isInitial.to Y)
      (biprod.inl : X ⟶ X ⊞ Y) biprod.inr at h
    have hX : (isZero_zero C).isInitial.to X = (0 : 0 ⟶ X) := Subsingleton.elim _ _
    have hY : (isZero_zero C).isInitial.to Y = (0 : 0 ⟶ Y) := Subsingleton.elim _ _
    simpa only [hX, hY] using h
  exact E.inflation.of_isPushout h.flip (E.inflation_zero X)

/-- The standard split short complex is a conflation in every exact category. -/
lemma conflation_biprod_inl_snd (X Y : C) :
    E.conflation (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.snd (by simp)) :=
  E.conflation_of_inflation_of_isCokernel (E.inflation_biprod_inl X Y)
    (biprod.isCokernelInlCokernelFork X Y)

/-- The reverse-order split short complex is also a conflation. -/
lemma conflation_biprod_inr_fst (X Y : C) :
    E.conflation (ShortComplex.mk (biprod.inr : Y ⟶ X ⊞ Y) biprod.fst (by simp)) :=
  E.conflation_of_inflation_of_isCokernel (E.inflation_biprod_inr X Y)
    (biprod.isCokernelInrCokernelFork X Y)

/-- Base change of a conflation, retaining its kernel object. -/
abbrev pullbackConflation {S : ShortComplex C} (f : C) (g : f ⟶ S.X₃)
    [HasPullback S.g g] : ShortComplex C :=
  ShortComplex.mk (pullback.lift (f := S.g) (g := g) S.f 0 (by simp [S.zero])) (pullback.snd S.g g)
    (by simp)

lemma pullbackConflation_mem {S : ShortComplex C} (hS : E.conflation S)
    {T : C} (g : T ⟶ S.X₃) [HasPullback S.g g] :
    E.conflation (pullbackConflation T g) := by
  let hk := E.kernel S hS
  let : Mono S.f := Fork.IsLimit.mono hk
  apply E.conflation_of_isKernel _ _
    (E.deflation.pullback_snd S.g g (E.deflation_of_conflation hS))
  refine KernelFork.IsLimit.ofι _ _
    (fun {W} a ha => hk.lift (KernelFork.ofι (a ≫ pullback.fst S.g g) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change a ≫ pullback.snd S.g g = 0 at ha
      simp [ha]))) ?_ ?_
  · intro W a ha
    apply pullback.hom_ext
    · simpa using hk.fac (KernelFork.ofι (a ≫ pullback.fst S.g g) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change a ≫ pullback.snd S.g g = 0 at ha
        simp [ha])) WalkingParallelPair.zero
    · simpa using ha.symm
  · intro W a ha m hm
    apply (cancel_mono S.f).1
    calc
      m ≫ S.f = a ≫ pullback.fst S.g g := by
        simpa using congrArg (fun k => k ≫ pullback.fst S.g g) hm
      _ = _ := by
        symm
        exact hk.fac (KernelFork.ofι (a ≫ pullback.fst S.g g) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          simp [ha])) WalkingParallelPair.zero

/-- Cobase change of a conflation, retaining its cokernel object. -/
abbrev pushoutConflation {S : ShortComplex C} (T : C) (g : S.X₁ ⟶ T)
    [HasPushout S.f g] : ShortComplex C :=
  ShortComplex.mk (pushout.inr S.f g) (pushout.desc (f := S.f) (g := g) S.g 0 (by simp [S.zero]))
    (by simp)

lemma pushoutConflation_mem {S : ShortComplex C} (hS : E.conflation S)
    {T : C} (g : S.X₁ ⟶ T) [HasPushout S.f g] :
    E.conflation (pushoutConflation T g) := by
  let hc := E.cokernel S hS
  let : Epi S.g := Cofork.IsColimit.epi hc
  apply E.conflation_of_inflation_of_isCokernel
    (E.inflation.pushout_inr S.f g (E.inflation_of_conflation hS))
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {W} a ha => hc.desc (CokernelCofork.ofπ (pushout.inl S.f g ≫ a) (by
      rw [← Category.assoc, pushout.condition, Category.assoc]
      change pushout.inr S.f g ≫ a = 0 at ha
      simp [ha]))) ?_ ?_
  · intro W a ha
    apply pushout.hom_ext
    · simpa using hc.fac (CokernelCofork.ofπ (pushout.inl S.f g ≫ a) (by
        rw [← Category.assoc, pushout.condition, Category.assoc]
        change pushout.inr S.f g ≫ a = 0 at ha
        simp [ha])) WalkingParallelPair.one
    · simpa using ha.symm
  · intro W a ha m hm
    apply (cancel_epi S.g).1
    calc
      S.g ≫ m = pushout.inl S.f g ≫ a := by
        simpa using congrArg (fun k => pushout.inl S.f g ≫ k) hm
      _ = _ := by
        symm
        exact hc.fac (CokernelCofork.ofπ (pushout.inl S.f g ≫ a) (by
          rw [← Category.assoc, pushout.condition, Category.assoc]
          simp [ha])) WalkingParallelPair.one


end CategoryTheory.ExactCategory.ExactStructure
