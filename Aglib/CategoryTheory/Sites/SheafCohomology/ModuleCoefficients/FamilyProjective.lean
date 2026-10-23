/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.CechFamily
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Projectivity of free families of representables

The free abelian presheaf on a family of representables is projective.
The proof lifts the section at each representing object along an actual
pointwise epimorphism and extends it by the original free adjunction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presheaf.Cech

universe w h c

variable {C : Type c} [Category.{h} C] {ι : Type w} (U : ι → C)

/-- Yoneda's lemma for the explicit family presheaf. -/
def familyHomEquiv (A : Cᵒᵖ ⥤ Type (max w h)) :
    (familyPresheaf U ⟶ A) ≃ (∀ i, A.obj (op (U i))) where
  toFun f i := f.app (op (U i)) ⟨i, 𝟙 _⟩
  invFun s :=
    { app X := ↾fun x => A.map x.2.op (s x.1)
      naturality X Y f := by
        apply ConcreteCategory.hom_ext
        rintro ⟨i, g⟩
        change A.map (f.unop ≫ g).op (s i) = A.map f (A.map g.op (s i))
        rw [op_comp, Functor.map_comp]
        rfl }
  left_inv f := by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    rintro ⟨i, g⟩
    change A.map g.op (f.app (op (U i)) ⟨i, 𝟙 _⟩) = f.app X ⟨i, g⟩
    have h := (f.naturality_apply g.op ⟨i, 𝟙 _⟩).symm
    change A.map g.op (f.app (op (U i)) ⟨i, 𝟙 _⟩) = f.app X ⟨i, g ≫ 𝟙 _⟩ at h
    simpa only [Category.comp_id] using h
  right_inv s := by
    funext i
    change A.map (𝟙 (U i)).op (s i) = s i
    simp

/-- Free abelian natural transformations are determined by one section per component. -/
def freeFamilyHomEquiv (A : Cᵒᵖ ⥤ AddCommGrpCat.{max w h}) :
    (familyPresheaf U ⋙ AddCommGrpCat.free ⟶ A) ≃ (∀ i, A.obj (op (U i))) :=
  ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ A).trans
    (familyHomEquiv U (A ⋙ forget AddCommGrpCat))

lemma freeFamilyHomEquiv_apply (A : Cᵒᵖ ⥤ AddCommGrpCat.{max w h})
    (f : familyPresheaf U ⋙ AddCommGrpCat.free ⟶ A) (i : ι) :
    freeFamilyHomEquiv U A f i = f.app (op (U i)) (FreeAbelianGroup.of ⟨i, 𝟙 _⟩) := rfl

/-- Projectivity is proved on the original presheaf category, not on a slice restriction. -/
instance freeFamily_projective : Projective (familyPresheaf U ⋙ AddCommGrpCat.free) where
  factors {E X} f e := by
    intro he
    classical
    have hs (i : ι) : Function.Surjective (e.app (op (U i))) :=
      (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
    choose s hs using fun i => hs i (freeFamilyHomEquiv U X f i)
    refine ⟨(freeFamilyHomEquiv U E).symm s, ?_⟩
    apply (freeFamilyHomEquiv U X).injective
    funext i
    change e.app (op (U i)) (((freeFamilyHomEquiv U E).symm s).app (op (U i))
      (FreeAbelianGroup.of ⟨i, 𝟙 _⟩)) = freeFamilyHomEquiv U X f i
    have h := congrFun ((freeFamilyHomEquiv U E).apply_symm_apply s) i
    rw [freeFamilyHomEquiv_apply] at h
    rw [h]
    exact hs i

section TupleProjectivity

variable {W : C} (V : ι → Over W) [HasFiniteProducts (Over W)]

/-- The tuple/product equivalence is natural on the original site. -/
def tupleProductIso (n : ℕ) :
    tuplePresheaf (familyMap V) n ≅
      familyPresheaf (fun a : Fin (n + 1) → ι => (∏ᶜ fun i => V (a i)).left) :=
  NatIso.ofComponents (fun X => Equiv.toIso (tupleProductEquiv V n X)) (by
    intro X Y g
    apply ConcreteCategory.hom_ext
    intro t
    change tupleToProduct V (tupleRestrict (familyMap V) g t) =
      ⟨fun i => (t.2 i).1.1, g.unop ≫ (tupleProductLift V t).left⟩
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    let k : Over.mk (g.unop ≫ t.1.down) ⟶ Over.mk t.1.down := Over.homMk g.unop
    let q (j : Fin (n + 1)) : Over.mk (g.unop ≫ t.1.down) ⟶ V (t.2 j).1.1 :=
      Over.homMk (g.unop ≫ (t.2 j).1.2) (by
        rw [Category.assoc]
        exact congrArg (fun a => g.unop ≫ a) (congrArg ULift.down (t.2 j).2))
    have h : k ≫ tupleProductLift V t =
        tupleProductLift V (tupleRestrict (familyMap V) g t) := by
      change k ≫ tupleProductLift V t = Pi.lift q
      apply Pi.hom_ext
      intro i
      simp only [Category.assoc, tupleProductLift, Pi.lift_comp_π]
      apply Over.OverMorphism.ext
      rfl
    exact congrArg (fun f => f.left) h.symm)

/-- Every free tuple term of a represented family is an actual projective presheaf. -/
instance freeTuple_projective (n : ℕ) :
    Projective (tuplePresheaf (familyMap V) n ⋙ AddCommGrpCat.free) :=
  Projective.of_iso
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).mapIso
      (tupleProductIso V n).symm)
    (freeFamily_projective (fun a : Fin (n + 1) → ι => (∏ᶜ fun i => V (a i)).left))

end TupleProjectivity

end CategoryTheory.Presheaf.Cech
