/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.FinitePresentation.Generators
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare

/-! # Original scalar-quotient generator maps and binary covering sections

The maps are induced from the original free-abelian representable maps by
the original cokernel. Binary sheaf gluing is used at the original value
universe, with the native covering and original restriction maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.TorsionFinitePresentation.FiniteCover

universe t v u w w'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

/-- The map induced by the original free-representable map on its original scalar cokernel. -/
def freeMap (n : ℕ) {U V : C} (f : U ⟶ V) :
    freeZModRepresentable.{t} J n U ⟶ freeZModRepresentable.{t} J n V :=
  cokernel.map _ _ ((Hypercohomology.freeAbelianSheafFunctor.{t} J).map f)
    ((Hypercohomology.freeAbelianSheafFunctor.{t} J).map f) (by simp)

/-- The quotient map records the literal free-representable inclusion. -/
@[reassoc]
theorem π_freeMap (n : ℕ) {U V : C} (f : U ⟶ V) :
    freeZModRepresentableπ.{t} J n U ≫ freeMap J n f =
      (Hypercohomology.freeAbelianSheafFunctor.{t} J).map f ≫
        freeZModRepresentableπ.{t} J n V := by
  exact cokernel.π_desc _ _ _

theorem freeMap_id (n : ℕ) (U : C) : freeMap.{t} J n (𝟙 U) = 𝟙 _ := by
  apply (cancel_epi (freeZModRepresentableπ.{t} J n U)).mp
  rw [π_freeMap, (Hypercohomology.freeAbelianSheafFunctor.{t} J).map_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem freeMap_comp (n : ℕ) {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    freeMap.{t} J n (f ≫ g) = freeMap J n f ≫ freeMap J n g := by
  apply (cancel_epi (freeZModRepresentableπ.{t} J n U)).mp
  rw [π_freeMap, ← Category.assoc, π_freeMap, Category.assoc, π_freeMap,
    (Hypercohomology.freeAbelianSheafFunctor.{t} J).map_comp, Category.assoc]

/-- The actual original generators, functorially in their original representing objects. -/
def freeFunctor (n : ℕ) : C ⥤ Sheaf J AddCommGrpCat.{max v t} where
  obj U := freeZModRepresentable.{t} J n U
  map f := freeMap J n f
  map_id U := freeMap_id J n U
  map_comp f g := freeMap_comp J n f g

/-- Evaluation of the actual integer-free map is original restriction of sections. -/
theorem freeAbelian_sections_naturality_left {U V : C} (f : U ⟶ V)
    (F : Sheaf J AddCommGrpCat.{max v t}) (b : Hypercohomology.freeAbelianSheaf.{t} J V ⟶ F) :
    Hypercohomology.sectionsEquiv J U F
        ((Hypercohomology.freeAbelianSheafFunctor.{t} J).map f ≫ b) =
      F.obj.map f.op (Hypercohomology.sectionsEquiv J V F b) := by
  let P : Cᵒᵖ ⥤ Type (max v t) := uliftYoneda.{t}.obj U
  let Q : Cᵒᵖ ⥤ Type (max v t) := uliftYoneda.{t}.obj V
  let K : (Cᵒᵖ ⥤ Type (max v t)) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max v t}) :=
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free
  let q : P ⟶ Q := uliftYoneda.{t}.map f
  let b₀ : (presheafToSheaf J AddCommGrpCat.{max v t}).obj (K.obj Q) ⟶ F := b
  let a : K.obj Q ⟶ F.obj :=
    (sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv (K.obj Q) F b₀
  let r : Q ⟶ F.obj ⋙ forget AddCommGrpCat.{max v t} :=
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv Q F.obj a
  have h₀ : (sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv (K.obj P) F
      ((presheafToSheaf J AddCommGrpCat.{max v t}).map (K.map q) ≫ b₀) = K.map q ≫ a :=
    (sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv_naturality_left (K.map q) b₀
  have h₁ : (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv P F.obj (K.map q ≫ a) = q ≫ r :=
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left q a
  have h := (congrArg (fun (z : K.obj P ⟶ F.obj) =>
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv P F.obj z) h₀).trans h₁
  have h' := congrArg
    (fun (z : P ⟶ F.obj ⋙ forget AddCommGrpCat.{max v t}) => uliftYonedaEquiv.{t} z) h
  exact h'.trans (uliftYonedaEquiv_naturality r f.op).symm

/-- Evaluation of the original mod-n inclusion is precisely the original section restriction. -/
theorem sections_naturality_left (n : ℕ) {U V : C} (f : U ⟶ V)
    (F : Sheaf J AddCommGrpCat.{max v t}) (b : freeZModRepresentable.{t} J n V ⟶ F) :
    (freeZModSectionsEquiv J n U F (freeMap J n f ≫ b)).val =
      F.obj.map f.op (freeZModSectionsEquiv J n V F b).val := by
  change Hypercohomology.sectionsEquiv J U F
      (freeZModRepresentableπ J n U ≫ (freeMap J n f ≫ b)) =
    F.obj.map f.op (Hypercohomology.sectionsEquiv J V F (freeZModRepresentableπ J n V ≫ b))
  rw [← Category.assoc, π_freeMap, Category.assoc]
  exact freeAbelian_sections_naturality_left J f F _

section BinarySections

omit [HasSheafify J AddCommGrpCat.{max v t}]

variable (sq : Square C) [Mono sq.f₂₄] [Mono sq.f₃₄]
  (hp : sq.IsPullback) (hcover : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄)

include hp hcover

/-- The original binary-cover argument works at every coefficient universe.
This is the native Mayer--Vietoris amalgamation argument without resizing values. -/
theorem sheaf_isPullback {A : Type w} [Category.{w'} A] (F : Sheaf J A) :
    (sq.op.map F.obj).IsPullback := by
  apply Square.IsPullback.mk
  refine PullbackCone.IsLimit.mk _
    (fun s => F.property.amalgamateOfArrows _ hcover
      (fun j => WalkingPair.casesOn j s.fst s.snd)
      (fun W => by
        rintro (_ | _) (_ | _) a b fac
        · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₂₄] using fac
          rfl
        · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hp.isLimit _ _ fac
          simpa using s.condition =≫ F.obj.map φ.op
        · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hp.isLimit _ _ fac.symm
          simpa using s.condition.symm =≫ F.obj.map φ.op
        · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₃₄] using fac
          rfl)) (fun _ => ?_) (fun _ => ?_) (fun s m hm₀ hm₁ => ?_)
  · exact F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.left
  · exact F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.right
  · apply F.property.hom_ext_ofArrows _ hcover
    rintro (_ | _)
    · rw [F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.left]
      exact hm₀
    · rw [F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.right]
      exact hm₁

/-- The actual underlying section square is a pullback of original functions. -/
theorem sectionsPullback (F : Sheaf J AddCommGrpCat.{max v t}) :
    (sq.op.map (F.obj ⋙ forget AddCommGrpCat.{max v t})).IsPullback :=
  (sheaf_isPullback J sq hp hcover F).map (forget AddCommGrpCat.{max v t})

/-- Original section amalgamation on the two actual members of the cover. -/
def glue (F : Sheaf J AddCommGrpCat.{max v t})
    (s₀ : F.obj.obj (op sq.X₂)) (s₁ : F.obj.obj (op sq.X₃))
    (hs : F.obj.map sq.f₁₂.op s₀ = F.obj.map sq.f₁₃.op s₁) : F.obj.obj (op sq.X₄) :=
  (PullbackCone.IsLimit.equivPullbackObj (sectionsPullback J sq hp hcover F).isLimit).symm
    ⟨⟨s₀, s₁⟩, hs⟩

@[simp]
theorem glue_left (F : Sheaf J AddCommGrpCat.{max v t})
    (s₀ : F.obj.obj (op sq.X₂)) (s₁ : F.obj.obj (op sq.X₃))
    (hs : F.obj.map sq.f₁₂.op s₀ = F.obj.map sq.f₁₃.op s₁) :
    F.obj.map sq.f₂₄.op (glue J sq hp hcover F s₀ s₁ hs) = s₀ :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst
    (sectionsPullback J sq hp hcover F).isLimit _

@[simp]
theorem glue_right (F : Sheaf J AddCommGrpCat.{max v t})
    (s₀ : F.obj.obj (op sq.X₂)) (s₁ : F.obj.obj (op sq.X₃))
    (hs : F.obj.map sq.f₁₂.op s₀ = F.obj.map sq.f₁₃.op s₁) :
    F.obj.map sq.f₃₄.op (glue J sq hp hcover F s₀ s₁ hs) = s₁ :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd
    (sectionsPullback J sq hp hcover F).isLimit _

/-- Original restrictions detect equality of sections on the actual union. -/
theorem sections_ext (F : Sheaf J AddCommGrpCat.{max v t})
    {s t : F.obj.obj (op sq.X₄)}
    (h₀ : F.obj.map sq.f₂₄.op s = F.obj.map sq.f₂₄.op t)
    (h₁ : F.obj.map sq.f₃₄.op s = F.obj.map sq.f₃₄.op t) : s = t := by
  apply (PullbackCone.IsLimit.equivPullbackObj
    (sectionsPullback J sq hp hcover F).isLimit).injective
  ext <;> assumption

end BinarySections

end CategoryTheory.Sheaf.TorsionFinitePresentation.FiniteCover
