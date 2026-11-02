/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Elements.SheafCondition

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Yoneda

/-!
# Presheaves on `Over S` as presheaves on `C`

For a presheaf of types `P` on `Over S`, `Presieve.overSigma P` is the presheaf on `C` whose
sections over `Y` are the pairs `⟨g, s⟩` of a morphism `g : Y ⟶ S` and a section `s` of `P` over
`Over.mk g`; restriction along `t : Y' ⟶ Y` is `⟨t ≫ g, P.map (Over.homMk t).op s⟩`.

The sheaf conditions correspond:

* `Presieve.isSheafFor_of_isSheafFor_overSigma`: if `overSigma P` is a sheaf for a sieve `R` of
  `S` and `yoneda.obj S` is separated for `R`, then `P` is a sheaf for the corresponding sieve
  `(Sieve.overEquiv (Over.mk (𝟙 S))).symm R` of `Over.mk (𝟙 S)`;
* `Presieve.isSheafFor_overSigma`: if `yoneda.obj S` is a sheaf for a sieve `R` of `Y` and `P` is
  a sheaf for `(Sieve.overEquiv (Over.mk g)).symm R` for every `g : Y ⟶ S`, then `overSigma P` is
  a sheaf for `R`.

The consumer is the prestack property of a pseudofunctor (Mathlib's `Pseudofunctor.IsPrestack`
asks that the presheaves `F.presheafHom M N` on `Over S` be sheaves), which these lemmas reduce
to sheaf conditions for presheaves on `C`, where Mathlib's criteria for big sites apply.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Presieve

open Opposite

variable {C : Type u} [Category.{v} C] {S : C} (P : (Over S)ᵒᵖ ⥤ Type w)

/-- Restriction along a composite. -/
private lemma map_map_eq {A B D : Over S} (u : B ⟶ A) (c : D ⟶ B) (s : P.obj (op A)) :
    P.map c.op (P.map u.op s) = P.map (c ≫ u).op s := by
  simp

/-- Restriction along equal morphisms. -/
private lemma map_congr_hom {A B : Over S} {u v : B ⟶ A} (h : u = v) (s : P.obj (op A)) :
    P.map u.op s = P.map v.op s := by
  rw [h]

/-- Restriction along an identity. -/
private lemma map_id_eq {A : Over S} (u : A ⟶ A) (hu : u = 𝟙 A) (s : P.obj (op A)) :
    P.map u.op s = s := by
  subst hu
  simp

/-- Equality of pairs whose first components are equal. -/
private lemma sigma_over_ext {Y : C} {g₁ g₂ : Y ⟶ S} (h : g₁ = g₂)
    {s₁ : P.obj (op (Over.mk g₁))} {s₂ : P.obj (op (Over.mk g₂))}
    (hs : s₁ = P.map (Over.homMk (𝟙 Y) (by simp [h]) : Over.mk g₁ ⟶ Over.mk g₂).op s₂) :
    (⟨g₁, s₁⟩ : Σ g : Y ⟶ S, P.obj (op (Over.mk g))) = ⟨g₂, s₂⟩ := by
  subst h hs
  rw [map_id_eq P _ (by ext; simp)]

/-- The presheaf on `C` of pairs of a morphism `g : Y ⟶ S` and a section of `P` over
`Over.mk g`. -/
@[simps obj]
def overSigma : Cᵒᵖ ⥤ Type (max v w) where
  obj Y := Σ g : Y.unop ⟶ S, P.obj (op (Over.mk g))
  map {Y Y'} t := ↾fun x ↦ ⟨t.unop ≫ x.1,
    P.map (Over.homMk t.unop rfl : Over.mk (t.unop ≫ x.1) ⟶ Over.mk x.1).op x.2⟩
  map_id Y := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨g, s⟩ := x
    exact sigma_over_ext P (Category.id_comp g) rfl
  map_comp {Y Y' Y''} t t' := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨g, s⟩ := x
    refine sigma_over_ext P (Category.assoc _ _ _) ?_
    change _ = P.map _ (P.map _ (P.map _ s))
    rw [map_map_eq, map_map_eq]
    exact map_congr_hom P (by ext; simp) s

lemma overSigma_map_apply {Y Y' : Cᵒᵖ} (t : Y ⟶ Y') (x : (overSigma P).obj Y) :
    (overSigma P).map t x =
      ⟨t.unop ≫ x.1, P.map (Over.homMk t.unop rfl : Over.mk (t.unop ≫ x.1) ⟶ Over.mk x.1).op x.2⟩ :=
  rfl

/-- Restricting the second components of equal pairs to an object of `Over S` over `Y`. -/
private lemma map_homMk_eq_of_overSigma_eq {Y : C} {g₁ g₂ : Y ⟶ S}
    {s₁ : P.obj (op (Over.mk g₁))} {s₂ : P.obj (op (Over.mk g₂))}
    (h : (⟨g₁, s₁⟩ : Σ g : Y ⟶ S, P.obj (op (Over.mk g))) = ⟨g₂, s₂⟩) (Z : Over S)
    (a : Z.left ⟶ Y) (h₁ : a ≫ g₁ = Z.hom) (h₂ : a ≫ g₂ = Z.hom) :
    P.map (Over.homMk a h₁ : Z ⟶ Over.mk g₁).op s₁ =
      P.map (Over.homMk a h₂ : Z ⟶ Over.mk g₂).op s₂ := by
  cases h
  rfl

/-- Restriction along `c : W ⟶ Z` of a section transported along `Over.homMk (𝟙 _)`. -/
private lemma map_map_homMk_id {Z W : Over S} (c : W ⟶ Z) {k : Z.left ⟶ S}
    (hk : 𝟙 Z.left ≫ k = Z.hom)
    (s : P.obj (op (Over.mk k))) (h : 𝟙 W.left ≫ c.left ≫ k = W.hom) :
    P.map c.op (P.map (Over.homMk (𝟙 Z.left) hk : Z ⟶ Over.mk k).op s) =
      P.map (Over.homMk (𝟙 W.left) h : W ⟶ Over.mk (c.left ≫ k)).op
        (P.map (Over.homMk c.left rfl : Over.mk (c.left ≫ k) ⟶ Over.mk k).op s) := by
  rw [map_map_eq, map_map_eq]
  exact map_congr_hom P (by ext; simp) s

/-- If `overSigma P` is a sheaf for a sieve `R` of `S` and `yoneda.obj S` is separated for `R`,
then `P` is a sheaf for the corresponding sieve of `Over.mk (𝟙 S)`. -/
lemma isSheafFor_of_isSheafFor_overSigma {R : Sieve S}
    (hR : IsSheafFor (overSigma P) R.arrows) (hY : IsSeparatedFor (yoneda.obj S) R.arrows) :
    IsSheafFor P ((Sieve.overEquiv (Over.mk (𝟙 S))).symm R).arrows := by
  intro x hx
  let y : FamilyOfElements (overSigma P) R.arrows := fun Z t ht ↦
    ⟨t, x (Over.homMk t : Over.mk t ⟶ Over.mk (𝟙 S))
      ((Sieve.overEquiv_symm_iff _ _).2 ht)⟩
  have hy : y.Compatible := by
    intro Z₁ Z₂ W a b t₁ t₂ h₁ h₂ fac
    refine (overSigma_map_apply P _ _).trans (Eq.trans ?_ (overSigma_map_apply P _ _).symm)
    refine sigma_over_ext P fac ?_
    dsimp only [y]
    rw [map_map_eq]
    exact hx (Over.homMk a rfl : Over.mk (a ≫ t₁) ⟶ Over.mk t₁)
      ((Over.homMk (𝟙 W) (by simp [fac]) : Over.mk (a ≫ t₁) ⟶ Over.mk (b ≫ t₂)) ≫
        (Over.homMk b rfl : Over.mk (b ≫ t₂) ⟶ Over.mk t₂)) _ _ (by ext; simp [fac])
  obtain ⟨⟨g, φ⟩, hz, hzu⟩ := hR y hy
  obtain rfl : g = 𝟙 S := by
    refine hY (fun Z t _ ↦ t) g (𝟙 S) (fun Z t ht ↦ ?_) (fun Z t ht ↦ by simp)
    exact congrArg Sigma.fst (hz t ht)
  refine ⟨φ, fun Z b hb ↦ ?_, fun φ' hφ' ↦ ?_⟩
  · have hb' : R b.left := (Sieve.overEquiv_symm_iff _ _).1 hb
    have hw : b.left = Z.hom := by simpa using Over.w b
    have hzb : (⟨b.left ≫ 𝟙 S, P.map (Over.homMk b.left rfl :
        Over.mk (b.left ≫ 𝟙 S) ⟶ Over.mk (𝟙 S)).op φ⟩ : Σ g : Z.left ⟶ S, P.obj (op (Over.mk g))) =
        ⟨b.left, x (Over.homMk b.left : Over.mk b.left ⟶ Over.mk (𝟙 S))
          ((Sieve.overEquiv_symm_iff _ _).2 hb')⟩ := hz b.left hb'
    have := map_homMk_eq_of_overSigma_eq P hzb Z (𝟙 _) (by simp [hw]) (by simp [hw])
    rw [map_map_eq] at this
    have e : (Over.homMk (𝟙 Z.left) (by simp [hw]) : Z ⟶ Over.mk (b.left ≫ 𝟙 S)) ≫
        (Over.homMk b.left rfl : Over.mk (b.left ≫ 𝟙 S) ⟶ Over.mk (𝟙 S)) = b := by
      ext; simp
    rw [e] at this
    rw [this]
    have e' : (Over.homMk (𝟙 Z.left) (by simp [hw]) : Z ⟶ Over.mk b.left) ≫
        (Over.homMk b.left : Over.mk b.left ⟶ Over.mk (𝟙 S)) = b := by
      ext; simp
    rw [hx (Over.homMk (𝟙 Z.left) (by simp [hw]) : Z ⟶ Over.mk b.left) (𝟙 Z)
      ((Sieve.overEquiv_symm_iff _ _).2 hb') hb (by rw [e', Category.id_comp]),
      map_id_eq P _ (by simp)]
  · have := hzu ⟨𝟙 S, φ'⟩ (fun Z t ht ↦ by
      refine (overSigma_map_apply P _ _).trans ?_
      refine sigma_over_ext P (Category.comp_id t) ?_
      dsimp only [y]
      rw [← hφ' _ ((Sieve.overEquiv_symm_iff _ _).2 ht), map_map_eq]
      exact map_congr_hom P (by ext; simp) φ')
    exact eq_of_heq (Sigma.mk.inj this).2

/-- If `yoneda.obj S` is a sheaf for a sieve `R` of `Y` and `P` is a sheaf for the corresponding
sieve of `Over.mk g` for every `g : Y ⟶ S`, then `overSigma P` is a sheaf for `R`. -/
lemma isSheafFor_overSigma {Y : C} {R : Sieve Y} (hY : IsSheafFor (yoneda.obj S) R.arrows)
    (hP : ∀ g : Y ⟶ S, IsSheafFor P ((Sieve.overEquiv (Over.mk g)).symm R).arrows) :
    IsSheafFor (overSigma P) R.arrows := by
  let Q := (Presheaf.ElementsSite.representedElementsToOver S).op ⋙ P
  apply Presheaf.ElementsSite.isSheafFor_of_sigma_equiv (yoneda.obj S) Q
    (overSigma P) (fun Y => Equiv.refl _) ?_ hY ?_
  · intro Y Z f z
    rfl
  · intro g
    exact Presheaf.ElementsSite.representedElements_isSheafFor S P g (hP g)

end CategoryTheory.Presieve
