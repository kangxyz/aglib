/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Descent.Bind
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Binary descent data from one overlap isomorphism

For two monomorphisms into the same object, one isomorphism on their actual
pullback determines full native descent data. Repeated indices use identity
maps; the two nontrivial triple-index equations are the original inverse
identities. The cover and effectivity conditions belong to the consumer.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Opposite CategoryTheory.Limits

namespace CategoryTheory.Pseudofunctor.BinaryDescent

open LocallyDiscreteOpToCat

universe t v v' u u'
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {S X₀ X₁ W : C} (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S)
  (p₀ : W ⟶ X₀) (p₁ : W ⟶ X₁) (h : IsPullback p₀ p₁ f₀ f₁)
  (A : F.obj (.mk (op X₀))) (B : F.obj (.mk (op X₁)))
  (e : (F.map p₀.op.toLoc).toFunctor.obj A ≅ (F.map p₁.op.toLoc).toFunctor.obj B)

/-- The two original objects, with a freely chosen index universe. -/
def family : ULift.{t} Bool → C
  | ⟨false⟩ => X₀
  | ⟨true⟩ => X₁

/-- The original two arrows as one binary family. -/
def arrows (i : ULift.{t} Bool) : family (X₀ := X₀) (X₁ := X₁) i ⟶ S :=
  match i with
  | ⟨false⟩ => f₀
  | ⟨true⟩ => f₁

/-- The specified local objects on the original binary family. -/
def localObject (i : ULift.{t} Bool) : F.obj (.mk (op (family (X₀ := X₀) (X₁ := X₁) i))) :=
  match i with
  | ⟨false⟩ => A
  | ⟨true⟩ => B

/-- The original overlap isomorphism pulled back to any common test object. -/
def crossIso {Y : C} (a : Y ⟶ X₀) (b : Y ⟶ X₁) (hab : a ≫ f₀ = b ≫ f₁) :
    (F.map a.op.toLoc).toFunctor.obj A ≅ (F.map b.op.toLoc).toFunctor.obj B where
  hom := pullHom e.hom (h.lift a b hab) a b
  inv := pullHom e.inv (h.lift a b hab) b a
  hom_inv_id := by
    simp [pullHom, Category.assoc]
  inv_hom_id := by
    simp [pullHom, Category.assoc]

/-- Pulling the forward overlap arrow back again gives the original forward
overlap arrow on the new test object. -/
theorem pull_crossIso_hom {Y Y' : C} (a : Y ⟶ X₀) (b : Y ⟶ X₁)
    (hab : a ≫ f₀ = b ≫ f₁) (g : Y' ⟶ Y) (a' : Y' ⟶ X₀) (b' : Y' ⟶ X₁)
    (ha : g ≫ a = a') (hb : g ≫ b = b') (hab' : a' ≫ f₀ = b' ≫ f₁) :
    pullHom (crossIso F f₀ f₁ p₀ p₁ h A B e a b hab).hom g a' b' ha hb =
      (crossIso F f₀ f₁ p₀ p₁ h A B e a' b' hab').hom := by
  dsimp [crossIso]
  rw [pullHom_pullHom]
  have hh : g ≫ h.lift a b hab = h.lift a' b' hab' := by
    apply h.hom_ext <;> simp [Category.assoc, ha, hb]
  exact pullHom_congr_left e.hom hh _ _ _ _

/-- The reverse overlap arrow has the same actual pullback compatibility. -/
theorem pull_crossIso_inv {Y Y' : C} (a : Y ⟶ X₀) (b : Y ⟶ X₁)
    (hab : a ≫ f₀ = b ≫ f₁) (g : Y' ⟶ Y) (a' : Y' ⟶ X₀) (b' : Y' ⟶ X₁)
    (ha : g ≫ a = a') (hb : g ≫ b = b') (hab' : a' ≫ f₀ = b' ≫ f₁) :
    pullHom (crossIso F f₀ f₁ p₀ p₁ h A B e a b hab).inv g b' a' hb ha =
      (crossIso F f₀ f₁ p₀ p₁ h A B e a' b' hab').inv := by
  dsimp [crossIso]
  rw [pullHom_pullHom]
  have hh : g ≫ h.lift a b hab = h.lift a' b' hab' := by
    apply h.hom_ext <;> simp [Category.assoc, ha, hb]
  exact pullHom_congr_left e.inv hh _ _ _ _

variable [Mono f₀] [Mono f₁]

/-- The two cross arrows and identity arrows, with all original test maps. -/
def comparison {Y : C} (q : Y ⟶ S) {i j : ULift.{t} Bool}
    (a : Y ⟶ family (X₀ := X₀) (X₁ := X₁) i)
    (b : Y ⟶ family (X₀ := X₀) (X₁ := X₁) j)
    (ha : a ≫ arrows f₀ f₁ i = q) (hb : b ≫ arrows f₀ f₁ j = q) :
    (F.map a.op.toLoc).toFunctor.obj (localObject F A B i) ⟶
      (F.map b.op.toLoc).toFunctor.obj (localObject F A B j) := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  cases i <;> cases j
  · have hab : a = b := (cancel_mono f₀).mp (ha.trans hb.symm)
    subst b
    exact 𝟙 _
  · exact (crossIso F f₀ f₁ p₀ p₁ h A B e a b (ha.trans hb.symm)).hom
  · exact (crossIso F f₀ f₁ p₀ p₁ h A B e b a (hb.trans ha.symm)).inv
  · have hab : a = b := (cancel_mono f₁).mp (ha.trans hb.symm)
    subst b
    exact 𝟙 _

/-- One specified isomorphism on a binary overlap supplies genuine native
descent data, with no additional cocycle or effectivity premise. -/
def descentData : F.DescentData (fun i : ULift.{t} Bool => arrows f₀ f₁ i) where
  obj := localObject F A B
  hom Y q i j a b ha hb := comparison F f₀ f₁ p₀ p₁ h A B e q a b ha hb
  pullHom_hom Y' Y g q q' hq i j a b ha hb a' b' ha' hb' := by
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    cases i <;> cases j <;> dsimp only [family, arrows, localObject] at *
    · have hab : a = b := (cancel_mono f₀).mp (ha.trans hb.symm)
      subst b
      subst a' b'
      change pullHom (𝟙 ((F.map a.op.toLoc).toFunctor.obj A)) g (g ≫ a) (g ≫ a) rfl rfl = 𝟙 _
      exact pullHom_id' g (g ≫ a) rfl
    · exact pull_crossIso_hom F f₀ f₁ p₀ p₁ h A B e a b (ha.trans hb.symm)
        g a' b' ha' hb' (by
          calc
            a' ≫ f₀ = g ≫ (a ≫ f₀) :=
              (congrArg (fun z : Y' ⟶ X₀ => z ≫ f₀) ha'.symm).trans (Category.assoc _ _ _)
            _ = g ≫ (b ≫ f₁) := congrArg (fun z : Y ⟶ S => g ≫ z) (ha.trans hb.symm)
            _ = b' ≫ f₁ := (Category.assoc _ _ _).symm.trans
              (congrArg (fun z : Y' ⟶ X₁ => z ≫ f₁) hb'))
    · exact pull_crossIso_inv F f₀ f₁ p₀ p₁ h A B e b a (hb.trans ha.symm)
        g b' a' hb' ha' (by
          calc
            b' ≫ f₀ = g ≫ (b ≫ f₀) :=
              (congrArg (fun z : Y' ⟶ X₀ => z ≫ f₀) hb'.symm).trans (Category.assoc _ _ _)
            _ = g ≫ (a ≫ f₁) := congrArg (fun z : Y ⟶ S => g ≫ z) (hb.trans ha.symm)
            _ = a' ≫ f₁ := (Category.assoc _ _ _).symm.trans
              (congrArg (fun z : Y' ⟶ X₁ => z ≫ f₁) ha'))
    · have hab : a = b := (cancel_mono f₁).mp (ha.trans hb.symm)
      subst b
      subst a' b'
      change pullHom (𝟙 ((F.map a.op.toLoc).toFunctor.obj B)) g (g ≫ a) (g ≫ a) rfl rfl = 𝟙 _
      exact pullHom_id' g (g ≫ a) rfl
  hom_self Y q i a ha := by
    rcases i with ⟨i⟩
    cases i <;> simp [comparison]
  hom_comp Y q i j k a b c ha hb hc := by
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    rcases k with ⟨k⟩
    cases i <;> cases j <;> cases k
    · have hab : a = b := (cancel_mono f₀).mp (ha.trans hb.symm)
      have hac : a = c := (cancel_mono f₀).mp (ha.trans hc.symm)
      subst b c
      simp [comparison]
    · have hab : a = b := (cancel_mono f₀).mp (ha.trans hb.symm)
      subst b
      simp [comparison]
    · have hac : a = c := (cancel_mono f₀).mp (ha.trans hc.symm)
      subst c
      simp [comparison]
    · have hbc : b = c := (cancel_mono f₁).mp (hb.trans hc.symm)
      subst c
      simp [comparison]
    · have hbc : b = c := (cancel_mono f₀).mp (hb.trans hc.symm)
      subst c
      simp [comparison]
    · have hac : a = c := (cancel_mono f₁).mp (ha.trans hc.symm)
      subst c
      simp [comparison]
    · have hab : a = b := (cancel_mono f₁).mp (ha.trans hb.symm)
      subst b
      simp [comparison]
    · have hab : a = b := (cancel_mono f₁).mp (ha.trans hb.symm)
      have hac : a = c := (cancel_mono f₁).mp (ha.trans hc.symm)
      subst b c
      simp [comparison]

end CategoryTheory.Pseudofunctor.BinaryDescent
