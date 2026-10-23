/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Descent.Binary
public import Aglib.CategoryTheory.Sites.Descent.OfEpi

/-!
# Checking binary descent morphisms on the single overlap

Compatibility on one actual pullback implies compatibility on every test
object. For two monomorphisms, the reverse overlap follows by cancellation
of the original descent isomorphisms. Thus one square suffices to glue
local morphisms or local isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Opposite CategoryTheory.Limits

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

universe t v v' u u'
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

namespace DescentData

variable {S : C} {ι : Type t} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- A compatibility square on an actual pullback gives that same square
on every common test object, through the original descent transport. -/
theorem comm_of_pullback (D E : F.DescentData f) {i j : ι} {W : C}
    (p : W ⟶ X i) (r : W ⟶ X j) (hp : IsPullback p r (f i) (f j))
    (q₀ : W ⟶ S) (hp₀ : p ≫ f i = q₀) (hr₀ : r ≫ f j = q₀)
    (α : D.obj i ⟶ E.obj i) (β : D.obj j ⟶ E.obj j)
    (he : (F.map p.op.toLoc).toFunctor.map α ≫ E.hom q₀ p r hp₀ hr₀ =
      D.hom q₀ p r hp₀ hr₀ ≫ (F.map r.op.toLoc).toFunctor.map β)
    {Y : C} (q : Y ⟶ S) (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (F.map a.op.toLoc).toFunctor.map α ≫ E.hom q a b ha hb =
      D.hom q a b ha hb ≫ (F.map b.op.toLoc).toFunctor.map β := by
  let k := hp.lift a b (ha.trans hb.symm)
  have hk : k ≫ p = a := hp.lift_fst _ _ _
  have hl : k ≫ r = b := hp.lift_snd _ _ _
  have hq : k ≫ q₀ = q := by
    exact (congrArg (fun z : W ⟶ S => k ≫ z) hp₀.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun z : Y ⟶ X i => z ≫ f i) hk).trans ha))
  have h := congrArg (fun φ => pullHom φ k a b hk hl) he
  rw [pullHom_comp _ _ k a a b hk hk hl, pullHom_map α p k a hk,
    pullHom_comp _ _ k a b b hk hl hl, pullHom_map β r k b hl,
    D.pullHom_hom k q₀ q hq p r hp₀ hr₀ a b hk hl,
    E.pullHom_hom k q₀ q hq p r hp₀ hr₀ a b hk hl] at h
  exact h

end DescentData

namespace BinaryDescent

variable {S X₀ X₁ W : C} (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S)
  [Mono f₀] [Mono f₁] (p₀ : W ⟶ X₀) (p₁ : W ⟶ X₁)
  (h : IsPullback p₀ p₁ f₀ f₁)
  (D E : F.DescentData (fun i : ULift.{t} Bool => arrows f₀ f₁ i))
  (α : ∀ i, D.obj i ⟶ E.obj i)

/-- A square on the single nontrivial binary overlap is the entire native
compatibility condition for a family of local module morphisms. -/
theorem comm
    (he : (F.map p₀.op.toLoc).toFunctor.map (α ⟨false⟩) ≫
        E.hom (i₁ := ⟨false⟩) (i₂ := ⟨true⟩) (p₀ ≫ f₀) p₀ p₁ rfl h.w.symm =
      D.hom (i₁ := ⟨false⟩) (i₂ := ⟨true⟩) (p₀ ≫ f₀) p₀ p₁ rfl h.w.symm ≫
        (F.map p₁.op.toLoc).toFunctor.map (α ⟨true⟩))
    {Y : C} (q : Y ⟶ S) {i j : ULift.{t} Bool}
    (a : Y ⟶ family (X₀ := X₀) (X₁ := X₁) i)
    (b : Y ⟶ family (X₀ := X₀) (X₁ := X₁) j)
    (ha : a ≫ arrows f₀ f₁ i = q) (hb : b ≫ arrows f₀ f₁ j = q) :
    (F.map a.op.toLoc).toFunctor.map (α i) ≫ E.hom q a b ha hb =
      D.hom q a b ha hb ≫ (F.map b.op.toLoc).toFunctor.map (α j) := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  cases i <;> cases j
  · have hab : a = b := (cancel_mono f₀).mp (ha.trans hb.symm)
    subst b
    calc
      _ = (F.map a.op.toLoc).toFunctor.map (α ⟨false⟩) ≫ 𝟙 _ :=
        congrArg (fun z => (F.map a.op.toLoc).toFunctor.map (α ⟨false⟩) ≫ z)
          (E.hom_self q a ha)
      _ = (F.map a.op.toLoc).toFunctor.map (α ⟨false⟩) := Category.comp_id _
      _ = 𝟙 _ ≫ (F.map a.op.toLoc).toFunctor.map (α ⟨false⟩) := (Category.id_comp _).symm
      _ = _ := congrArg (fun z => z ≫ (F.map a.op.toLoc).toFunctor.map (α ⟨false⟩))
        (D.hom_self q a ha).symm
  · exact DescentData.comm_of_pullback F D E (i := ⟨false⟩) (j := ⟨true⟩)
      p₀ p₁ h (p₀ ≫ f₀) rfl h.w.symm
      (α ⟨false⟩) (α ⟨true⟩) he q a b ha hb
  · have hrev : (F.map p₁.op.toLoc).toFunctor.map (α ⟨true⟩) ≫
        E.hom (i₁ := ⟨true⟩) (i₂ := ⟨false⟩) (p₀ ≫ f₀) p₁ p₀ h.w.symm rfl =
      D.hom (i₁ := ⟨true⟩) (i₂ := ⟨false⟩) (p₀ ≫ f₀) p₁ p₀ h.w.symm rfl ≫
        (F.map p₀.op.toLoc).toFunctor.map (α ⟨false⟩) := by
      let d := D.iso (i₁ := ⟨false⟩) (i₂ := ⟨true⟩) (p₀ ≫ f₀) p₀ p₁ rfl h.w.symm
      let e := E.iso (i₁ := ⟨false⟩) (i₂ := ⟨true⟩) (p₀ ≫ f₀) p₀ p₁ rfl h.w.symm
      change (F.map p₁.op.toLoc).toFunctor.map (α ⟨true⟩) ≫ e.inv =
        d.inv ≫ (F.map p₀.op.toLoc).toFunctor.map (α ⟨false⟩)
      change (F.map p₀.op.toLoc).toFunctor.map (α ⟨false⟩) ≫ e.hom =
        d.hom ≫ (F.map p₁.op.toLoc).toFunctor.map (α ⟨true⟩) at he
      apply (cancel_mono e.hom).mp
      calc
        _ = (F.map p₁.op.toLoc).toFunctor.map (α ⟨true⟩) := by
          rw [Category.assoc, e.inv_hom_id, Category.comp_id]
        _ = d.inv ≫ (d.hom ≫ (F.map p₁.op.toLoc).toFunctor.map (α ⟨true⟩)) :=
          (d.inv_hom_id_assoc _).symm
        _ = d.inv ≫ ((F.map p₀.op.toLoc).toFunctor.map (α ⟨false⟩) ≫ e.hom) :=
          congrArg (fun z => d.inv ≫ z) he.symm
        _ = _ := (Category.assoc _ _ _).symm
    exact DescentData.comm_of_pullback F D E (i := ⟨true⟩) (j := ⟨false⟩)
      p₁ p₀ h.flip (p₀ ≫ f₀) h.w.symm rfl
      (α ⟨true⟩) (α ⟨false⟩) hrev q a b ha hb
  · have hab : a = b := (cancel_mono f₁).mp (ha.trans hb.symm)
    subst b
    calc
      _ = (F.map a.op.toLoc).toFunctor.map (α ⟨true⟩) ≫ 𝟙 _ :=
        congrArg (fun z => (F.map a.op.toLoc).toFunctor.map (α ⟨true⟩) ≫ z)
          (E.hom_self q a ha)
      _ = (F.map a.op.toLoc).toFunctor.map (α ⟨true⟩) := Category.comp_id _
      _ = 𝟙 _ ≫ (F.map a.op.toLoc).toFunctor.map (α ⟨true⟩) := (Category.id_comp _).symm
      _ = _ := congrArg (fun z => z ≫ (F.map a.op.toLoc).toFunctor.map (α ⟨true⟩))
        (D.hom_self q a ha).symm

/-- The actual descent-data isomorphism determined by two local
isomorphisms and the single original overlap square. -/
def isoMk (a : ∀ i, D.obj i ≅ E.obj i)
    (ha : (F.map p₀.op.toLoc).toFunctor.map (a ⟨false⟩).hom ≫
        E.hom (i₁ := ⟨false⟩) (i₂ := ⟨true⟩) (p₀ ≫ f₀) p₀ p₁ rfl h.w.symm =
      D.hom (i₁ := ⟨false⟩) (i₂ := ⟨true⟩) (p₀ ≫ f₀) p₀ p₁ rfl h.w.symm ≫
        (F.map p₁.op.toLoc).toFunctor.map (a ⟨true⟩).hom) : D ≅ E :=
  DescentData.isoMk a (by
    intro Y q i j b c hb hc
    exact comm F f₀ f₁ p₀ p₁ h D E (fun i => (a i).hom) ha q b c hb hc)

end BinaryDescent

end CategoryTheory.Pseudofunctor
