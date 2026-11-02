/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveSystem
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Original inverse transitions of compatible coefficient systems -/

@[expose] public noncomputable section

namespace CategoryTheory

section Mates

universe u v u' v'
variable {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
  {L₁ L₂ : C ⥤ E} {R₁ R₂ : E ⥤ C}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)

/-- Composition with a left-adjoint map corresponds to composition with its original mate. -/
lemma homEquiv_precomp_conjugate (α : L₂ ⟶ L₁) {X : C} {Y : E}
    (h : L₁.obj X ⟶ Y) :
    a₂.homEquiv X Y (α.app X ≫ h) =
      a₁.homEquiv X Y h ≫ (conjugateEquiv a₁ a₂ α).app Y := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv, Category.assoc,
    ← (conjugateEquiv a₁ a₂ α).naturality, ← Category.assoc,
    ← Adjunction.homEquiv_unit]

end Mates

namespace InjectiveSystem

universe uI vI uA vA
variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)] (D : AdjunctionData A)

/-- The left identity comparison is the mate of the actual right identity comparison. -/
def AdjunctionData.leftIdIso (i : I) : D.left (𝟙 i) ≅ 𝟭 (A i) :=
  Adjunction.leftAdjointIdIso (D.adj (𝟙 i)) (D.idIso i)

/-- The left composition comparison retains the actual right composition isomorphism. -/
def AdjunctionData.leftCompIso {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    D.left (a ≫ b) ≅ D.left a ⋙ D.left b :=
  (Adjunction.leftAdjointCompIso (D.adj a) (D.adj b) (D.adj (a ≫ b))
    (D.compIso a b).symm).symm

/-- The original transition written on the inverse-image side of the original adjunction. -/
def System.leftMap (F : System D) {i j : I} (a : i ⟶ j) :
    (D.left a).obj (F.obj i) ⟶ F.obj j :=
  ((D.adj a).homEquiv _ _).symm (F.map a)

@[simp]
lemma System.homEquiv_leftMap (F : System D) {i j : I} (a : i ⟶ j) :
    (D.adj a).homEquiv _ _ (F.leftMap D a) = F.map a :=
  Equiv.apply_symm_apply _ _

/-- The mate transition obeys the original identity comparison. -/
lemma System.leftMap_id (F : System D) (i : I) :
    F.leftMap D (𝟙 i) = (D.leftIdIso i).hom.app (F.obj i) := by
  apply ((D.adj (𝟙 i)).homEquiv _ _).injective
  rw [System.homEquiv_leftMap]
  have ht := homEquiv_precomp_conjugate Adjunction.id (D.adj (𝟙 i))
    (D.leftIdIso i).hom (𝟙 (F.obj i))
  have hm : conjugateEquiv Adjunction.id (D.adj (𝟙 i)) (D.leftIdIso i).hom =
      (D.idIso i).inv := Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _
  rw [hm] at ht
  let l : (D.left (𝟙 i)).obj (F.obj i) ⟶ F.obj i :=
    (D.leftIdIso i).hom.app (F.obj i)
  let r : F.obj i ⟶ (D.right (𝟙 i)).obj (F.obj i) :=
    (D.idIso i).inv.app (F.obj i)
  have hid : Adjunction.id.homEquiv (F.obj i) (F.obj i) (𝟙 (F.obj i)) =
      𝟙 (F.obj i) :=
    (Adjunction.homEquiv_id Adjunction.id (F.obj i)).trans
      (show Adjunction.id.unit.app (F.obj i) = 𝟙 (F.obj i) from rfl)
  have ht' : (D.adj (𝟙 i)).homEquiv _ _ (l ≫ 𝟙 (F.obj i)) =
      𝟙 (F.obj i) ≫ r := ht.trans (congrArg (· ≫ r) hid)
  rw [Category.comp_id, Category.id_comp] at ht'
  change F.map (𝟙 i) = (D.adj (𝟙 i)).homEquiv _ _ l
  rw [ht']
  apply (cancel_mono ((D.idIso i).hom.app (F.obj i))).1
  rw [F.map_id, Iso.inv_hom_id_app]
  rfl

/-- The mate transitions obey the actual composition comparison. -/
lemma System.leftMap_comp (F : System D) {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    F.leftMap D (a ≫ b) = (D.leftCompIso a b).hom.app (F.obj i) ≫
      (D.left b).map (F.leftMap D a) ≫ F.leftMap D b := by
  apply ((D.adj (a ≫ b)).homEquiv _ _).injective
  rw [System.homEquiv_leftMap]
  rw [homEquiv_precomp_conjugate ((D.adj a).comp (D.adj b))
    (D.adj (a ≫ b)) (D.leftCompIso a b).hom]
  have hm : conjugateEquiv ((D.adj a).comp (D.adj b)) (D.adj (a ≫ b))
      (D.leftCompIso a b).hom = (D.compIso a b).inv :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  rw [hm]
  have ht : ((D.adj a).comp (D.adj b)).homEquiv _ _
      ((D.left b).map (F.leftMap D a) ≫ F.leftMap D b) =
      F.map a ≫ (D.right a).map (F.map b) := by
    rw [Adjunction.comp_homEquiv]
    change (D.adj a).homEquiv _ _ ((D.adj b).homEquiv _ _
      ((D.left b).map (F.leftMap D a) ≫ F.leftMap D b)) = _
    rw [Adjunction.homEquiv_naturality_left, System.homEquiv_leftMap,
      Adjunction.homEquiv_naturality_right, System.homEquiv_leftMap]
  rw [ht, ← F.map_comp, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Construct the original system from left transitions with their actual comparison laws. -/
def System.ofLeft (obj : ∀ i, A i)
    (map : ∀ {i j : I} (a : i ⟶ j), (D.left a).obj (obj i) ⟶ obj j)
    (map_id : ∀ i, map (𝟙 i) = (D.leftIdIso i).hom.app (obj i))
    (map_comp : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k),
      map (a ≫ b) = (D.leftCompIso a b).hom.app (obj i) ≫
        (D.left b).map (map a) ≫ map b) : System D where
  obj := obj
  map a := (D.adj a).homEquiv _ _ (map a)
  map_id i := by
    rw [map_id]
    have ht := homEquiv_precomp_conjugate Adjunction.id (D.adj (𝟙 i))
      (D.leftIdIso i).hom (𝟙 (obj i))
    have hm : conjugateEquiv Adjunction.id (D.adj (𝟙 i)) (D.leftIdIso i).hom =
        (D.idIso i).inv := Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _
    rw [hm] at ht
    have hid : Adjunction.id.homEquiv (obj i) (obj i) (𝟙 (obj i)) = 𝟙 (obj i) :=
      (Adjunction.homEquiv_id Adjunction.id (obj i)).trans rfl
    have ht' := ht.trans (congrArg
      (fun k => k ≫ (D.idIso i).inv.app (obj i)) hid)
    have hleft := congrArg ((D.adj (𝟙 i)).homEquiv (obj i) (obj i))
      (Category.comp_id ((D.leftIdIso i).hom.app (obj i)))
    have hvalue := hleft.symm.trans (ht'.trans (Category.id_comp _))
    exact (congrArg (fun k => k ≫ (D.idIso i).hom.app (obj i)) hvalue).trans
      ((D.idIso i).inv_hom_id_app (obj i))
  map_comp a b := by
    rw [map_comp, homEquiv_precomp_conjugate ((D.adj a).comp (D.adj b))
      (D.adj (a ≫ b)) (D.leftCompIso a b).hom]
    have hm : conjugateEquiv ((D.adj a).comp (D.adj b)) (D.adj (a ≫ b))
        (D.leftCompIso a b).hom = (D.compIso a b).inv :=
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
    rw [hm, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
      Adjunction.comp_homEquiv]
    change (D.adj a).homEquiv _ _ ((D.adj b).homEquiv _ _
      ((D.left b).map (map a) ≫ map b)) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

/-- The constructor retains the supplied original left-transition map. -/
@[simp]
lemma System.ofLeft_leftMap (obj : ∀ i, A i)
    (map : ∀ {i j : I} (a : i ⟶ j), (D.left a).obj (obj i) ⟶ obj j)
    (map_id : ∀ i, map (𝟙 i) = (D.leftIdIso i).hom.app (obj i))
    (map_comp : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k),
      map (a ≫ b) = (D.leftCompIso a b).hom.app (obj i) ≫
        (D.left b).map (map a) ≫ map b)
    {i j : I} (a : i ⟶ j) :
    (System.ofLeft D obj map map_id map_comp).leftMap D a = map a := by
  change ((D.adj a).homEquiv (obj i) (obj j)).symm
    (((D.adj a).homEquiv (obj i) (obj j)) (map a)) = map a
  exact Equiv.symm_apply_apply _ _

/-- Compatibility name for the canonical constructor from left transitions. -/
abbrev System.ofLeftMaps (P : ∀ i, A i)
    (φ : ∀ {i j}, (a : i ⟶ j) → (D.left a).obj (P i) ⟶ P j)
    (hId : ∀ i, φ (𝟙 i) = (D.leftIdIso i).hom.app (P i))
    (hComp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) = (D.leftCompIso a b).hom.app (P i) ≫
        (D.left b).map (φ a) ≫ φ b) : System D :=
  System.ofLeft D P φ hId hComp

/-- Compatibility adapter for comparison isomorphisms equal to the actual mates. -/
abbrev System.ofLeftMapsWithComparisons
    (eId : ∀ i, D.left (𝟙 i) ≅ 𝟭 (A i))
    (eComp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k),
      D.left (a ≫ b) ≅ D.left a ⋙ D.left b)
    (heId : ∀ i, D.leftIdIso i = eId i)
    (heComp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k), D.leftCompIso a b = eComp a b)
    (P : ∀ i, A i) (φ : ∀ {i j}, (a : i ⟶ j) → (D.left a).obj (P i) ⟶ P j)
    (hId : ∀ i, φ (𝟙 i) = (eId i).hom.app (P i))
    (hComp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) = (eComp a b).hom.app (P i) ≫ (D.left b).map (φ a) ≫ φ b) :
    System D :=
  System.ofLeft D P φ
    (fun i => by rw [heId]; exact hId i)
    (fun a b => by rw [heComp]; exact hComp a b)

end InjectiveSystem
end CategoryTheory
