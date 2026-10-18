/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-! Lift a local gluing diagram through a faithful functor using actual arrow lifts. -/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.DiagramLift

universe i v u v' u'

section Lift

variable {I : Type i} [Category I] {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) [G.Faithful] (F : I ⥤ D) (A : I → C)
  (e : ∀ i, G.obj (A i) ≅ F.obj i)
  (h : ∀ {i j : I} (f : i ⟶ j), ∃ g : A i ⟶ A j,
    G.map g = (e i).hom ≫ F.map f ≫ (e j).inv)

/-- A chosen lift of the conjugated transition `(e i).hom ≫ F.map f ≫ (e j).inv` through `G`,
supplied by `h`. -/
def diagramLiftMap {i j : I} (f : i ⟶ j) : A i ⟶ A j := (h f).choose

omit [G.Faithful] in
@[simp] theorem map_diagramLiftMap {i j : I} (f : i ⟶ j) :
    G.map (diagramLiftMap G F A e h f) = (e i).hom ≫ F.map f ≫ (e j).inv :=
  (h f).choose_spec

/-- Lift the local diagram; faithfulness proves the functor laws. -/
def diagramLift : I ⥤ C where
  obj := A
  map f := diagramLiftMap G F A e h f
  map_id i := by
    apply G.map_injective
    simp
  map_comp f g := by
    apply G.map_injective
    simp [Category.assoc]

/-- The lifted diagram becomes exactly the original diagram up to these
specified objectwise isomorphisms. -/
def diagramLiftIso : diagramLift G F A e h ⋙ G ≅ F :=
  NatIso.ofComponents e (by
    intro i j f
    change G.map (diagramLiftMap G F A e h f) ≫ (e j).hom = (e i).hom ≫ F.map f
    simp)

variable (B : I ⥤ C) (ρ : F ⟶ B ⋙ G)
  (τ : ∀ i, A i ⟶ B.obj i)
  (hτ : ∀ i, G.map (τ i) = (e i).hom ≫ ρ.app i)

/-- The local structural maps descend as a natural transformation. -/
def diagramLiftStructure : diagramLift G F A e h ⟶ B where
  app := τ
  naturality i j f := by
    apply G.map_injective
    change G.map (diagramLiftMap G F A e h f ≫ τ j) = G.map (τ i ≫ B.map f)
    simp only [Functor.map_comp, map_diagramLiftMap, hτ, Category.assoc,
      Iso.inv_hom_id_assoc]
    exact congrArg (fun k ↦ (e i).hom ≫ k) (ρ.naturality f)

theorem diagramLiftStructure_equifibered [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan G] [G.ReflectsIsomorphisms]
    (hρ : ρ.Equifibered) : (diagramLiftStructure G F A e h B ρ τ hτ).Equifibered := by
  let : ReflectsLimitsOfShape WalkingCospan G :=
    ⟨fun {H} ↦ reflectsLimit_of_reflectsIsomorphisms H G⟩
  intro i j f
  apply IsPullback.of_map G
    ((diagramLiftStructure G F A e h B ρ τ hτ).naturality f)
  refine (hρ f).of_iso (e i).symm (e j).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [diagramLift]
  · simp [diagramLiftStructure, hτ]
  · simp [diagramLiftStructure, hτ]
  · simp

end Lift

end CategoryTheory.Functor.DiagramLift

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 59c64ca85b66b7cfeb030272e8efeb797e5a91e404a1fc9fb0bd39932aef24ae.
Definitions, hypotheses and universes are retained modulo native names. -/
