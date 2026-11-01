/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing

/-! # Sections of actual finite-presentation morphisms at a stage

Apply native morphism descent to the identity source model. The result is
an actual section of the original pullback, with its exact limit comparison.
No new model or normalization/base-change identification is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- A section of an actual limit pullback descends to a section of the same
model at a later stage, retaining its original comparison map. -/
theorem exists_section_of_baseChange_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {Y : Scheme.{u}} (p : Y ⟶ D.obj i) [LocallyOfFinitePresentation p]
    (s : c.pt ⟶ pullback (c.π.app i) p)
    (hs : s ≫ pullback.fst (c.π.app i) p = 𝟙 c.pt) :
    ∃ (j : Over i) (t : D.obj j.left ⟶ (baseChangeDiagram D i p).obj j),
      t ≫ pullback.fst (D.map j.hom) p = 𝟙 (D.obj j.left) ∧
      c.π.app j.left ≫ t = s ≫ (baseChangeCone D c i p).π.app j := by
  let a : pullback (c.π.app i) (𝟙 (D.obj i)) ⟶ pullback (c.π.app i) p :=
    pullback.fst _ _ ≫ s
  have ha : a ≫ pullback.fst (c.π.app i) p = pullback.fst _ (𝟙 (D.obj i)) := by
    dsimp only [a]
    rw [Category.assoc, hs]
    exact Category.comp_id _
  obtain ⟨j, b, hb, hcomp⟩ :=
    exists_hom_between_baseChanges_of_isLimit D c hc i (𝟙 (D.obj i)) p a ha
  let k : D.obj j.left ⟶ pullback (D.map j.hom) (𝟙 (D.obj i)) :=
    pullback.lift (𝟙 _) (D.map j.hom) (by simp)
  let kLimit : c.pt ⟶ pullback (c.π.app i) (𝟙 (D.obj i)) :=
    pullback.lift (𝟙 _) (c.π.app i) (by simp)
  have hk : c.π.app j.left ≫ k =
      kLimit ≫ (baseChangeCone D c i (𝟙 (D.obj i))).π.app j := by
    apply pullback.hom_ext
    · simp [k, kLimit, Category.assoc]
    · simp [k, kLimit, Category.assoc]
  refine ⟨j, k ≫ b, ?_, ?_⟩
  · rw [Category.assoc, hb]
    exact pullback.lift_fst _ _ _
  · rw [← Category.assoc, hk, Category.assoc, hcomp, ← Category.assoc]
    simp only [a, kLimit, ← Category.assoc, pullback.lift_fst]
    exact congrArg (fun f => f ≫ (baseChangeCone D c i p).π.app j) (Category.id_comp s)

end AlgebraicGeometry.Scheme
