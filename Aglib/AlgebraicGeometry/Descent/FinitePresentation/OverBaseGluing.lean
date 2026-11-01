/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing

/-!
# Finite-presentation isomorphism descent over an unchanged base

The models lie over a supplied original base, while the cofiltered diagram lies
above that base. Canonical pullback reassociation retains both comparison
directions and both original pullback projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.OverBaseSpreading

universe u

variable {I : Type u} [Category.{u} I]
variable (D : I ⥤ Scheme.{u}) (c : Cone D) {B : Scheme.{u}}
variable (β : D ⟶ (Functor.const I).obj B) (α : c.pt ⟶ B)
variable (hα : ∀ k, c.π.app k ≫ β.app k = α) (i : I)

variable {X Y : Scheme.{u}}

/-- The original model pulled back to the specified stage. -/
abbrev initialModel (f : X ⟶ B) := pullback.fst (β.app i) f

/-- Reassociation at the original limit, with its exact coefficient equation. -/
def localRebase (f : X ⟶ B) :
    (Over.pullback (c.π.app i)).obj (Over.mk (initialModel D β i f)) ≅
      (Over.pullback α).obj (Over.mk f) :=
  baseChangeDiagram_rebaseIso f (β.app i) (c.π.app i) ≪≫
    eqToIso (congrArg (fun b => (Over.pullback b).obj (Over.mk f))
      (hα i))

/-- A later stage keeps the original coefficient map under reassociation. -/
theorem stage_structure (j : Over i) :
    D.map j.hom ≫ β.app i = β.app j.left := by
  exact (β.naturality j.hom).trans (Category.comp_id _)

/-- Reassociation at a later stage. -/
def stageRebase (f : X ⟶ B) (j : Over i) :
    (Over.pullback (D.map j.hom)).obj (Over.mk (initialModel D β i f)) ≅
      (Over.pullback (β.app j.left)).obj (Over.mk f) :=
  baseChangeDiagram_rebaseIso f (β.app i) (D.map j.hom) ≪≫
    eqToIso (congrArg (fun b => (Over.pullback b).obj (Over.mk f)) (stage_structure D β i j))

/-- The actual limit comparison, expressed by canonical pullback reassociation. -/
def comparison (f : X ⟶ B) (j : Over i) :
    ((Over.pullback α).obj (Over.mk f)).left ⟶
      ((Over.pullback (β.app j.left)).obj (Over.mk f)).left :=
  (localRebase D c β α hα i f).inv.left ≫
    (pullbackSymmetry (c.π.app i) (initialModel D β i f)).inv ≫
    (baseChangeCone D c i (initialModel D β i f)).π.app j ≫
    (pullbackSymmetry (D.map j.hom) (initialModel D β i f)).hom ≫
    (stageRebase D β i f j).hom.left

/-- Reassociation retains the original model projection, including equality transport. -/
private theorem rebase_hom_fst {T T₀ T₁ Z : Scheme.{u}}
    (f : Z ⟶ T) (k : T₀ ⟶ T) (h : T₁ ⟶ T₀) (b : T₁ ⟶ T)
    (hb : h ≫ k = b) :
    (baseChangeDiagram_rebaseIso f k h ≪≫
      eqToIso (congrArg (fun a => (Over.pullback a).obj (Over.mk f)) hb)).hom.left ≫
        pullback.fst f b = pullback.fst (pullback.fst k f) h ≫ pullback.snd k f := by
  subst b
  simp [baseChangeDiagram_rebaseIso]

/-- Local reassociation preserves the original model projection. -/
@[reassoc (attr := simp)]
theorem localRebase_hom_fst (f : X ⟶ B) :
    (localRebase D c β α hα i f).hom.left ≫ pullback.fst f α =
      pullback.fst (initialModel D β i f) (c.π.app i) ≫
        pullback.snd (β.app i) f :=
  rebase_hom_fst f (β.app i) (c.π.app i)
    α (hα i)

/-- Inverse local reassociation preserves the original model projection. -/
@[reassoc (attr := simp)]
theorem localRebase_inv_fst (f : X ⟶ B) :
    (localRebase D c β α hα i f).inv.left ≫
      pullback.fst (initialModel D β i f) (c.π.app i) ≫
        pullback.snd (β.app i) f = pullback.fst f α := by
  rw [← localRebase_hom_fst D c β α hα i f]
  exact Over.inv_left_hom_left_assoc (localRebase D c β α hα i f) _

/-- Stage reassociation preserves the original model projection. -/
@[reassoc (attr := simp)]
theorem stageRebase_hom_fst (f : X ⟶ B)
    (j : Over i) :
    (stageRebase D β i f j).hom.left ≫ pullback.fst f (β.app j.left) =
      pullback.fst (initialModel D β i f) (D.map j.hom) ≫
        pullback.snd (β.app i) f :=
  rebase_hom_fst f (β.app i) (D.map j.hom)
    (β.app j.left) (stage_structure D β i j)

/-- The comparison retains the projection to the original model. -/
@[reassoc (attr := simp)]
theorem comparison_fst (f : X ⟶ B) (j : Over i) :
    comparison D c β α hα i f j ≫ pullback.fst f (β.app j.left) =
      pullback.fst f α := by
  simp only [comparison, Category.assoc, stageRebase_hom_fst,
    pullbackSymmetry_hom_comp_fst_assoc, baseChangeCone_π_app_snd_assoc,
    pullbackSymmetry_inv_comp_snd_assoc, localRebase_inv_fst]

/-- The comparison retains the original cone projection on bases. -/
@[reassoc (attr := simp)]
theorem comparison_snd (f : X ⟶ B) (j : Over i) :
    comparison D c β α hα i f j ≫ pullback.snd f (β.app j.left) =
      pullback.snd f α ≫ c.π.app j.left := by
  have hs := Over.w (stageRebase D β i f j).hom
  have hl := Over.w (localRebase D c β α hα i f).inv
  change (stageRebase D β i f j).hom.left ≫
    pullback.snd f (β.app j.left) =
      pullback.snd (initialModel D β i f) (D.map j.hom) at hs
  change (localRebase D c β α hα i f).inv.left ≫
    pullback.snd (initialModel D β i f) (c.π.app i) =
      pullback.snd f α at hl
  simp only [comparison, Category.assoc, hs, pullbackSymmetry_hom_comp_snd,
    baseChangeCone_π_app_fst, pullbackSymmetry_inv_comp_fst_assoc, reassoc_of% hl]

/-- An isomorphism over the limit descends to an actual later stage. Both comparison
equations concern the original supplied isomorphism and the original models over
the unchanged base. -/
theorem exists_iso_with_comparison [IsCofiltered I]
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (hc : IsLimit c)
    (f : X ⟶ B) (g : Y ⟶ B)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (e : (Over.pullback α).obj (Over.mk f) ≅
      (Over.pullback α).obj (Over.mk g)) :
    ∃ (j : Over i)
      (e' : (Over.pullback (β.app j.left)).obj (Over.mk f) ≅
        (Over.pullback (β.app j.left)).obj (Over.mk g)),
      comparison D c β α hα i f j ≫ e'.hom.left = e.hom.left ≫ comparison D c β α hα i g j ∧
      comparison D c β α hα i g j ≫ e'.inv.left = e.inv.left ≫ comparison D c β α hα i f j := by
  let e₀ := localRebase D c β α hα i f ≪≫ e ≪≫ (localRebase D c β α hα i g).symm
  obtain ⟨j, e₁, h⟩ := exists_iso_between_baseChanges_with_comparison_of_isLimit
    D c hc i
    (initialModel D β i f) (initialModel D β i g) e₀
  let e' := (stageRebase D β i f j).symm ≪≫ e₁ ≪≫ stageRebase D β i g j
  refine ⟨j, e', ?_, ?_⟩
  · have hh := congrArg (fun z =>
        (localRebase D c β α hα i f).inv.left ≫
          (pullbackSymmetry (c.π.app i) (initialModel D β i f)).inv ≫
          z ≫ (pullbackSymmetry (D.map j.hom) (initialModel D β i g)).hom ≫
          (stageRebase D β i g j).hom.left) h.1
    simpa only [comparison, e', e₀, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Over.forget_map, Over.comp_left, Category.assoc,
      Iso.inv_hom_id_assoc, Over.hom_left_inv_left_assoc,
      Over.inv_left_hom_left_assoc] using hh
  · have hh := congrArg (fun z =>
        (localRebase D c β α hα i g).inv.left ≫
          (pullbackSymmetry (c.π.app i) (initialModel D β i g)).inv ≫
          z ≫ (pullbackSymmetry (D.map j.hom) (initialModel D β i f)).hom ≫
          (stageRebase D β i f j).hom.left) h.2
    simpa only [comparison, e', e₀, Iso.trans_inv, Iso.symm_inv,
      Functor.mapIso_inv, Over.forget_map, Over.comp_left, Category.assoc,
      Iso.inv_hom_id_assoc, Over.hom_left_inv_left_assoc,
      Over.inv_left_hom_left_assoc] using hh

end AlgebraicGeometry.Scheme.OverBaseSpreading
