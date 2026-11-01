/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.OverBaseGluing

/-!
# Descent with supplied original chart comparisons

Specified isomorphisms to the actual pullbacks transport the original
isomorphism descent theorem without replacing any chart. Both directions,
the structural map and the projection tracking original points are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.OverBaseSpreading

universe u

variable {I : Type u} [Category.{u} I]
variable (D : I ⥤ Scheme.{u}) (c : Cone D) {B : Scheme.{u}}
variable (β : D ⟶ (Functor.const I).obj B) (α : c.pt ⟶ B)
variable (hα : ∀ k, c.π.app k ≫ β.app k = α) (i : I)
variable {X Y Z : Scheme.{u}} (q : Y ⟶ B)
variable {Z' : Over i → Scheme.{u}}
variable (d : Z ≅ pullback q α)
variable (d' : ∀ j, Z' j ≅ pullback q (β.app j.left))

/-- The actual comparison between the supplied original charts. -/
def chartComparison (j : Over i) : Z ⟶ Z' j :=
  d.hom ≫ comparison D c β α hα i q j ≫ (d' j).inv

/-- Chart comparison retains the projection to the original model. -/
@[reassoc (attr := simp)]
theorem chartComparison_fst (j : Over i) :
    chartComparison D c β α hα i q d d' j ≫ (d' j).hom ≫
      pullback.fst q (β.app j.left) = d.hom ≫ pullback.fst q α := by
  simp only [chartComparison, Category.assoc, Iso.inv_hom_id_assoc, comparison_fst]

/-- Chart comparison retains the original base-cone projection. -/
@[reassoc (attr := simp)]
theorem chartComparison_snd (j : Over i) :
    chartComparison D c β α hα i q d d' j ≫ (d' j).hom ≫
      pullback.snd q (β.app j.left) = d.hom ≫ pullback.snd q α ≫ c.π.app j.left := by
  simp only [chartComparison, Category.assoc, Iso.inv_hom_id_assoc, comparison_snd]

/-- A supplied chart isomorphism over the original limit descends using the
supplied original charts at the stages, with both comparison directions and
both original projections. -/
theorem exists_chart_with_comparison [IsCofiltered I]
    [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (hc : IsLimit c) (p : X ⟶ B)
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (e : Z ≅ pullback p α)
    (he : e.hom ≫ pullback.snd p α = d.hom ≫ pullback.snd q α) :
    ∃ (j : Over i) (e' : Z' j ≅ pullback p (β.app j.left)),
      e'.hom ≫ pullback.snd p (β.app j.left) =
        (d' j).hom ≫ pullback.snd q (β.app j.left) ∧
      chartComparison D c β α hα i q d d' j ≫ e'.hom =
        e.hom ≫ comparison D c β α hα i p j ∧
      comparison D c β α hα i p j ≫ e'.inv =
        e.inv ≫ chartComparison D c β α hα i q d d' j ∧
      chartComparison D c β α hα i q d d' j ≫ e'.hom ≫
        pullback.fst p (β.app j.left) = e.hom ≫ pullback.fst p α := by
  let e₀ : (Over.pullback α).obj (Over.mk q) ≅ (Over.pullback α).obj (Over.mk p) :=
    Over.isoMk (d.symm ≪≫ e) (by
      change (d.inv ≫ e.hom) ≫ pullback.snd p α = pullback.snd q α
      simp only [Category.assoc, he, Iso.inv_hom_id_assoc])
  obtain ⟨j, e₁, hh, hi⟩ := exists_iso_with_comparison D c β α hα i hc q p e₀
  let e' := d' j ≪≫ (Over.forget _).mapIso e₁
  have hhom : chartComparison D c β α hα i q d d' j ≫ e'.hom =
      e.hom ≫ comparison D c β α hα i p j := by
    have h := congrArg (fun z => d.hom ≫ z) hh
    simpa only [chartComparison, e', e₀, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Over.forget_map, Over.isoMk_hom_left,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] using h
  have hinv : comparison D c β α hα i p j ≫ e'.inv =
      e.inv ≫ chartComparison D c β α hα i q d d' j := by
    have h := congrArg (fun z => z ≫ (d' j).inv) hi
    simpa only [chartComparison, e', e₀, Iso.trans_inv, Iso.symm_inv,
      Functor.mapIso_inv, Over.forget_map, Over.isoMk_inv_left,
      Category.assoc] using h
  refine ⟨j, e', ?_, hhom, hinv, ?_⟩
  · have h := Over.w e₁.hom
    change e₁.hom.left ≫ pullback.snd p (β.app j.left) =
      pullback.snd q (β.app j.left) at h
    simp only [e', Iso.trans_hom, Functor.mapIso_hom, Over.forget_map,
      Category.assoc, h]
  · rw [← Category.assoc, hhom]
    simp only [Category.assoc, comparison_fst]

end AlgebraicGeometry.Scheme.OverBaseSpreading
