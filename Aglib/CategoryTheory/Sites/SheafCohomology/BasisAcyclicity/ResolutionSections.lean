/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Original represented Ext vanishing and resolution sections

Vanishing of positive Ext from the original free representable gives actual
section primitives in every supplied injective resolution. This is the
sectionwise input to a mapped-resolution comparison, with independent site,
coefficient and Ext universes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe c h w e

namespace CategoryTheory.Sheaf.BasisAcyclicity

open Hypercohomology

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max h w}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max h w})]
  {F : Sheaf J AddCommGrpCat.{max h w}} (I : InjectiveResolution F) (W : C)

/-- A section cocycle is a section boundary when its original represented Ext
class vanishes. The section maps are the literal maps of the supplied resolution. -/
theorem exists_resolution_section_primitive (n : ℕ)
    (h : ∀ x : Ext (freeAbelianSheaf J W) F (n + 1), x = 0)
    (s : (I.cocomplex.X (n + 1)).obj.obj (op W))
    (hs : (I.cocomplex.d (n + 1) (n + 2)).hom.app (op W) s = 0) :
    ∃ t : (I.cocomplex.X n).obj.obj (op W),
      (I.cocomplex.d n (n + 1)).hom.app (op W) t = s := by
  let f := (sectionsAddEquiv J W (I.cocomplex.X (n + 1))).symm s
  have hf : f ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
    apply (sectionsAddEquiv J W _).injective
    change sectionsEquiv J W _ (f ≫ _) = (sectionsAddEquiv J W _) 0
    rw [map_zero, sectionsEquiv_naturality]
    have he : sectionsEquiv J W _ f = s :=
      (sectionsAddEquiv J W _).apply_symm_apply s
    rw [he]
    exact hs
  obtain ⟨g, hg⟩ := (I.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp
    (h (I.extMk f (n + 2) rfl hf))
  refine ⟨sectionsEquiv J W _ g, ?_⟩
  rw [← sectionsEquiv_naturality, hg]
  exact (sectionsAddEquiv J W _).apply_symm_apply s

/-- The original evaluation complex of any supplied resolution is exact in a
positive degree whenever the corresponding original represented Ext vanishes. -/
theorem resolution_sections_exactAt_succ (n : ℕ)
    (h : ∀ x : Ext (freeAbelianSheaf J W) F (n + 1), x = 0) :
    (((sheafToPresheaf J AddCommGrpCat ⋙
      (evaluation Cᵒᵖ AddCommGrpCat).obj (op W)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  rw [ShortComplex.ab_exact_iff]
  exact exists_resolution_section_primitive J I W n h

end CategoryTheory.Sheaf.BasisAcyclicity
