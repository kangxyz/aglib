/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.Annihilator.Diagram
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Sections of the native annihilator subsheaf

Evaluation preserves the actual sheaf kernel. Thus a section killed by `n`
has its canonical lift to that kernel, with the original inclusion formula.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]

/-- Native evaluation of the actual abelian sheaf at a test object. -/
abbrev annihilatorEvaluation (U : C) : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)

omit [HasSheafify J AddCommGrpCat.{w}] in
/-- The native evaluation map of multiplication acts on sections by the same natural scalar. -/
theorem annihilatorEvaluation_nsmul_id (F : Sheaf J AddCommGrpCat.{w}) (U : C)
    (n : ℕ) (s : F.obj.obj (op U)) :
    ((annihilatorEvaluation (J := J) U).map (n • 𝟙 F)) s = n • s := by
  rw [Functor.map_nsmul, Functor.map_id]
  rfl

/-- The actual native kernel/evaluation comparison, followed by the native concrete-kernel iso. -/
def annihilatorSectionsIso (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (U : C) :
    (annihilator F n).obj.obj (op U) ≅
      AddCommGrpCat.of
        (((annihilatorEvaluation (J := J) U).map (n • 𝟙 F)).hom.ker) :=
  PreservesKernel.iso (annihilatorEvaluation (J := J) U) (n • 𝟙 F) ≪≫
    AddCommGrpCat.kernelIsoKer _

/-- The section comparison's inverse maps back by the original native inclusion. -/
@[reassoc (attr := simp)]
theorem annihilatorSectionsIso_inv_ι (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (U : C) :
    (annihilatorSectionsIso F n U).inv ≫ (annihilatorι F n).hom.app (op U) =
      AddCommGrpCat.ofHom
        (AddSubgroup.subtype
          (((annihilatorEvaluation (J := J) U).map (n • 𝟙 F)).hom.ker)) := by
  change (AddCommGrpCat.kernelIsoKer _).inv ≫
      (PreservesKernel.iso (annihilatorEvaluation (J := J) U) (n • 𝟙 F)).inv ≫
        (annihilatorEvaluation (J := J) U).map (kernel.ι (n • 𝟙 F)) = _
  rw [PreservesKernel.iso_inv_ι, AddCommGrpCat.kernelIsoKer_inv_comp_ι]

/-- A killed section has its canonical lift to the actual native annihilator subsheaf. -/
def annihilatorSection (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (U : C)
    (s : F.obj.obj (op U)) (h : n • s = 0) : (annihilator F n).obj.obj (op U) :=
  (annihilatorSectionsIso F n U).inv
    ⟨s, by
      change ((annihilatorEvaluation (J := J) U).map (n • 𝟙 F)) s = 0
      exact (annihilatorEvaluation_nsmul_id F U n s).trans h⟩

/-- The canonical lifted section maps to the identical original section. -/
@[simp]
theorem annihilatorSection_ι (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (U : C)
    (s : F.obj.obj (op U)) (h : n • s = 0) :
    (annihilatorι F n).hom.app (op U) (annihilatorSection F n U s h) = s :=
  ConcreteCategory.congr_hom (annihilatorSectionsIso_inv_ι F n U) _

end CategoryTheory.Sheaf
