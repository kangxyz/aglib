/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantFiniteGenerators
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Constant-source morphisms and original module sections

The original constant-sheaf adjunction at the terminal object of a slice
identifies maps from a constant module with linear maps to the original section
module. This is assembled naturally in the whole target sheaf. Its inverse is
the existing sectionToSlice constructor, so no second local-Hom realization is
introduced. No finiteness, projectivity or connectedness is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r

namespace ModuleCat.Sheaf

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  {Λ : Type r} [Ring Λ]

attribute [local instance] hasSheafify

/-- The original constant-sheaf adjunction on the slice gives the additive section comparison. -/
def constantSliceHomAddEquiv (U : C) (M : ModuleCat.{max c h} Λ)
    (F : Sheaf J (ModuleCat.{max c h} Λ)) :
    ((constantSheaf (J.over U) (ModuleCat.{max c h} Λ)).obj M ⟶
      (J.overPullback (ModuleCat.{max c h} Λ) U).obj F) ≃+ (M ⟶ F.obj.obj (op U)) :=
  (constantSheafAdj (J.over U) (ModuleCat.{max c h} Λ) Over.mkIdTerminal).homAddEquiv
    M ((J.overPullback (ModuleCat.{max c h} Λ) U).obj F)

/-- The forward map retains the original sheafification unit at the slice's terminal object. -/
theorem constantSliceHomAddEquiv_apply (U : C) (M : ModuleCat.{max c h} Λ)
    (F : Sheaf J (ModuleCat.{max c h} Λ))
    (a : (constantSheaf (J.over U) (ModuleCat.{max c h} Λ)).obj M ⟶
      (J.overPullback (ModuleCat.{max c h} Λ) U).obj F) :
    constantSliceHomAddEquiv J U M F a =
      (constantUnit (J.over U) M).app (op (Over.mk (𝟙 U))) ≫
        a.hom.app (op (Over.mk (𝟙 U))) := by
  change (constantSheafAdj (J.over U) (ModuleCat.{max c h} Λ)
    Over.mkIdTerminal).homEquiv M _ a = _
  rw [Adjunction.homEquiv_unit, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, Category.id_comp]
  rfl

/-- The inverse is exactly the existing section-to-slice morphism. -/
theorem constantSliceHomAddEquiv_symm (U : C) (M : ModuleCat.{max c h} Λ)
    (F : Sheaf J (ModuleCat.{max c h} Λ)) (a : M ⟶ F.obj.obj (op U)) :
    (constantSliceHomAddEquiv J U M F).symm a = sectionToSlice J U F M a := by
  apply (constantSliceHomAddEquiv J U M F).injective
  rw [AddEquiv.apply_symm_apply, constantSliceHomAddEquiv_apply, sectionToSlice_unit]
  simp only [Over.mk_left, Over.mk_hom, op_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- The whole comparison is natural on the original coefficient sheaves. -/
def constantSliceHomNatIso (U : C) (M : ModuleCat.{max c h} Λ) :
    J.overPullback (ModuleCat.{max c h} Λ) U ⋙
        preadditiveCoyoneda.obj
          (op ((constantSheaf (J.over U) (ModuleCat.{max c h} Λ)).obj M)) ≅
      (sheafSections J (ModuleCat.{max c h} Λ)).obj (op U) ⋙
        preadditiveCoyoneda.obj (op M) :=
  NatIso.ofComponents (fun F => (constantSliceHomAddEquiv J U M F).toAddCommGrpIso)
    (fun p => by
      ext a
      exact (constantSheafAdj (J.over U) (ModuleCat.{max c h} Λ)
        Over.mkIdTerminal).homEquiv_naturality_right a
          ((J.overPullback (ModuleCat.{max c h} Λ) U).map p))

/-- Evaluation of the whole comparison is the original additive adjunction map. -/
theorem constantSliceHomNatIso_hom_app_apply (U : C) (M : ModuleCat.{max c h} Λ)
    (F : Sheaf J (ModuleCat.{max c h} Λ))
    (a : (constantSheaf (J.over U) (ModuleCat.{max c h} Λ)).obj M ⟶
      (J.overPullback (ModuleCat.{max c h} Λ) U).obj F) :
    (constantSliceHomNatIso J U M).hom.app F a = constantSliceHomAddEquiv J U M F a := rfl

end ModuleCat.Sheaf
