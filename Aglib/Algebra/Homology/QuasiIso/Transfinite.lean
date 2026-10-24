/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.QuasiIso.Colimit
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-! # Exact-colimit stability of the native quasi-isomorphism property -/

@[expose] public noncomputable section

universe w w' v u t

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type t} (c : ComplexShape ι)

set_option backward.isDefEq.respectTransparency false in
instance quasiIso_isStableUnderColimitsOfShape (J : Type w') [Category.{w} J]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    (quasiIso C c).IsStableUnderColimitsOfShape J where
  condition F G cF cG hF hG α hα φ hφ := by
    have : QuasiIso (colim.map α) := quasiIso_colimMap α hα
    let eF := colimit.isoColimitCocone ⟨cF, hF⟩
    let eG := colimit.isoColimitCocone ⟨cG, hG⟩
    have he : φ = eF.inv ≫ colim.map α ≫ eG.hom := by
      apply hF.hom_ext
      intro j
      have hp : cF.ι.app j ≫ eF.inv = colimit.ι F j :=
        colimit.isoColimitCocone_ι_inv ⟨cF, hF⟩ j
      have hq : colimit.ι G j ≫ eG.hom = cG.ι.app j :=
        colimit.isoColimitCocone_ι_hom ⟨cG, hG⟩ j
      rw [← Category.assoc, ← Category.assoc, hp, colimit.ι_map, Category.assoc, hq]
      exact hφ j
    change QuasiIso φ
    rw [he]
    infer_instance

instance quasiIso_isStableUnderFilteredColimits [IsGrothendieckAbelian.{w} C] :
    MorphismProperty.IsStableUnderFilteredColimits.{w, w} (quasiIso C c) where
  isStableUnderColimitsOfShape J _ _ := by infer_instance

end HomologicalComplex
