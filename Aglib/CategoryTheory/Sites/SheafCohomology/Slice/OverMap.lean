/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Restriction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# The original restriction between slice sites

Restriction along a map of representing objects is native precomposition by
`Over.map`. Its exactness follows from cocontinuity, and its map from a constant
sheaf is constructed from the original sheafification unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace CategoryTheory.Sheaf.SliceCohomology

universe u v m w w'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {V U : C} (f : V ⟶ U)

/-- The native restriction along `Over.map f`, without an isomorphic replacement. -/
abbrev overMapRestriction : Sheaf (J.over U) AddCommGrpCat.{m} ⥤
    Sheaf (J.over V) AddCommGrpCat.{m} :=
  (Over.map f).sheafPushforwardContinuous AddCommGrpCat (J.over V) (J.over U)

instance overMapRestriction_additive : (overMapRestriction J f).Additive where
  map_add := by intros; rfl

instance overMapRestriction_preservesLimitsOfShape {K : Type w} [Category.{w'} K]
    [HasLimitsOfShape K AddCommGrpCat.{m}] :
    PreservesLimitsOfShape K (overMapRestriction.{u, v, m} J f) :=
  Functor.sheafPushforwardContinuous_preservesLimitsOfShape
    (Over.map f) AddCommGrpCat.{m} (J.over V) (J.over U)

instance overMapRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (overMapRestriction.{u, v, m} J f) :=
  ⟨fun _ => inferInstance⟩

section Exact

variable [HasSheafify (J.over U) AddCommGrpCat.{m}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [(J.over U).HasSheafCompose (forget AddCommGrpCat.{m})]
  [HasSheafify (J.over V) AddCommGrpCat.{m}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [(J.over V).HasSheafCompose (forget AddCommGrpCat.{m})]

instance overMapRestriction_preservesEpimorphisms :
    (overMapRestriction.{u, v, m} J f).PreservesEpimorphisms where
  preserves {F G} g hg := by
    let : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{m} g).mpr hg
    apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{m}
      ((overMapRestriction J f).map g)).mp
    change Presheaf.IsLocallySurjective (J.over V) (whiskerLeft (Over.map f).op g.hom)
    exact Presheaf.isLocallySurjective_whisker (J.over V) (J.over U) (Over.map f) g.hom

instance overMapRestriction_preservesHomology :
    (overMapRestriction.{u, v, m} J f).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance overMapRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (overMapRestriction.{u, v, m} J f) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end Exact

variable [HasSheafify (J.over U) AddCommGrpCat.{m}]
  [HasSheafify (J.over V) AddCommGrpCat.{m}]

/-- The original constant-sheaf map induced by restricting the sheafification unit. -/
def constantOverMap (A : AddCommGrpCat.{m}) :
    (constantSheaf (J.over V) AddCommGrpCat).obj A ⟶
      (overMapRestriction J f).obj ((constantSheaf (J.over U) AddCommGrpCat).obj A) :=
  ((sheafificationAdjunction (J.over V) AddCommGrpCat).homEquiv _ _).symm
    (whiskerLeft (Over.map f).op (toSheafify (J.over U)
      ((Functor.const (Over U)ᵒᵖ).obj A)))

/-- The defining comparison retains the native sheafification unit on presheaves. -/
theorem constantOverMap_unit (A : AddCommGrpCat.{m}) :
    toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj A) ≫
      (constantOverMap J f A).hom =
        whiskerLeft (Over.map f).op
          (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj A)) := by
  exact ((sheafificationAdjunction (J.over V) AddCommGrpCat).homEquiv _ _).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- Composing with a coefficient morphism gives its original restricted presheaf map. -/
theorem constantOverMap_comp_unit (A : AddCommGrpCat.{m})
    (F : Sheaf (J.over U) AddCommGrpCat.{m})
    (a : (constantSheaf (J.over U) AddCommGrpCat).obj A ⟶ F) :
    toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj A) ≫
      (constantOverMap J f A ≫ (overMapRestriction J f).map a).hom =
        whiskerLeft (Over.map f).op
          (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj A) ≫ a.hom) := by
  change _ ≫ (constantOverMap J f A).hom ≫ whiskerLeft (Over.map f).op a.hom = _
  rw [← Category.assoc, constantOverMap_unit, ← whiskerLeft_comp]

/-- The terminal-section adjunction evaluates the original sheafification unit. -/
theorem constantSheafAdj_homEquiv_eq (A : AddCommGrpCat.{m})
    (F : Sheaf (J.over U) AddCommGrpCat.{m})
    (a : (constantSheaf (J.over U) AddCommGrpCat).obj A ⟶ F) :
    (constantSheafAdj (J.over U) AddCommGrpCat Over.mkIdTerminal).homEquiv A F a =
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj A) ≫ a.hom).app
        (op (Over.mk (𝟙 U))) := by
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a constant-source morphism gives the original restriction on sections. -/
theorem constantOverMap_sections (A : AddCommGrpCat.{m})
    (F : Sheaf (J.over U) AddCommGrpCat.{m})
    (a : (constantSheaf (J.over U) AddCommGrpCat).obj A ⟶ F) :
    (constantSheafAdj (J.over V) AddCommGrpCat Over.mkIdTerminal).homEquiv A
      ((overMapRestriction J f).obj F)
      (constantOverMap J f A ≫ (overMapRestriction J f).map a) =
    (constantSheafAdj (J.over U) AddCommGrpCat Over.mkIdTerminal).homEquiv A F a ≫
      F.obj.map (Over.mkIdTerminal.from
        ((Over.map f).obj (Over.mk (𝟙 V)))).op := by
  rw [constantSheafAdj_homEquiv_eq, constantSheafAdj_homEquiv_eq,
    constantOverMap_comp_unit]
  simpa using ((toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj A) ≫ a.hom).naturality
    (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V)))).op)

end CategoryTheory.Sheaf.SliceCohomology
