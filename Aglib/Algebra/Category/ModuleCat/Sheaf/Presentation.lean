/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Presentations and basis transport for module sheaves

Relocated from `Aglib/AlgebraicGeometry/Modules/FinitePresentation/Basic.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `fb3cf4be303d84a2475c735f1a32c1112c5c5d3685bac0880fa02dfe4550fea2`.
Relocated from `Aglib/AlgebraicGeometry/Modules/LocallyFree/Locality.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `63707ec1099ec3f8e22aac5b09edaf5cac5cba94047bc52ea700beab11dafad2`.
The statements retain their original universes, hypotheses and actual maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v v' w w' t t'
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

section Presentation

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type w'} [Category.{v'} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [HasSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transporting generating sections by an isomorphism preserves the basis condition. -/
instance generatingSections_ofEpi_isIso {M N : SheafOfModules.{u} R}
    (G : M.GeneratingSections) (f : M ⟶ N) [IsIso f] [IsIso G.π] :
    IsIso (G.ofEpi f).π := by
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

/-- A colimit-preserving functor which preserves the unit carries finite
presentations to finite presentations: the generator and relation index sets
are unchanged. -/
instance finitePresentation_map_isFinite {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := by
    constructor
    change Finite P.generators.I
    infer_instance
  isFiniteType_relations := by
    constructor
    change Finite P.relations.I
    infer_instance

end Presentation

section Presentation
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type t} [Category.{t'} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [HasSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transporting a presentation with a basis along an isomorphism preserves
its basis property. -/
theorem presentationOfIsIso_generators_isIso {M N : SheafOfModules.{u} R}
    (P : M.Presentation) (f : M ⟶ N) [IsIso f] (hP : IsIso P.generators.π) :
    IsIso (P.ofIsIso f).generators.π := by
  have := hP
  exact generatingSections_ofEpi_isIso P.generators f

/-- A colimit-preserving functor carrying units to units preserves the basis
property of a presentation. -/
theorem presentationMap_generators_isIso {M : SheafOfModules.{u} R}
    (P : M.Presentation)
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R))
    (hP : IsIso P.generators.π) :
    IsIso (P.map F η).generators.π := by
  have := hP
  rw [SheafOfModules.Presentation.map_π_eq]
  infer_instance

end Presentation

end SheafOfModules
