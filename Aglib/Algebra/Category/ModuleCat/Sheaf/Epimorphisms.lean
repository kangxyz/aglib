/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Epimorphisms of module sheaves on a site

Relocated from `Aglib/AlgebraicGeometry/Modules/Epimorphisms.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `9f34c7fede80f84f59fbfe2f5cef224d5f6e05d382bfa9b9d2d08cfbdeb9c9e0`.
The statements retain their original universes, hypotheses and actual maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w w' t t'
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

section General
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  {D : Type t} [Category.{t'} D] [HasColimitsOfShape D AddCommGrpCat.{v}]

/-- Forgetting a sheaf's scalar action commutes with colimits. -/
instance toSheaf_preservesColimitsOfShape :
    PreservesColimitsOfShape D (SheafOfModules.toSheaf.{v} R) where
  preservesColimit {F} := by
    let L := _root_.PresheafOfModules.sheafification (𝟙 R.obj)
    let G := SheafOfModules.toSheaf.{v} R
    let P := F ⋙ SheafOfModules.forget R
    have : PreservesColimit P (L ⋙ G) := by
      change PreservesColimit P
        (_root_.PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{v})
      infer_instance
    let h := isColimitOfPreserves L (colimit.isColimit P)
    have : PreservesColimit (P ⋙ L) G :=
      preservesColimit_of_preserves_colimit_cocone h
        (isColimitOfPreserves (L ⋙ G) (colimit.isColimit P))
    let e : P ⋙ L ≅ F := Functor.isoWhiskerLeft F
      (asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit)
    exact preservesColimit_of_iso_diagram G e

/-- Epimorphisms remain epimorphisms after forgetting the scalar action. -/
instance toSheaf_preservesEpimorphisms :
    (SheafOfModules.toSheaf.{v} R).PreservesEpimorphisms := by
  let : PreservesFiniteColimits (SheafOfModules.toSheaf.{v} R) := ⟨fun _ => inferInstance⟩
  infer_instance

variable [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{v})]

/-- An epimorphism of module sheaves is locally surjective. -/
instance isLocallySurjective_of_epi {M N : SheafOfModules.{v} R}
    (f : M ⟶ N) [Epi f] : _root_.PresheafOfModules.IsLocallySurjective J f.val :=
  (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{v}
    ((SheafOfModules.toSheaf R).map f)).mpr inferInstance

end General

end SheafOfModules
