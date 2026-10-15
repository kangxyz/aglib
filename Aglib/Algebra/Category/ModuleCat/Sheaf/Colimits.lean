/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Colimits under native scalar forgetting for module sheaves

The original functor `SheafOfModules.toSheaf` preserves colimits by forming
presheaf colimits and sheafifying. Finite-colimit preservation is bundled
for exact-functor and Ext consumers; the components and maps are unchanged.

The colimit proof is extracted from `Scheme.Modules.Epimorphisms`, with its
ringed-site hypotheses and independent universes retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

universe u v w w' t t'

variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Forgetting a module sheaf's scalar action preserves colimits of the specified shape. -/
instance toSheaf_preservesColimitsOfShape {D : Type t} [Category.{t'} D]
    [HasColimitsOfShape D AddCommGrpCat.{v}] :
    PreservesColimitsOfShape D (SheafOfModules.toSheaf.{v} R) where
  preservesColimit {F} := by
    let L := PresheafOfModules.sheafification (𝟙 R.obj)
    let G := SheafOfModules.toSheaf.{v} R
    let P := F ⋙ SheafOfModules.forget R
    have : PreservesColimit P (L ⋙ G) := by
      change PreservesColimit P
        (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{v})
      infer_instance
    let h := isColimitOfPreserves L (colimit.isColimit P)
    have : PreservesColimit (P ⋙ L) G :=
      preservesColimit_of_preserves_colimit_cocone h
        (isColimitOfPreserves (L ⋙ G) (colimit.isColimit P))
    let e : P ⋙ L ≅ F := Functor.isoWhiskerLeft F
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit)
    exact preservesColimit_of_iso_diagram G e

/-- The same native scalar-forgetting functor preserves finite colimits. -/
instance toSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{v} R) :=
  ⟨fun _ => inferInstance⟩

/-- Actual module-sheaf epimorphisms remain epimorphisms after scalar forgetting. -/
instance toSheaf_preservesEpimorphisms :
    (SheafOfModules.toSheaf.{v} R).PreservesEpimorphisms := by
  infer_instance

end SheafOfModules
