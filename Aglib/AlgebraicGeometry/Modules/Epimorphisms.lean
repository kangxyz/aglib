/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
/-!
# Epimorphisms of module sheaves are locally surjective

Forgetting the module structure preserves colimits of sheaves: form a colimit
as a presheaf and sheafify, and use that this construction commutes with
forgetting to additive sheaves. In particular an epimorphism of module sheaves
is locally surjective on sections. This does not assert that it is surjective
on sections over a fixed open set.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w w' t t'
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

section General
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  {D : Type t} [Category.{t'} D] [HasColimitsOfShape D AddCommGrpCat.{v}]

/-- Compatibility name for the native scalar-forgetting colimit instance. -/
abbrev toSheaf_preservesColimitsOfShape :
    PreservesColimitsOfShape D (SheafOfModules.toSheaf.{v} R) :=
  SheafOfModules.toSheaf_preservesColimitsOfShape R

/-- Compatibility name for native scalar forgetting of epimorphisms. -/
abbrev toSheaf_preservesEpimorphisms :
    (SheafOfModules.toSheaf.{v} R).PreservesEpimorphisms :=
  SheafOfModules.toSheaf_preservesEpimorphisms R

variable [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{v})]

/-- An epimorphism of module sheaves is locally surjective. -/
instance isLocallySurjective_of_epi {M N : SheafOfModules.{v} R}
    (f : M ⟶ N) [Epi f] : _root_.PresheafOfModules.IsLocallySurjective J f.val :=
  (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{v}
    ((SheafOfModules.toSheaf R).map f)).mpr inferInstance

end General
end AlgebraicGeometry.Scheme.Modules
