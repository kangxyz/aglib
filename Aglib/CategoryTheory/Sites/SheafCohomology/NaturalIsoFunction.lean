/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.MapIsoInjection

/-! # Complete cohomology-function transport of a whole natural isomorphism

The original functors, whole natural isomorphism, original component map and
literal H dictionaries are fixed before evaluating at any geometric object.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Sheaf

universe u v w e d t

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]
  {D : Type d} [Category.{t} D]
  {F G : D ⥤ Sheaf J AddCommGrpCat.{w}}

/-- Original cohomology of the component of the specified whole natural iso. -/
def H.naturalIsoFunction (α : F ≅ G) (M : D) (q : ℕ) :
    H.{e} (F.obj M) q → H.{e} (G.obj M) q :=
  H.map (α.hom.app M) q

/-- Construct component invertibility and literal-map injectivity while
both functors and their objects are still variables. -/
theorem H.naturalIsoFunction_injective (α : F ≅ G) (M : D) (q : ℕ) :
    Function.Injective (H.naturalIsoFunction α M q) :=
  H.map_injective_of_isIso (α.hom.app M) q

end CategoryTheory.Sheaf
