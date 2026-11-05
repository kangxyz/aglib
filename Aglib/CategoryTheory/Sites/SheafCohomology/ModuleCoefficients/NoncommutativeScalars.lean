/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.UnderlyingAction
public import Aglib.CategoryTheory.Preadditive.ScalarDiagram
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Original module-valued cohomology over a possibly noncommutative ring

The actual scalar endomorphisms act on the underlying abelian coefficient
functor, where they are additive even when not module-linear. The complete
scalar-diagram construction supplies the original cohomology groups and
coefficient maps with their left module structure. No commutativity or
Noetherianity is required, and no cohomology carrier is replaced.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace ModuleCat.Sheaf

universe u v r e
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

attribute [local instance] hasSheafify

/-- The actual additive cohomology functor applied to whole coefficient diagrams. -/
abbrev cohomologyDiagramFunctor (q : ℕ) :=
  (Functor.whiskeringRight (Sheaf J (ModuleCat.{max u v} R))
    (Sheaf J AddCommGrpCat.{max u v}) AddCommGrpCat.{e}).obj
      (CategoryTheory.Sheaf.functorH J q)

/-- Original sheaf cohomology, with its actual left coefficient action over
an arbitrary ring. Scalars need not be module-linear coefficient maps. -/
def cohomologyOfRing (q : ℕ) :
    Sheaf J (ModuleCat.{max u v} R) ⥤ ModuleCat.{e} R :=
  (cohomologyDiagramFunctor J R q).coefficientModuleDiagram
    (underlying R J) (underlyingScalarAction J R)

/-- The module-valued coefficient map is precisely the original cohomology map. -/
theorem cohomologyOfRing_map_apply {M N : Sheaf J (ModuleCat.{max u v} R)}
    (f : M ⟶ N) (q : ℕ) (x : (cohomologyOfRing J R q).obj M) :
    (cohomologyOfRing J R q).map f x =
      CategoryTheory.Sheaf.H.map ((underlying R J).map f) q x := rfl

/-- Left multiplication is the original cohomology map of the underlying
additive scalar map, without any false linearity claim over the ring. -/
theorem cohomologyOfRing_smul (M : Sheaf J (ModuleCat.{max u v} R))
    (q : ℕ) (a : R) (x : (cohomologyOfRing J R q).obj M) :
    a • x = CategoryTheory.Sheaf.H.map ((underlyingScalar J R a).app M) q x := rfl

/-- The original additive coefficient laws are preserved by the left-module lift. -/
instance cohomologyOfRing_additive (q : ℕ) : (cohomologyOfRing J R q).Additive where
  map_add := by
    intro M N f g
    ext x
    change (CategoryTheory.Sheaf.functorH J q).map
      ((underlying R J).map f + (underlying R J).map g) x = _
    rw [Functor.map_add]
    rfl

/-- Forgetting the scalar action returns the exact original cohomology functor. -/
def cohomologyOfRingForgetIso (q : ℕ) :
    cohomologyOfRing J R q ⋙ forget₂ (ModuleCat.{e} R) AddCommGrpCat.{e} ≅
      underlying R J ⋙ CategoryTheory.Sheaf.functorH J q :=
  Iso.refl _

end ModuleCat.Sheaf
