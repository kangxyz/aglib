/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.SmallModel.Exact

/-!
# The source-side natural comparison for the exact functor on chosen small models

Essential smallness and the chosen universe remain explicit.

Source: `lean/R5Lab/Aglib/CategoryTheory/SmallModel/FunctorComparison.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `a45205c8f8818f0d28344d44b36756ccb97a3876129d100e03fed7f7b2219f10`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory.ExactCategory (ExactFunctor ExactStructure)
namespace CategoryTheory.ExactCategory.ExactFunctor
universe u v w u' v'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The actual unit of the small-model equivalence compares the two source presentations. -/
def smallModelSourceIso (F : ExactFunctor EC ED) :
    (equivSmallModel.{w} C).functor ⋙ F.smallModel.toFunctor ≅
      F.toFunctor ⋙ (equivSmallModel.{w} D).functor :=
  Functor.isoWhiskerRight (equivSmallModel.{w} C).unitIso.symm
    (F.toFunctor ⋙ (equivSmallModel.{w} D).functor) ≪≫ Functor.leftUnitor _

end CategoryTheory.ExactCategory.ExactFunctor
