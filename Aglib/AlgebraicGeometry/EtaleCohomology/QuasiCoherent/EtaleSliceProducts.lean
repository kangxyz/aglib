/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CechChange
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Original étale-slice products in the scheme slice

The functor is the original étale inclusion followed by the native iterated
slice equivalence. Its product comparisons retain the original arrows.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u a b w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable {X : Scheme.{u}} (W : X.Etale)

/-- The original inclusion from the étale slice to schemes over its underlying scheme. -/
def etaleSliceToScheme : Over W ⥤ Over W.left :=
  Over.post (Etale.forget X) ⋙ Over.iteratedSliceForward ((Etale.forget X).obj W)

instance etaleSliceToScheme_preservesFiniteProducts :
    PreservesFiniteProducts (etaleSliceToScheme W) := by
  let : PreservesFiniteLimits (Etale.forget X) := inferInstance
  let : PreservesFiniteLimits
      (Over.iteratedSliceForward ((Etale.forget X).obj W)) :=
    inferInstanceAs (PreservesFiniteLimits
      (Over.iteratedSliceEquiv ((Etale.forget X).obj W)).functor)
  dsimp [etaleSliceToScheme]
  infer_instance

/-- The original base-arrow equation identifies the two slice descriptions. -/
def etaleSliceBaseIso (T : Over W) :
    (Etale.forget X).obj T.left ≅
      (Over.map W.hom).obj ((etaleSliceToScheme W).obj T) :=
  Over.isoMk (Iso.refl _) (by
    dsimp [etaleSliceToScheme]
    simpa using Over.w ((Etale.forget X).map T.hom))

/-- Restricting original coefficients through the two native slice descriptions agrees. -/
def etaleSliceCoefficientIso {A : Type a} [Category.{b} A]
    (P : (Over X)ᵒᵖ ⥤ A) :
    (Over.forget W).op ⋙ ((Etale.forget X).op ⋙ P) ≅
      (etaleSliceToScheme W).op ⋙ ((Over.map W.hom).op ⋙ P) :=
  NatIso.ofComponents (fun T => P.mapIso (etaleSliceBaseIso W T.unop).op.symm) (by
    intro T S f
    change P.map ((Etale.forget X).map f.unop.left).op ≫
        P.map (etaleSliceBaseIso W S.unop).inv.op =
      P.map (etaleSliceBaseIso W T.unop).inv.op ≫
        P.map ((Over.map W.hom).map ((etaleSliceToScheme W).map f.unop)).op
    rw [← P.map_comp, ← P.map_comp]
    apply P.congr_map
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    simp [etaleSliceBaseIso, etaleSliceToScheme])

/-- Actual finite-family Čech comparison from the small étale slice to schemes. -/
def etaleSliceCechIso {A : Type a} [Category.{b} A] [Preadditive A]
    [HasProducts.{w} A] {ι : Type w} (U : ι → Over W)
    (P : (Over X)ᵒᵖ ⥤ A) :
    (CategoryTheory.cechComplexFunctor U).obj
      ((Over.forget W).op ⋙ ((Etale.forget X).op ⋙ P)) ≅
    (CategoryTheory.cechComplexFunctor
      (fun i => (etaleSliceToScheme W).obj (U i))).obj ((Over.map W.hom).op ⋙ P) :=
  (CategoryTheory.cechComplexFunctor U).mapIso (etaleSliceCoefficientIso W P) ≪≫
    CategoryTheory.Cech.cechComplexProductChangeIso (etaleSliceToScheme W) U
      ((Over.map W.hom).op ⋙ P)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
