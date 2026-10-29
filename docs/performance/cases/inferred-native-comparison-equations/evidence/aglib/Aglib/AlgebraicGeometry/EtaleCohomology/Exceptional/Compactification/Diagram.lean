/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompositionCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.Coherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.Isomorphism
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The original contravariant compactification diagram

At a dense compactification the value is the original open extension followed
by its proper derived direct image, restricted only at the source to actual
bounded-below torsion homology. A refinement gives the previously constructed
original unit comparison, followed by the original structural direct-image
identification. The actual identity and composition equations prove that this
is a functor, and actual proper base change makes its arrows invertible.

The source and target derived models are independent. A consistent family of
middle derived models is explicit across the compactification category. The
target here is the ambient native bounded-below category, not yet its torsion
subcategory; full exceptional composition and base change are later steps.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

section Value

variable (C : Hom.DenseCompactification f)
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The specified compactification value uses only its own actual middle realization. -/
def moduleCompactificationFunctor :
    (moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
      DerivedCategory.Plus (ModuleSheaf S Λ) :=
  (moduleTorsionCohomologyPlus X Λ).ι ⋙
    moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p

end Value

variable [middleModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
variable {f}

/-- The actual contravariant transition attached to a proper refinement. -/
def moduleCompactificationTransition {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    moduleCompactificationFunctor f Λ D ⟶ moduleCompactificationFunctor f Λ C :=
  Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
    (imageComparison (moduleDerivedRefinementComparison a Λ)
      (moduleDerivedRefinementDirectImageIso Λ a))

/-- Components retain the original refinement map and direct-image identification. -/
theorem moduleCompactificationTransition_app {C D : Hom.DenseCompactification f}
    (a : C ⟶ D) (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    (moduleCompactificationTransition Λ a).app K =
      (moduleDerivedDirectImage Λ D.p).map ((moduleDerivedRefinementComparison a Λ).app K.obj) ≫
        (moduleDerivedRefinementDirectImageIso Λ a).hom.app
          ((moduleDerivedLowerShriek C.j Λ).obj K.obj) :=
  imageComparison_app _ _ K.obj

/-- Identity refinements act by the literal identity natural transformation. -/
theorem moduleCompactificationTransition_id (C : Hom.DenseCompactification f) :
    moduleCompactificationTransition Λ (𝟙 C) = 𝟙 (moduleCompactificationFunctor f Λ C) := by
  have h := imageComparison_id (moduleDerivedRefinementComparison (𝟙 C) Λ)
    (moduleDerivedDirectImageIdIso Λ C.Xbar) (moduleDerivedRefinementDirectImageIso Λ (𝟙 C))
    (moduleDerivedRefinementComparison_id Λ C) (moduleDerivedRefinementDirectImageIso_id Λ C)
  simpa only [moduleCompactificationTransition, moduleCompactificationFunctor,
    Functor.whiskerLeft_id'] using
    congrArg (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι) h

/-- The unchanged original refinement transitions compose contravariantly. -/
theorem moduleCompactificationTransition_comp {C D E : Hom.DenseCompactification f}
    (a : C ⟶ D) (b : D ⟶ E) :
    moduleCompactificationTransition Λ (a ≫ b) =
      moduleCompactificationTransition Λ b ≫ moduleCompactificationTransition Λ a := by
  have h := imageComparison_comp (moduleDerivedRefinementComparison a Λ)
    (moduleDerivedRefinementComparison b Λ) (moduleDerivedRefinementComparison (a ≫ b) Λ)
    (moduleDerivedDirectImageCompIso Λ b.hom a.hom)
    (moduleDerivedRefinementDirectImageIso Λ a) (moduleDerivedRefinementDirectImageIso Λ b)
    (moduleDerivedRefinementDirectImageIso Λ (a ≫ b))
    (moduleDerivedRefinementComparison_comp Λ a b)
    (moduleDerivedRefinementDirectImageIso_comp Λ a b)
  simpa only [moduleCompactificationTransition, moduleCompactificationFunctor,
    Functor.whiskerLeft_comp] using
    congrArg (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι) h

/-- Proper base change makes every original transition invertible on torsion input. -/
instance moduleCompactificationTransition_isIso {C D : Hom.DenseCompactification f}
    (a : C ⟶ D) : IsIso (moduleCompactificationTransition Λ a) := by
  have (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
      IsIso ((moduleCompactificationTransition Λ a).app K) := by
    let : IsIso ((moduleDerivedRefinementComparison a Λ).app K.obj) :=
      moduleDerivedRefinementComparison_isIso a Λ K.obj K.property
    exact imageComparison_isIso_app (moduleDerivedRefinementComparison a Λ)
      (moduleDerivedRefinementDirectImageIso Λ a) K.obj
  exact NatIso.isIso_of_isIso_app _

/-- The original proper-image/open-extension construction is a contravariant
functor on dense compactifications, not merely a collection of isomorphic objects. -/
def moduleCompactificationDiagram :
    (Hom.DenseCompactification f)ᵒᵖ ⥤
      ((moduleTorsionCohomologyPlus X Λ).FullSubcategory ⥤
        DerivedCategory.Plus (ModuleSheaf S Λ)) where
  obj C := moduleCompactificationFunctor f Λ C.unop
  map a := moduleCompactificationTransition Λ a.unop
  map_id C := moduleCompactificationTransition_id Λ C.unop
  map_comp a b := moduleCompactificationTransition_comp Λ b.unop a.unop

/-- Every arrow of the actual compactification diagram is invertible. -/
instance moduleCompactificationDiagram_map_isIso
    (C D : (Hom.DenseCompactification f)ᵒᵖ) (a : C ⟶ D) :
    IsIso ((moduleCompactificationDiagram Λ).map a) :=
  moduleCompactificationTransition_isIso Λ a.unop

end AlgebraicGeometry.Scheme.EtaleCohomology
