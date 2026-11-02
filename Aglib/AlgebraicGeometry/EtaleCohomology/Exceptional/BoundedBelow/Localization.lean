/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.Derived
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Normalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsion
public import Aglib.CategoryTheory.Triangulated.VertexTransport

/-! # Original localization triangles after bounded-below exceptional direct image

The ambient functor here retains its specified compactification. Its native
triangulated structure maps the original localization triangle. Choice
independence is asserted only on the previously constructed torsion range.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wZ wX wS wM

variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The original ambient functor through a specified compactification.
No ambient compactification-independence assertion is made. -/
abbrev moduleCompactificationAmbientFunctor (C : Hom.DenseCompactification f) :
    DerivedCategory.Plus (ModuleSheaf X Λ) ⥤ DerivedCategory.Plus (ModuleSheaf S Λ) :=
  moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p

variable [CompactSpace S] [QuasiSeparatedSpace S]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- An ambient representative of the chosen exceptional functor, retaining its choice. -/
abbrev moduleExceptionalChosenAmbientFunctor :=
  moduleCompactificationAmbientFunctor f Λ (moduleExceptionalCompactification f)

variable {U Z : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i] (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]

/-- Map the actual original localization triangle, retaining every original arrow. -/
def moduleExceptionalLocalizationRawTriangle
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    Triangle (DerivedCategory.Plus (ModuleSheaf S Λ)) :=
  (moduleExceptionalChosenAmbientFunctor f Λ).mapTriangle.obj
    (moduleDerivedLocalizationTriangle j Λ i hcomp K.obj)

/-- Native triangulated direct image preserves the original distinguished triangle. -/
theorem moduleExceptionalLocalizationRawTriangle_distinguished
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    moduleExceptionalLocalizationRawTriangle f Λ j i hcomp K ∈
      distTriang (DerivedCategory.Plus (ModuleSheaf S Λ)) :=
  (moduleExceptionalChosenAmbientFunctor f Λ).map_distinguished _
    (moduleDerivedLocalizationTriangle_distinguished j Λ i hcomp K.obj)

end AlgebraicGeometry.Scheme.EtaleCohomology
