/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.RelativePullbackCoefficient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodBaseChange
public import Mathlib.CategoryTheory.Filtered.Connected

/-! # Original fixed coefficients on the actual geometric-neighborhood system -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

local instance : IsConnected (GeometricEtaleNeighborhood R Ω) :=
  IsFiltered.isConnected (GeometricEtaleNeighborhood R Ω)

/-- The actual geometric inverse scheme diagram, with the double-op reindexing explicit. -/
def geometricCoefficientDiagram : GeometricEtaleNeighborhood R Ω ⥤ Scheme.{u}ᵒᵖ :=
  (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse ⋙
    (baseChangedDiagram R Ω f ⋙ Over.forget X).op

/-- The structural arrows of the actual geometric diagram. -/
def geometricCoefficientBaseCone : Cone (geometricCoefficientDiagram R Ω f) :=
  (relativeCoefficientBaseCone (baseChangedDiagram R Ω f)).whisker
    (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse

/-- The original strict-local base-change cone, in the coefficient direction. -/
def geometricCoefficientLimitCocone : Cocone (geometricCoefficientDiagram R Ω f) :=
  (((Over.forget X).mapCone (baseChangedCone R Ω f)).op).whisker
    (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse

/-- The fixed original sheaf on the actual geometric-neighborhood system. -/
def geometricPullbackCoefficientSystem (F : AbelianSheaf.{u, u + 1} X) :
    DiagramCoefficientSystem (geometricCoefficientDiagram R Ω f) :=
  pullbackCoefficientSystem _ (geometricCoefficientBaseCone R Ω f) F

/-- The actual coefficient colimit is the literal strict-local structural pullback.
No cohomological continuity theorem is used. -/
def geometricPullbackLimitCoefficientIso (F : AbelianSheaf.{u, u + 1} X) :
    colimit (coneCoefficientFunctor (geometricCoefficientDiagram R Ω f)
      (geometricCoefficientLimitCocone R Ω f) (geometricPullbackCoefficientSystem R Ω f F)) ≅
        (inverseImage (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f)).obj F :=
  pullbackLimitCoefficientIso _ (geometricCoefficientBaseCone R Ω f)
    (geometricCoefficientLimitCocone R Ω f) (baseChangedCone R Ω f).pt.hom.op
    (fun i => relativeCoefficient_cone_composite (baseChangedDiagram R Ω f)
      (baseChangedCone R Ω f) ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj i)) F

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
