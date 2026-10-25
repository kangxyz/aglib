/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.RelativePullbackCoefficient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartGeometricBaseChange
public import Mathlib.CategoryTheory.Filtered.Connected

/-! # Original fixed coefficients on neighborhoods in an arbitrary-base affine chart -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) (f : X ⟶ S)

local instance : IsConnected (GeometricEtaleNeighborhood R Ω) :=
  IsFiltered.isConnected (GeometricEtaleNeighborhood R Ω)

/-- The actual geometric inverse scheme diagram, with the double-op reindexing explicit. -/
def chartCoefficientDiagram : GeometricEtaleNeighborhood R Ω ⥤ Scheme.{u}ᵒᵖ :=
  (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse ⋙
    (chartGeometricBaseChangedDiagram R Ω j f ⋙ Over.forget X).op

/-- The structural arrows of the actual geometric diagram. -/
def chartCoefficientBaseCone : Cone (chartCoefficientDiagram R Ω j f) :=
  (relativeCoefficientBaseCone (chartGeometricBaseChangedDiagram R Ω j f)).whisker
    (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse

/-- The original strict-local base-change cone, in the coefficient direction. -/
def chartCoefficientLimitCocone : Cocone (chartCoefficientDiagram R Ω j f) :=
  (((Over.forget X).mapCone (chartGeometricBaseChangedCone R Ω j f)).op).whisker
    (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse

/-- The fixed original sheaf on the actual geometric-neighborhood system. -/
def chartPullbackCoefficientSystem (F : AbelianSheaf.{u, u + 1} X) :
    DiagramCoefficientSystem (chartCoefficientDiagram R Ω j f) :=
  pullbackCoefficientSystem _ (chartCoefficientBaseCone R Ω j f) F

/-- The actual coefficient colimit is the literal strict-local structural pullback.
No cohomological continuity theorem is used. -/
def chartPullbackLimitCoefficientIso (F : AbelianSheaf.{u, u + 1} X) :
    colimit (coneCoefficientFunctor (chartCoefficientDiagram R Ω j f)
      (chartCoefficientLimitCocone R Ω j f) (chartPullbackCoefficientSystem R Ω j f F)) ≅
        (inverseImage (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).obj F :=
  pullbackLimitCoefficientIso _ (chartCoefficientBaseCone R Ω j f)
    (chartCoefficientLimitCocone R Ω j f) (chartGeometricBaseChangedCone R Ω j f).pt.hom.op
    (fun i => relativeCoefficient_cone_composite (chartGeometricBaseChangedDiagram R Ω j f)
      (chartGeometricBaseChangedCone R Ω j f)
      ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj i)) F

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
