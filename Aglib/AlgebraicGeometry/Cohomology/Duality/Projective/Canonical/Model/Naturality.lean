/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model.Restriction
public import
  Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FiniteSource.ResolutionNaturality

/-!
# The native common-model homology comparison on actual resolution lifts

The original derived-unit naturality and original homology-factorization
naturality identify the map induced by an actual injective-resolution lift.
In particular the native square-restriction lift retains its original
coefficient morphism, rather than an independently chosen model comparison.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance canonicalModelNaturalityStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {X P : Scheme.{u}} (i : X ⟶ P) [IsClosedImmersion i]
  {L N : P.Modules} {I : InjectiveResolution L} {J : InjectiveResolution N}
  {f : L ⟶ N} (φ : InjectiveResolution.Hom I J f)

/-- An actual resolution lift gives the original native coefficient morphism on homology. -/
theorem closedImmersionModelHomologyIso_naturality (c : ℤ) :
    (closedImmersionModelHomologyIso i I c).hom ≫
        HomologicalComplex.homologyMap
          (((closedImmersionRightAdjoint i).mapHomologicalComplex (.up ℤ)).map φ.hom') c =
      (DerivedCategory.Plus.homologyFunctor X.Modules c).map
          ((closedImmersionRightAdjoint i).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor P.Modules 0).map f)) ≫
        (closedImmersionModelHomologyIso i J c).hom := by
  exact derivedClosedImmersionRightAdjointModelHomologyIso_naturality i φ c

end AlgebraicGeometry.Scheme.Modules
