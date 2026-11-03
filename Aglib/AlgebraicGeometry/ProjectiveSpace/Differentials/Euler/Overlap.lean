/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.Overlap.Compatibility

/-!
# The original relative Euler overlap square

The compatibility construction is shared in the imported module. The literal indexed view uses
one transparent equation on the same original open immersions, module objects and local arrows.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

/-- The original four-edge equation on the same chosen overlap of two open immersions. -/
def eulerOverlapEquation {U V X : Scheme.{u}} (j : U ⟶ X) (a : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion a] (M N : X.Modules)
    (f : M.restrict j ⟶ N.restrict j) (g : M.restrict a ⟶ N.restrict a) : Prop :=
  (Scheme.Modules.restrictFunctor (pullback.fst j a)).map f ≫
      (Scheme.Modules.overlapRestrictIso j a).hom.app N =
    (Scheme.Modules.overlapRestrictIso j a).hom.app M ≫
      (Scheme.Modules.restrictFunctor (pullback.snd j a)).map g

/-- Interpret the existing whole compatibility law before specializing the original schemes. -/
private theorem eulerOverlapEquation_of_compatible
    {X : Scheme.{u}} {I : Type v} {Y : I → Scheme.{u}}
    (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)] (M N : X.Modules)
    (f : ∀ i, M.restrict (a i) ⟶ N.restrict (a i))
    (h : Scheme.Modules.InternalHom.RestrictionHomCompatible a M N f) (i k : I) :
    eulerOverlapEquation (a i) (a k) M N (f i) (f k) := by
  exact Scheme.Modules.InternalHom.restrictionHomCompatible_eq a M N f h i k

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The literal actual relative Euler chart arrows agree through the native pullback-overlap
restriction comparison. -/
theorem eulerDifferentialOnPolynomialChart_overlap (i k : ι) :
    eulerOverlapEquation (eulerPolynomialChart R ι i) (eulerPolynomialChart R ι k)
      (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))
      (eulerMiddle R ι) (eulerDifferentialOnPolynomialChart R ι i)
      (eulerDifferentialOnPolynomialChart R ι k) := by
  have hcompatible := eulerDifferentialOnPolynomialChart_compatible R ι
  have hoverlap := eulerOverlapEquation_of_compatible
    (eulerPolynomialChart R ι)
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι))
    (eulerMiddle R ι) (eulerDifferentialOnPolynomialChart R ι) hcompatible i k
  exact hoverlap

end AlgebraicGeometry.ProjectiveSpace
