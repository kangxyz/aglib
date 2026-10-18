/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.AffineDeterminant
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Concentration
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalCharts.Quotient
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-!
# Native canonical purity on the actual smooth closed charts

The chart supplier derives the regular list, differential bases, and local
codimension equality from smoothness. The original relative differential
and exterior-power restriction maps identify the coefficient and cotangent
lines. The native derived closed-adjoint open comparison then transports
the affine canonical map to the restriction of the independently installed
global object.

The homology concentration follows without comparing the chart maps with
one another. Their actual overlap equality is required separately to glue
the canonical homology map.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance canonicalChartStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i]
  (n d : ℕ) {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)

/-- The actual ambient relative top-differential coefficient. -/
abbrev relativeCanonicalModule : P.Modules :=
  moduleExteriorPower P (relativeDifferentialSheaf p) n

/-- The independently installed right adjoint at that actual coefficient single. -/
abbrev closedImmersionCanonicalValue : DerivedCategory.Plus X.Modules :=
  (closedImmersionRightAdjoint i).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj (relativeCanonicalModule p n))

private def chartAmbientTopIso :
    (relativeCanonicalModule p n).restrict C.jP ≅
      moduleExteriorPower (Spec C.A) (relativeDifferentialSheaf (Spec.map C.α)) n := by
  let := C.openP
  let := C.openY
  exact (moduleExteriorPowerRestrictionIso C.jP (relativeDifferentialSheaf p) n).symm ≪≫
    (moduleExteriorPowerFunctor (Spec C.A) n).mapIso
      (relativeDifferentialOpenSquareIso p C.jP (Spec.map C.α) C.jY C.ambientSquare.symm)

omit [IsClosedImmersion i] in
private theorem chartSourceSquare :
    C.jX ≫ (i ≫ p) = Spec.map (C.α ≫ C.σ) ≫ C.jY := by
  rw [Spec.map_comp, Category.assoc, C.ambientSquare, ← Category.assoc, ← C.closedSquare,
    Category.assoc]

private def chartSourceTopIso :
    (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict C.jX ≅
      moduleExteriorPower (Spec C.B)
        (relativeDifferentialSheaf (Spec.map (C.α ≫ C.σ))) d := by
  let := C.openX
  let := C.openY
  exact (moduleExteriorPowerRestrictionIso C.jX (relativeDifferentialSheaf (i ≫ p)) d).symm ≪≫
    (moduleExteriorPowerFunctor (Spec C.B) d).mapIso
      (relativeDifferentialOpenSquareIso (i ≫ p) C.jX (Spec.map (C.α ≫ C.σ)) C.jY
        (chartSourceSquare i p n d C))

/-- The actual global right-adjoint object on a genuine quotient chart has the required
single degree and the restriction of the original cotangent determinant. -/
@[no_expose] def smoothClosedImmersionChartCanonicalIso :
    let Q := C.quotientChart
    (restrictFunctor Q.jX).rightDerivedFunctorPlus.obj (closedImmersionCanonicalValue i p n) ≅
      (DerivedCategory.Plus.singleFunctor (Spec Q.B).Modules ((n : ℤ) - d)).obj
        ((moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict Q.jX) := by
  let Q := C.quotientChart
  let := Q.openX
  let := Q.openP
  let := IsClosedImmersion.spec_of_surjective Q.σ Q.surjective
  let bA := Q.ambientBasis.reindex (finCongr Q.dimension_eq)
  let L := relativeCanonicalModule p n
  let ΩA := relativeDifferentialSheaf (Spec.map Q.α)
  let ΩB := relativeDifferentialSheaf (Spec.map (Q.α ≫ Q.σ))
  let eA := chartAmbientTopIso i p n d Q
  let eX := chartSourceTopIso i p n d Q
  let eDegree : moduleExteriorPower (Spec Q.A) ΩA n ≅
      moduleExteriorPower (Spec Q.A) ΩA (Q.regularList.length + d) :=
    eqToIso (congrArg (moduleExteriorPower (Spec Q.A) ΩA) Q.dimension_eq)
  have hc : (Q.regularList.length : ℤ) = (n : ℤ) - d := by
    have h := Q.dimension_eq
    omega
  let eCodim :
      (DerivedCategory.Plus.singleFunctor (Spec Q.B).Modules
        (Q.regularList.length : ℤ)).obj (moduleExteriorPower (Spec Q.B) ΩB d) ≅
      (DerivedCategory.Plus.singleFunctor (Spec Q.B).Modules ((n : ℤ) - d)).obj
        (moduleExteriorPower (Spec Q.B) ΩB d) :=
    eqToIso (congrArg (fun c : ℤ => (DerivedCategory.Plus.singleFunctor (Spec Q.B).Modules c).obj
      (moduleExteriorPower (Spec Q.B) ΩB d)) hc)
  let eCoefficient := ((restrictFunctor Q.jP).rightDerivedFunctorPlusSingleIso 0).app L ≪≫
    (DerivedCategory.Plus.singleFunctor (Spec Q.A).Modules 0).mapIso (eA ≪≫ eDegree)
  exact (derivedClosedImmersionRightAdjointOpenIso Q.jX (Spec.map Q.σ) i Q.jP
    Q.cartesian).app ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L) ≪≫
    (closedImmersionRightAdjoint (Spec.map Q.σ)).rightDerivedFunctorPlus.mapIso eCoefficient ≪≫
    affineRegularListCanonicalIso Q.α Q.regularList Q.weaklyRegular
      Q.ambientFormallySmooth Q.sourceFormallySmooth bA Q.sourceBasis ≪≫
    eCodim ≪≫
    (DerivedCategory.Plus.singleFunctor (Spec Q.B).Modules ((n : ℤ) - d)).mapIso eX.symm

end AlgebraicGeometry.Scheme.Modules
