/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AtIdeal.Data

/-!
# The original chart factor at its literal quotient ideal

The genuine ideal transport is the original chart map when the ideal
equality is reflexive. The same original composed factor is recorded
before substituting any principal or isomorphic chart construction.
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

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance chartReflexiveStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ}
  [IsClosedImmersion i] {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)
  (J : InjectiveResolution (relativeCanonicalModule p n))

/-- Reflexive genuine ideal transport has exactly the original chart hom. -/
theorem canonicalCommonModelChartHomologyIsoAtIdeal_self :
    (canonicalCommonModelChartHomologyIsoAtIdeal i p n d J C
      (Ideal.ofList C.regularList) rfl).hom =
        (canonicalCommonModelChartHomologyIso i p n d J C).hom := rfl

/-- The original factor on its literal quotient is the original untransported chart arrow. -/
theorem canonicalChartModelFactorAtIdeal_self (c : ℕ) (hc : C.regularList.length = c) :
    canonicalChartModelFactorAtIdeal C J (Ideal.ofList C.regularList) rfl c hc =
      (canonicalCommonModelChartHomologyIso i p n d J C).hom :=
  (canonicalChartModelFactorAtIdeal_eq C J (Ideal.ofList C.regularList) rfl c hc).trans
    (canonicalCommonModelChartHomologyIsoAtIdeal_self C J)

/-- The same original composed equation at the literal ideal, before chart substitution. -/
theorem canonicalChartModelFactorAtIdeal_self_formula (c : ℕ) (hc : C.regularList.length = c) :
    letI := canonicalChartCoefficientQuasicoherent C c hc
    (canonicalChartModelPrefactorAtIdeal C J (Ideal.ofList C.regularList) rfl c hc).hom ≫
      regularListCanonicalModelMapAt C.α (Ideal.ofList C.regularList) c
        (canonicalAmbientChartResolution J C.jP) (canonicalChartCoefficientGammaFrame C c hc)
        (canonicalChartDeterminantAtIdeal C (Ideal.ofList C.regularList) rfl c hc)
        C.regularList C.weaklyRegular rfl hc ≫
      (canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList C.regularList) rfl).inv =
    (canonicalCommonModelChartHomologyIso i p n d J C).hom :=
  (canonicalChartModelFactorAtIdeal_formula C J (Ideal.ofList C.regularList) rfl c hc).symm.trans
    (canonicalChartModelFactorAtIdeal_self C J c hc)

end AlgebraicGeometry.Scheme.Modules
