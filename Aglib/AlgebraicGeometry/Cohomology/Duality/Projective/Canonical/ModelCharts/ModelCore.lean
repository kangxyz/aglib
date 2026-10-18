/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AtIdeal.Reflexive

/-!
# The shared original chart model core

The original model arrow is stored with its original coefficient frame,
determinant and fixed resolution. Its literal representation is used in
the local model calculations; the whole chart factor retains this getter.
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
local instance chartCoreStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

local instance {A : CommRingCat.{u}} (I : Ideal A) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
      A ⟶ CommRingCat.of (A ⧸ I))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ}
  [IsClosedImmersion i] {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)
  (J : InjectiveResolution (relativeCanonicalModule p n))

/-- The original fixed-resolution canonical arrow with its original chart data. -/
def canonicalChartModelCoreAtDegree (c : ℕ) (hc : C.regularList.length = c) :
    regularListModelTopHomologyAt (Ideal.ofList C.regularList)
        (canonicalAmbientChartResolution J C.jP) c ⟶
      regularListTangentTopAt C.α (Ideal.ofList C.regularList) d := by
  letI := canonicalChartCoefficientQuasicoherent C c hc
  exact regularListCanonicalModelMapAt C.α (Ideal.ofList C.regularList) c
    (canonicalAmbientChartResolution J C.jP) (canonicalChartCoefficientGammaFrame C c hc)
    (canonicalChartDeterminantAtIdeal C (Ideal.ofList C.regularList) rfl c hc)
    C.regularList C.weaklyRegular rfl hc

omit [IsClosedImmersion i] in
/-- The core getter is literally the same original native model arrow. -/
theorem canonicalChartModelCoreAtDegree_representation (c : ℕ) (hc : C.regularList.length = c) :
    letI := canonicalChartCoefficientQuasicoherent C c hc
    canonicalChartModelCoreAtDegree C J c hc =
      regularListCanonicalModelMapAt C.α (Ideal.ofList C.regularList) c
        (canonicalAmbientChartResolution J C.jP) (canonicalChartCoefficientGammaFrame C c hc)
        (canonicalChartDeterminantAtIdeal C (Ideal.ofList C.regularList) rfl c hc)
        C.regularList C.weaklyRegular rfl hc := rfl

/-- The whole original chart arrow uses precisely the three original shared getters. -/
theorem canonicalChartModelCoreAtDegree_factor (c : ℕ) (hc : C.regularList.length = c) :
    (canonicalChartModelPrefactorAtIdeal C J (Ideal.ofList C.regularList) rfl c hc).hom ≫
        canonicalChartModelCoreAtDegree C J c hc ≫
        (canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList C.regularList) rfl).inv =
      (canonicalCommonModelChartHomologyIso i p n d J C).hom :=
  canonicalChartModelFactorAtIdeal_self_formula C J c hc

end AlgebraicGeometry.Scheme.Modules
