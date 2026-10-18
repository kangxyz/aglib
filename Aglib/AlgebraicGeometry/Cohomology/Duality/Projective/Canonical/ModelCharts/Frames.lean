/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Charts

/-!
# Shared original coefficient data of a genuine smooth closed chart

These are the same ambient basis, differential restriction, unit frame and
sections frame used by the original chart canonical arrow. Sharing their
native types preserves the actual data through ideal and degree transport.
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

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ}
  {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)

/-- The same original ambient basis reindexed by the actual chart rank equation. -/
def canonicalChartAmbientBasisAtDegree (c : ℕ) (hc : C.regularList.length = c) :
    Module.Basis (Fin (c + d)) C.A (CommRingCat.KaehlerDifferential C.α) :=
  C.quotientChart.ambientBasis.reindex
    (finCongr (C.quotientChart.dimension_eq.trans (congrArg (fun k => k + d) hc)))

/-- Original ambient differential restriction followed by its genuine exterior-degree change. -/
def canonicalChartCoefficientAtDegree (c : ℕ) (hc : C.regularList.length = c) :
    (relativeCanonicalModule p n).restrict C.jP ≅
      moduleExteriorPower (Spec C.A) (relativeDifferentialSheaf (Spec.map C.α)) (c + d) :=
  ((moduleExteriorPowerRestrictionIso C.quotientChart.jP (relativeDifferentialSheaf p) n).symm ≪≫
    (moduleExteriorPowerFunctor (Spec C.quotientChart.A) n).mapIso
      (relativeDifferentialOpenSquareIso p C.quotientChart.jP (Spec.map C.quotientChart.α)
        C.quotientChart.jY C.quotientChart.ambientSquare.symm)) ≪≫
    eqToIso (congrArg
      (moduleExteriorPower (Spec C.quotientChart.A)
        (relativeDifferentialSheaf (Spec.map C.quotientChart.α)))
      (C.quotientChart.dimension_eq.trans (congrArg (fun k => k + d) hc)))

/-- The coefficient unit frame is the same original differential frame. -/
def canonicalChartCoefficientUnitFrame (c : ℕ) (hc : C.regularList.length = c) :
    (relativeCanonicalModule p n).restrict C.jP ≅ SheafOfModules.unit (Spec C.A).ringCatSheaf :=
  canonicalChartCoefficientAtDegree C c hc ≪≫
    affineRelativeTopFrame C.quotientChart.α (c + d) (canonicalChartAmbientBasisAtDegree C c hc)

/-- The original chart coefficient sheaf is quasicoherent by this actual unit frame. -/
theorem canonicalChartCoefficientQuasicoherent (c : ℕ) (hc : C.regularList.length = c) :
    ((relativeCanonicalModule p n).restrict C.jP).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec C.A).ringCatSheaf).prop_of_iso
    (tildeSelf ≪≫ (canonicalChartCoefficientUnitFrame C c hc).symm) inferInstance

/-- The original global-sections frame induced by that same coefficient unit frame. -/
def canonicalChartCoefficientGammaFrame (c : ℕ) (hc : C.regularList.length = c) :
    moduleSpecΓFunctor.obj ((relativeCanonicalModule p n).restrict C.jP) ≅
      ModuleCat.of C.A C.A :=
  moduleSpecΓFunctor.mapIso (canonicalChartCoefficientUnitFrame C c hc) ≪≫
    moduleSpecΓFunctor.mapIso (tildeSelf (R := C.quotientChart.A)).symm ≪≫
      (tilde.toTildeΓNatIso (R := C.quotientChart.A)).symm.app
        (ModuleCat.of C.quotientChart.A C.quotientChart.A)


/-- The actual quotient source has its original literal regular-list quotient domain. -/
theorem canonicalChartQuotientSource_eq :
    (C.quotientChart.jX : Spec (regularListQuotientRing C.regularList) ⟶ X) =
      C.quotientSource := rfl

/-- The original source basis on a genuinely equal literal quotient ideal. -/
def canonicalChartQuotientSourceBasis (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    Module.Basis (Fin d) (CommRingCat.of (C.A ⧸ I))
      (CommRingCat.KaehlerDifferential (C.α ≫
        (CommRingCat.ofHom (Ideal.Quotient.mk I) : C.A ⟶ CommRingCat.of (C.A ⧸ I)))) := by
  subst I
  exact C.quotientChart.sourceBasis

/-- The same original quotient has native source formal smoothness in the literal type. -/
theorem canonicalChartQuotientSourceFormallySmooth (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    (C.α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
      C.A ⟶ CommRingCat.of (C.A ⧸ I))).hom.FormallySmooth := by
  subst I
  exact C.quotientChart.sourceFormallySmooth


end AlgebraicGeometry.Scheme.Modules
