/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Charts
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Frames
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.Repoint

/-!
# Actual canonical chart arrows from one common ambient model

All chart arrows start at the homology of the independently installed global
right adjoint. Its original native model comparison, exact open restriction,
and original ordinary closed-adjoint open map give the chart model. The local
top map then uses the original inverse normal line and the same normal-first
determinant. One fixed ambient resolution supplies every chart resolution.
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
local instance canonicalCommonModelStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i]
  (n d : ℕ) (J : InjectiveResolution (relativeCanonicalModule p n))
  {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)

/-- The actual ordinary canonical homology arrow on a chart, from the same global model.
No independently supplied purity map or regular-frame family is used. -/
@[no_expose] def canonicalCommonModelChartHomologyIso :
    let Q := C.quotientChart
    ((DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
      (closedImmersionCanonicalValue i p n)).restrict Q.jX ≅
      (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict Q.jX := by
  let Q := C.quotientChart
  let := IsClosedImmersion.spec_of_surjective Q.σ Q.surjective
  let bA := canonicalChartAmbientBasisAtDegree C Q.regularList.length rfl
  let c : ℤ := (n : ℤ) - d
  let L := (relativeCanonicalModule p n).restrict Q.jP
  let J₀ := canonicalAmbientChartResolution J Q.jP
  let ΩB := relativeDifferentialSheaf (Spec.map (Q.α ≫ Q.σ))
  let eA := canonicalChartCoefficientAtDegree C Q.regularList.length rfl
  let eUnit := canonicalChartCoefficientUnitFrame C Q.regularList.length rfl
  let : L.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Q.A).ringCatSheaf).prop_of_iso
      (tildeSelf ≪≫ eUnit.symm) inferInstance
  letI := canonicalChartCoefficientQuasicoherent C Q.regularList.length rfl
  let eΓ := canonicalChartCoefficientGammaFrame C Q.regularList.length rfl
  let Δ := affineRegularListCanonicalDeterminant Q.α Q.regularList Q.weaklyRegular
    Q.ambientFormallySmooth Q.sourceFormallySmooth bA Q.sourceBasis ≪≫
      (pullback (Spec.map Q.σ)).mapIso eA.symm
  have hc : c = (Q.regularList.length : ℤ) := by
    have h := Q.dimension_eq
    dsimp only [c]
    omega
  have hSource : Q.jX ≫ (i ≫ p) = Spec.map (Q.α ≫ Q.σ) ≫ Q.jY := by
    rw [Spec.map_comp, Category.assoc, Q.ambientSquare, ← Category.assoc, ← Q.closedSquare,
      Category.assoc]
  let eX : (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict Q.jX ≅
      moduleExteriorPower (Spec Q.B) ΩB d :=
    (moduleExteriorPowerRestrictionIso Q.jX (relativeDifferentialSheaf (i ≫ p)) d).symm ≪≫
      (moduleExteriorPowerFunctor (Spec Q.B) d).mapIso
        (relativeDifferentialOpenSquareIso (i ≫ p) Q.jX (Spec.map (Q.α ≫ Q.σ)) Q.jY hSource)
  let K₀ := closedImmersionRightAdjointRegularListResolutionComplex Q.regularList J₀
  let eCodim : K₀.homology c ≅ K₀.homology (Q.regularList.length : ℤ) :=
    eqToIso (congrArg (fun k : ℤ => K₀.homology k) hc)
  exact closedImmersionRestrictedModelHomologyIso i J Q.jX c ≪≫
    (HomologicalComplex.homologyFunctor (Spec Q.B).Modules (.up ℤ) c).mapIso
      (closedImmersionModelOpenIso i J Q.jX Q.jP (Spec.map Q.σ) Q.cartesian) ≪≫
    eCodim ≪≫
    regularListCanonicalModelTopHomologyIso Q.regularList Q.weaklyRegular eΓ Q.α J₀ Δ ≪≫
    eX.symm

/-- The original global chart arrow retains its exact native model, coefficient frame,
normal-first determinant and cotangent restriction factors. -/
theorem canonicalCommonModelChartHomologyIso_eq :
    let Q := C.quotientChart
    letI := IsClosedImmersion.spec_of_surjective Q.σ Q.surjective
    let bA := Q.ambientBasis.reindex (finCongr Q.dimension_eq)
    let c : ℤ := (n : ℤ) - d
    let L := (relativeCanonicalModule p n).restrict Q.jP
    let J₀ := canonicalAmbientChartResolution J Q.jP
    let ΩA := relativeDifferentialSheaf (Spec.map Q.α)
    let ΩB := relativeDifferentialSheaf (Spec.map (Q.α ≫ Q.σ))
    let eA₀ : L ≅ moduleExteriorPower (Spec Q.A) ΩA n :=
      (moduleExteriorPowerRestrictionIso Q.jP (relativeDifferentialSheaf p) n).symm ≪≫
        (moduleExteriorPowerFunctor (Spec Q.A) n).mapIso
          (relativeDifferentialOpenSquareIso p Q.jP (Spec.map Q.α) Q.jY Q.ambientSquare.symm)
    let eDegree : moduleExteriorPower (Spec Q.A) ΩA n ≅
        moduleExteriorPower (Spec Q.A) ΩA (Q.regularList.length + d) :=
      eqToIso (congrArg (moduleExteriorPower (Spec Q.A) ΩA) Q.dimension_eq)
    let eA := eA₀ ≪≫ eDegree
    let eUnit := eA ≪≫ affineRelativeTopFrame Q.α (Q.regularList.length + d) bA
    letI : L.IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec Q.A).ringCatSheaf).prop_of_iso
        (tildeSelf ≪≫ eUnit.symm) inferInstance
    let eΓ : moduleSpecΓFunctor.obj L ≅ ModuleCat.of Q.A Q.A :=
      moduleSpecΓFunctor.mapIso eUnit ≪≫ moduleSpecΓFunctor.mapIso (tildeSelf (R := Q.A)).symm ≪≫
        (tilde.toTildeΓNatIso (R := Q.A)).symm.app (ModuleCat.of Q.A Q.A)
    let Δ := affineRegularListCanonicalDeterminant Q.α Q.regularList Q.weaklyRegular
      Q.ambientFormallySmooth Q.sourceFormallySmooth bA Q.sourceBasis ≪≫
        (pullback (Spec.map Q.σ)).mapIso eA.symm
    let hc : c = (Q.regularList.length : ℤ) := by
      have h := Q.dimension_eq
      dsimp only [c]
      omega
    let hSource : Q.jX ≫ (i ≫ p) = Spec.map (Q.α ≫ Q.σ) ≫ Q.jY := by
      rw [Spec.map_comp, Category.assoc, Q.ambientSquare, ← Category.assoc, ← Q.closedSquare,
        Category.assoc]
    let eX : (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict Q.jX ≅
        moduleExteriorPower (Spec Q.B) ΩB d :=
      (moduleExteriorPowerRestrictionIso Q.jX (relativeDifferentialSheaf (i ≫ p)) d).symm ≪≫
        (moduleExteriorPowerFunctor (Spec Q.B) d).mapIso
          (relativeDifferentialOpenSquareIso (i ≫ p) Q.jX (Spec.map (Q.α ≫ Q.σ)) Q.jY hSource)
    let K₀ := closedImmersionRightAdjointRegularListResolutionComplex Q.regularList J₀
    let eCodim : K₀.homology c ≅ K₀.homology (Q.regularList.length : ℤ) :=
      eqToIso (congrArg (fun k : ℤ => K₀.homology k) hc)
    canonicalCommonModelChartHomologyIso i p n d J C =
      closedImmersionRestrictedModelHomologyIso i J Q.jX c ≪≫
      (HomologicalComplex.homologyFunctor (Spec Q.B).Modules (.up ℤ) c).mapIso
        (closedImmersionModelOpenIso i J Q.jX Q.jP (Spec.map Q.σ) Q.cartesian) ≪≫
      eCodim ≪≫
      regularListCanonicalModelTopHomologyIso Q.regularList Q.weaklyRegular eΓ Q.α J₀ Δ ≪≫
      eX.symm := by
  rfl

/-- The same original chart arrow shares its original coefficient data before transport. -/
theorem canonicalCommonModelChartHomologyIso_eq_shared :
    letI := IsClosedImmersion.spec_of_surjective (regularListQuotientMap C.regularList)
      Ideal.Quotient.mk_surjective
    let bA := canonicalChartAmbientBasisAtDegree C C.regularList.length rfl
    let c : ℤ := (n : ℤ) - d
    let L := (relativeCanonicalModule p n).restrict C.jP
    let J₀ := canonicalAmbientChartResolution J C.jP
    let ΩB := relativeDifferentialSheaf (Spec.map (C.α ≫ (regularListQuotientMap C.regularList)))
    let eA := canonicalChartCoefficientAtDegree C C.regularList.length rfl
    let eUnit := canonicalChartCoefficientUnitFrame C C.regularList.length rfl
    letI : L.IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec C.A).ringCatSheaf).prop_of_iso
        (tildeSelf ≪≫ eUnit.symm) inferInstance
    letI := canonicalChartCoefficientQuasicoherent C C.regularList.length rfl
    let eΓ := canonicalChartCoefficientGammaFrame C C.regularList.length rfl
    let hA := C.ambientFormallySmooth
    let hB := canonicalChartQuotientSourceFormallySmooth C (Ideal.ofList C.regularList) rfl
    let bQ := canonicalChartQuotientSourceBasis C (Ideal.ofList C.regularList) rfl
    let Δ := affineRegularListCanonicalDeterminant C.α C.regularList C.weaklyRegular
      hA hB bA bQ ≪≫
        (pullback (Spec.map (regularListQuotientMap C.regularList))).mapIso eA.symm
    let hc : c = (C.regularList.length : ℤ) := by
      have h : n = C.regularList.length + d := C.dimension_eq
      dsimp only [c]
      omega
    let hSource : C.quotientSource ≫ (i ≫ p) =
        Spec.map (C.α ≫ regularListQuotientMap C.regularList) ≫ C.jY := by
      rw [Spec.map_comp, Category.assoc, C.ambientSquare, ← Category.assoc,
        ← C.quotientSource_square, Category.assoc]
    let eX : (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict
        C.quotientSource ≅
        moduleExteriorPower (Spec (regularListQuotientRing C.regularList)) ΩB d :=
      (moduleExteriorPowerRestrictionIso C.quotientSource
        (relativeDifferentialSheaf (i ≫ p)) d).symm ≪≫
        (moduleExteriorPowerFunctor (Spec (regularListQuotientRing C.regularList)) d).mapIso
          (relativeDifferentialOpenSquareIso (i ≫ p) C.quotientSource
            (Spec.map (C.α ≫ regularListQuotientMap C.regularList)) C.jY hSource)
    let K₀ := closedImmersionRightAdjointRegularListResolutionComplex C.regularList J₀
    let eCodim : K₀.homology c ≅ K₀.homology (C.regularList.length : ℤ) :=
      eqToIso (congrArg (fun k : ℤ => K₀.homology k) hc)
    canonicalCommonModelChartHomologyIso i p n d J C =
      closedImmersionRestrictedModelHomologyIso i J C.quotientSource c ≪≫
      (HomologicalComplex.homologyFunctor (Spec (regularListQuotientRing C.regularList)).Modules
        (.up ℤ) c).mapIso (closedImmersionModelOpenIso i J C.quotientSource C.jP
          (Spec.map (regularListQuotientMap C.regularList)) C.quotientSource_isPullback) ≪≫
      eCodim ≪≫
      regularListCanonicalModelTopHomologyIso C.regularList C.weaklyRegular eΓ C.α J₀ Δ ≪≫
      eX.symm := by
  rfl


/-- Retaining the identical actual chart at another source point preserves its original map. -/
theorem canonicalCommonModelChartHomologyIso_repoint
    (y : X) (q : PrimeSpectrum C.B) (hq : C.jX q = y) :
    canonicalCommonModelChartHomologyIso i p n d J C =
      canonicalCommonModelChartHomologyIso i p n d J (C.repoint y q hq) := by
  rfl

end AlgebraicGeometry.Scheme.Modules
