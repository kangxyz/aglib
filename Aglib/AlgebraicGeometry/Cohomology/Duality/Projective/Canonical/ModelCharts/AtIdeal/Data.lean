/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AtIdeal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Prefactor

/-!
# The original chart data on the common quotient and degree

The ambient frame, original coefficient isomorphism and source differential
isomorphism have their native types shared before the genuine ideal and degree
transports are applied. The resulting factor uses the actual fixed-model map
on the literal common quotient.
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
local instance chartDataStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ}
  [IsClosedImmersion i] {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)

omit [IsClosedImmersion i] in
/-- The actual rank equation identifies the installed integer homology degree. -/
theorem canonicalChartCodimensionEq (c : ℕ) (hc : C.regularList.length = c) :
    (n : ℤ) - d = (c : ℤ) := by
  have h := C.quotientChart.dimension_eq
  have hl : C.quotientChart.regularList.length = c := hc
  omega

/-- The same normal-first determinant with the actual original coefficient sheaf. -/
def canonicalChartDeterminantAtIdeal (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) (c : ℕ) (hc : C.regularList.length = c) :
    tensorSheaf (Spec (CommRingCat.of (C.A ⧸ I))) (regularListNormalAt I c)
      (regularListTangentTopAt C.α I d) ≅
        (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
          C.A ⟶ CommRingCat.of (C.A ⧸ I)))).obj
            ((relativeCanonicalModule p n).restrict C.jP) :=
  regularListCanonicalDeterminantAt C.α I c d C.quotientChart.ambientFormallySmooth
    (canonicalChartSourceFormallySmoothAtIdeal C I hI)
    (canonicalChartAmbientBasisAtDegree C c hc) (canonicalChartSourceBasisAtIdeal C I hI)
      C.regularList C.weaklyRegular hI hc ≪≫
    (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
      C.A ⟶ CommRingCat.of (C.A ⧸ I)))).mapIso (canonicalChartCoefficientAtDegree C c hc).symm

/-- The actual source top-differential restriction on the same transported quotient. -/
def canonicalChartSourceTopIsoAtIdeal (I : Ideal C.A) (hI : Ideal.ofList C.regularList = I) :
    (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict
        (canonicalChartSourceAtIdeal C I hI) ≅ regularListTangentTopAt C.α I d := by
  subst I
  have hSource : C.quotientSource ≫ (i ≫ p) =
      Spec.map (C.α ≫ regularListQuotientMap C.regularList) ≫ C.jY := by
    rw [Spec.map_comp, Category.assoc, C.ambientSquare, ← Category.assoc,
      ← C.quotientSource_square, Category.assoc]
  exact (moduleExteriorPowerRestrictionIso C.quotientSource
    (relativeDifferentialSheaf (i ≫ p)) d).symm ≪≫
    (moduleExteriorPowerFunctor (Spec (regularListQuotientRing C.regularList)) d).mapIso
      (relativeDifferentialOpenSquareIso (i ≫ p) C.quotientSource
        (Spec.map (C.α ≫ regularListQuotientMap C.regularList)) C.jY hSource)

variable (J : InjectiveResolution (relativeCanonicalModule p n))

/-- The original native model comparison followed only by the genuine homology-degree change. -/
def canonicalChartModelPrefactorAtIdeal (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) (c : ℕ) (hc : C.regularList.length = c) :
    ((DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
      (closedImmersionCanonicalValue i p n)).restrict (canonicalChartSourceAtIdeal C I hI) ≅
        regularListModelTopHomologyAt I (canonicalAmbientChartResolution J C.jP) c := by
  let q : C.A ⟶ CommRingCat.of (C.A ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  letI := IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
  exact closedImmersionChartModelHomologyIsoInDegree i J (canonicalChartSourceAtIdeal C I hI)
    C.jP (Spec.map q) (canonicalChartCartesianAtIdeal C I hI) ((n : ℤ) - d) (c : ℤ)
    (canonicalChartCodimensionEq C c hc)

/-- The same original fixed-model arrow on the literal common ideal and degree. -/
def canonicalChartModelFactorAtIdeal (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) (c : ℕ) (hc : C.regularList.length = c) :
    ((DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
      (closedImmersionCanonicalValue i p n)).restrict (canonicalChartSourceAtIdeal C I hI) ⟶
      (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict
        (canonicalChartSourceAtIdeal C I hI) := by
  letI := canonicalChartCoefficientQuasicoherent C c hc
  exact (canonicalChartModelPrefactorAtIdeal C J I hI c hc).hom ≫
    regularListCanonicalModelMapAt C.α I c (canonicalAmbientChartResolution J C.jP)
      (canonicalChartCoefficientGammaFrame C c hc) (canonicalChartDeterminantAtIdeal C I hI c hc)
      C.regularList C.weaklyRegular hI hc ≫ (canonicalChartSourceTopIsoAtIdeal C I hI).inv

/-- The shared factor retains the literal original prefactor, model arrow and target inverse. -/
theorem canonicalChartModelFactorAtIdeal_formula (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) (c : ℕ) (hc : C.regularList.length = c) :
    letI := canonicalChartCoefficientQuasicoherent C c hc
    canonicalChartModelFactorAtIdeal C J I hI c hc =
      (canonicalChartModelPrefactorAtIdeal C J I hI c hc).hom ≫
        regularListCanonicalModelMapAt C.α I c (canonicalAmbientChartResolution J C.jP)
          (canonicalChartCoefficientGammaFrame C c hc)
          (canonicalChartDeterminantAtIdeal C I hI c hc) C.regularList C.weaklyRegular hI hc ≫
        (canonicalChartSourceTopIsoAtIdeal C I hI).inv := by
  rfl

/-- This shared-data factor is the original chart map on the genuine common degree. -/
theorem canonicalChartModelFactorAtIdeal_eq (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) (c : ℕ) (hc : C.regularList.length = c) :
    canonicalChartModelFactorAtIdeal C J I hI c hc =
      (canonicalCommonModelChartHomologyIsoAtIdeal i p n d J C I hI).hom := by
  subst I c
  simpa only [canonicalChartModelFactorAtIdeal, canonicalChartModelPrefactorAtIdeal,
    canonicalChartDeterminantAtIdeal, canonicalChartSourceTopIsoAtIdeal,
    canonicalChartSourceBasisAtIdeal, canonicalChartSourceAtIdeal, canonicalChartQuotientSource_eq,
    canonicalCommonModelChartHomologyIsoAtIdeal, regularListCanonicalModelMapAt,
    regularListCanonicalDeterminantAt, closedImmersionChartModelHomologyIsoInDegree,
    closedImmersionChartModelHomologyIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc] using
      (congrArg Iso.hom (canonicalCommonModelChartHomologyIso_eq_shared i p n d J C)).symm

end AlgebraicGeometry.Scheme.Modules
