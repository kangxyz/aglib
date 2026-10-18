/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.SourceIdeal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.GeneratorOverlap
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model.OpenComposition.Homology

/-!
# The original chart arrow on a genuine common ideal and degree

Only actual equalities of the regular-list ideal and normal degree change
the presentation. The global source prefactor is the same original native
model comparison, and the ordinary local factor is the original model map
on the common quotient and degree.
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
local instance chartAtIdealStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

/-- The original source differential basis transported only through its actual ideal equality. -/
def canonicalChartSourceBasisAtIdeal
    {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
    (C : SmoothClosedImmersionLocalChart i p n d x) (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    Module.Basis (Fin d) (CommRingCat.of (C.A ⧸ I))
      (CommRingCat.KaehlerDifferential (C.α ≫
        (CommRingCat.ofHom (Ideal.Quotient.mk I) : C.A ⟶ CommRingCat.of (C.A ⧸ I)))) :=
  canonicalChartQuotientSourceBasis C I hI

/-- Native source formal smoothness is retained by the same genuine ideal transport. -/
theorem canonicalChartSourceFormallySmoothAtIdeal
    {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
    (C : SmoothClosedImmersionLocalChart i p n d x) (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    (C.α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
      C.A ⟶ CommRingCat.of (C.A ⧸ I))).hom.FormallySmooth :=
  canonicalChartQuotientSourceFormallySmooth C I hI

/-- The same original Cartesian chart square is retained by genuine ideal transport. -/
theorem canonicalChartCartesianAtIdeal
    {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
    (C : SmoothClosedImmersionLocalChart i p n d x) (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    IsPullback (canonicalChartSourceAtIdeal C I hI)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) i C.jP := by
  subst I
  exact C.quotientChart.cartesian

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i]
  (n d : ℕ) (J : InjectiveResolution (relativeCanonicalModule p n))
  {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)

/-- The same original chart arrow, transported only by its genuine quotient ideal equality. -/
def canonicalCommonModelChartHomologyIsoAtIdeal (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    ((DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
      (closedImmersionCanonicalValue i p n)).restrict (canonicalChartSourceAtIdeal C I hI) ≅
      (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict
        (canonicalChartSourceAtIdeal C I hI) := by
  subst I
  exact canonicalCommonModelChartHomologyIso i p n d J C

/-- The actual original chart factor, written using the ordinary common-ideal model arrow.
Genuine ideal and degree equality transport this same factor; no new choice is made. -/
def canonicalCommonModelChartFactorAtIdeal (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) (c : ℕ) (_hc : C.regularList.length = c) :
    ((DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
      (closedImmersionCanonicalValue i p n)).restrict (canonicalChartSourceAtIdeal C I hI) ⟶
      (moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d).restrict
        (canonicalChartSourceAtIdeal C I hI) := by
  subst I
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
  exact (closedImmersionChartModelHomologyIso i J Q.jX Q.jP (Spec.map Q.σ)
    Q.cartesian c).hom ≫ eCodim.hom ≫
    regularListCanonicalModelMapAt Q.α (Ideal.ofList Q.regularList) Q.regularList.length
      J₀ eΓ Δ Q.regularList Q.weaklyRegular rfl rfl ≫ eX.inv

private theorem modelMapAt_reflexive
    {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] (K : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
    {T : (Spec (regularListQuotientRing s)).Modules}
    (Δ : tensorSheaf _ (regularListNormalAt (Ideal.ofList s) s.length) T ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L) :
    regularListCanonicalModelMapAt α (Ideal.ofList s) s.length K e Δ s hs rfl rfl =
      (regularListCanonicalModelTopHomologyIso s hs e α K Δ).hom := rfl

/-- The original chart homomorphism equals its genuine common-ideal model factor. -/
theorem canonicalCommonModelChartHomologyIsoAtIdeal_hom (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) (c : ℕ) (hc : C.regularList.length = c) :
    (canonicalCommonModelChartHomologyIsoAtIdeal i p n d J C I hI).hom =
      canonicalCommonModelChartFactorAtIdeal i p n d J C I hI c hc := by
  subst I
  simpa only [canonicalCommonModelChartHomologyIsoAtIdeal,
    canonicalCommonModelChartFactorAtIdeal, canonicalChartSourceAtIdeal,
    modelMapAt_reflexive, closedImmersionChartModelHomologyIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc] using
      congrArg Iso.hom (canonicalCommonModelChartHomologyIso_eq i p n d J C)

end AlgebraicGeometry.Scheme.Modules
