/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Ambient
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Base
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.SameData
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Descent.Sections

/-!
# The original normalized arrows as ordinary Hom-sheaf sections

The actual principal and isomorphic chart equations give literal
restrictions of the original Hom sections. Composition of refinements
then uses only the ordinary presheaf restriction maps.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.InternalHom

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem refinementRange_le {V W X : Scheme.{u}}
    (a : V ⟶ X) (b : W ⟶ X) [IsOpenImmersion a] [IsOpenImmersion b]
    (g : W ⟶ V) (h : b = g ≫ a) : b.opensRange ≤ a.opensRange := by
  rintro z ⟨w, rfl⟩
  exact ⟨g w, (congrArg (fun f : W ⟶ X => f w) h).symm⟩

private theorem arrowsEqualOfSameFactors {V : Type*} [Category V] {A B P Q : V}
    (s s' : A ≅ P) (f f' : P ⟶ Q) (t t' : B ≅ Q) (a b : A ⟶ B)
    (hs : s = s') (hf : f = f') (ht : t = t')
    (ha : s.hom ≫ f ≫ t.inv = a) (hb : s'.hom ≫ f' ≫ t'.inv = b) : a = b := by
  cases hs
  cases hf
  cases ht
  exact ha.symm.trans hb

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance chartSectionsStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ}
  [IsClosedImmersion i] {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)
  (J : InjectiveResolution (relativeCanonicalModule p n))

local notation "M" => Functor.obj
  (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d))
  (closedImmersionCanonicalValue i p n)
local notation "N" => moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
local notation "H" => InternalHom.sheaf X M N

/-- The original chart arrow, viewed in the original ordinary Hom sheaf. -/
def canonicalChartHomSection : Γ(H, C.quotientSource.opensRange) :=
  restrictionHomEquiv C.quotientSource M N
    (canonicalCommonModelChartHomologyIso i p n d J C).hom

/-- The actual principal source range is contained in the original source range. -/
theorem canonicalPrincipalChart_range_le (r : C.A) (hr : C.σ r ∉ C.point.asIdeal) :
    (C.principalChart r hr).quotientSource.opensRange ≤ C.quotientSource.opensRange := by
  have h : (C.principalChart r hr).quotientSource =
      Spec.map (regularListPrincipalLiteralQuotientMap C.regularList r) ≫ C.quotientSource := by
    simpa only [canonicalChartQuotientSource_eq] using canonicalPrincipalChart_source C r hr
  exact refinementRange_le C.quotientSource (C.principalChart r hr).quotientSource
    (Spec.map (regularListPrincipalLiteralQuotientMap C.regularList r)) h

/-- The principal whole-arrow equation is literal restriction of the original Hom section. -/
theorem canonicalChartHomSection_principal (r : C.A) (hr : C.σ r ∉ C.point.asIdeal) :
    (H).val.presheaf.map (homOfLE (canonicalPrincipalChart_range_le C r hr)).op
        (canonicalChartHomSection C J) = canonicalChartHomSection (C.principalChart r hr) J := by
  have h : (C.principalChart r hr).quotientSource =
      Spec.map (regularListPrincipalLiteralQuotientMap C.regularList r) ≫ C.quotientSource := by
    simpa only [canonicalChartQuotientSource_eq] using canonicalPrincipalChart_source C r hr
  apply canonicalRestrictionHomEquiv_refinement C.quotientSource
    (C.principalChart r hr).quotientSource
    (Spec.map (regularListPrincipalLiteralQuotientMap C.regularList r)) h M N
    (canonicalCommonModelChartHomologyIso i p n d J C).hom
    (canonicalCommonModelChartHomologyIso i p n d J (C.principalChart r hr)).hom
  simpa only [CanonicalPrincipalChartArrowSquare, canonicalChartQuotientSource_eq,
    Iso.trans_hom, Iso.app_hom, Category.assoc] using
      canonicalCommonModelChartHomologyIso_principal i p n d J C r hr

/-- Changing only the actual base presentation preserves the original Hom section. -/
theorem canonicalChartHomSection_baseIso {R' : CommRingCat.{u}} (eR : C.R ≅ R') :
    canonicalChartHomSection C J = canonicalChartHomSection (C.baseIsoChart eR) J := by
  exact congrArg (restrictionHomEquiv C.quotientSource M N)
    (canonicalCommonModelChartHomologyIso_baseIso i p n d J C eR)

/-- The original base-principal chart retains the section of its actual ambient refinement. -/
theorem canonicalChartHomSection_basePrincipal (r : C.R)
    (hr : C.σ (C.α r) ∉ C.point.asIdeal) :
    canonicalChartHomSection (C.principalChart (C.α r) hr) J =
      canonicalChartHomSection (C.basePrincipalChart r hr) J := by
  exact congrArg
    (restrictionHomEquiv (C.principalChart (C.α r) hr).quotientSource M N)
    (canonicalCommonModelChartHomologyIso_basePrincipal i p n d J C r hr)

/-- The actual ambient-isomorphism source lies over the original source range. -/
theorem canonicalAmbientIsoChart_range_le {A' : CommRingCat.{u}} (eA : C.A ≅ A') :
    (C.ambientIsoChart eA).quotientSource.opensRange ≤ C.quotientSource.opensRange := by
  exact refinementRange_le C.quotientSource (C.ambientIsoChart eA).quotientSource
    (Spec.map (canonicalAmbientIsoChartQuotientMap C eA))
    (canonicalAmbientIsoChart_source C eA)

/-- The ambient whole-arrow equation is literal restriction of the original Hom section. -/
theorem canonicalChartHomSection_ambientIso {A' : CommRingCat.{u}} (eA : C.A ≅ A') :
    (H).val.presheaf.map (homOfLE (canonicalAmbientIsoChart_range_le C eA)).op
        (canonicalChartHomSection C J) = canonicalChartHomSection (C.ambientIsoChart eA) J := by
  apply canonicalRestrictionHomEquiv_refinement C.quotientSource
    (C.ambientIsoChart eA).quotientSource
    (Spec.map (canonicalAmbientIsoChartQuotientMap C eA)) (canonicalAmbientIsoChart_source C eA)
    M N (canonicalCommonModelChartHomologyIso i p n d J C).hom
    (canonicalCommonModelChartHomologyIso i p n d J (C.ambientIsoChart eA)).hom
  simpa only [CanonicalAmbientChartArrowSquare, Iso.trans_hom, Iso.app_hom,
    Category.assoc] using canonicalCommonModelChartHomologyIso_ambientIso i p n d J C eA

private theorem canonicalChartPrefactor_repoint (y : X) (q : PrimeSpectrum C.B)
    (hq : C.jX q = y) :
    canonicalChartModelPrefactorAtIdeal C J (Ideal.ofList C.regularList) rfl
        C.regularList.length rfl =
      canonicalChartModelPrefactorAtIdeal (C.repoint y q hq) J
        (Ideal.ofList (C.repoint y q hq).regularList) rfl C.regularList.length rfl := rfl

omit [IsClosedImmersion i] in
private theorem canonicalChartCore_repoint (y : X) (q : PrimeSpectrum C.B)
    (hq : C.jX q = y) :
    canonicalChartModelCoreAtDegree C J C.regularList.length rfl =
      canonicalChartModelCoreAtDegree (C.repoint y q hq) J C.regularList.length rfl := rfl

omit [IsClosedImmersion i] in
private theorem canonicalChartSourceTop_repoint (y : X) (q : PrimeSpectrum C.B)
    (hq : C.jX q = y) :
    canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList C.regularList) rfl =
      canonicalChartSourceTopIsoAtIdeal (C.repoint y q hq)
        (Ideal.ofList (C.repoint y q hq).regularList) rfl := rfl

/-- Compare the original arrows through typed factor equalities before taking Hom sections. -/
private theorem canonicalChartHomologyMap_repoint (y : X) (q : PrimeSpectrum C.B)
    (hq : C.jX q = y) :
    (canonicalCommonModelChartHomologyIso i p n d J C).hom =
      (canonicalCommonModelChartHomologyIso i p n d J (C.repoint y q hq)).hom := by
  exact arrowsEqualOfSameFactors
    (canonicalChartModelPrefactorAtIdeal C J (Ideal.ofList C.regularList) rfl
      C.regularList.length rfl)
    (canonicalChartModelPrefactorAtIdeal (C.repoint y q hq) J
      (Ideal.ofList (C.repoint y q hq).regularList) rfl C.regularList.length rfl)
    (canonicalChartModelCoreAtDegree C J C.regularList.length rfl)
    (canonicalChartModelCoreAtDegree (C.repoint y q hq) J C.regularList.length rfl)
    (canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList C.regularList) rfl)
    (canonicalChartSourceTopIsoAtIdeal (C.repoint y q hq)
      (Ideal.ofList (C.repoint y q hq).regularList) rfl)
    (canonicalCommonModelChartHomologyIso i p n d J C).hom
    (canonicalCommonModelChartHomologyIso i p n d J (C.repoint y q hq)).hom
    (canonicalChartPrefactor_repoint C J y q hq)
    (canonicalChartCore_repoint C J y q hq)
    (canonicalChartSourceTop_repoint C y q hq)
    (canonicalChartModelCoreAtDegree_factor C J C.regularList.length rfl)
    (canonicalChartModelCoreAtDegree_factor (C.repoint y q hq) J C.regularList.length rfl)

/-- Retaining the same chart at a new actual source point retains its original Hom section. -/
theorem canonicalChartHomSection_repoint (y : X) (q : PrimeSpectrum C.B)
    (hq : C.jX q = y) :
    canonicalChartHomSection C J = canonicalChartHomSection (C.repoint y q hq) J := by
  exact congrArg (restrictionHomEquiv C.quotientSource M N)
    (canonicalChartHomologyMap_repoint C J y q hq)

/-- The genuine same-data comparison gives a common restriction of original Hom sections. -/
theorem canonicalChartHomSection_sameData (D : SmoothClosedImmersionLocalChart i p n d x)
    (hR : C.R = D.R) (hA : C.A = D.A) (hα : HEq C.α D.α)
    (hY : HEq C.jY D.jY) (hP : HEq C.jP D.jP)
    (hI : HEq (Ideal.ofList C.regularList) (Ideal.ofList D.regularList)) :
    ∃ hCD : C.quotientSource.opensRange ≤ D.quotientSource.opensRange,
      (H).val.presheaf.map (homOfLE hCD).op (canonicalChartHomSection D J) =
        canonicalChartHomSection C J := by
  obtain ⟨e, he, hSquare⟩ := canonicalCommonModelChartHomologyIso_sameData
    i p n d J C D hR hA hα hY hP hI
  have h : C.quotientSource = e.hom ≫ D.quotientSource := by
    simpa only [canonicalChartQuotientSource_eq] using he.symm
  have hCD : C.quotientSource.opensRange ≤ D.quotientSource.opensRange := by
    exact refinementRange_le D.quotientSource C.quotientSource e.hom h
  refine ⟨hCD, ?_⟩
  apply canonicalRestrictionHomEquiv_refinement D.quotientSource C.quotientSource e.hom h
    M N (canonicalCommonModelChartHomologyIso i p n d J D).hom
    (canonicalCommonModelChartHomologyIso i p n d J C).hom
  simpa only [canonicalChartQuotientSource_eq, Iso.trans_hom, Iso.app_hom,
    Category.assoc] using hSquare

end AlgebraicGeometry.Scheme.Modules
