/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.PrincipalDifferentials
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.PrincipalModel

/-!
# The original source prefactor on a principal chart

Native fixed-resolution composition and source congruence give the exact
ordinary source-prefactor equation. This calculation precedes the
coefficient and determinant calculations of the whole chart arrow.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance principalPrefactorStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i]
  (n d : ℕ) (J : InjectiveResolution (relativeCanonicalModule p n))
  {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)
  (r : C.A) (hr : C.σ r ∉ C.point.asIdeal)

/-- The actual original source-prefactor equation, with the original two resolutions. -/
def CanonicalPrincipalChartPrefactorSquare : Prop :=
  let D := C.principalChart r hr
  let c := C.regularList.length
  let hc := canonicalPrincipalChart_length C r hr c rfl
  let φ : C.A ⟶ CommRingCat.of (Localization.Away r) :=
    CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
  let g := Spec.map (regularListPrincipalLiteralQuotientMap C.regularList r)
  let k := Spec.map φ
  let t := regularListPrincipalList C.regularList r
  let q := regularListQuotientMap C.regularList
  let q' := regularListQuotientMap (A := CommRingCat.of (Localization.Away r)) t
  letI := IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
  letI := IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
  let J₀ := canonicalAmbientChartResolution J C.jP
  let H := regularListPrincipalLiteralIsPullback C.regularList r
  let h : D.quotientSource = g ≫ C.quotientSource := by
    simpa only [canonicalChartQuotientSource_eq] using canonicalPrincipalChart_source C r hr
  let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
    (closedImmersionCanonicalValue i p n)
  let Rₘ := (restrictFunctorCongr h).app M ≪≫
    (restrictFunctorComp g C.quotientSource).app M
  let S := canonicalChartModelPrefactorAtIdeal C J (Ideal.ofList C.regularList) rfl c rfl
  let Sd := canonicalChartModelPrefactorAtIdeal D J (Ideal.ofList D.regularList) rfl c hc
  let T := closedImmersionChartModelStepHomologyMap (Spec.map q) J₀ g k (Spec.map q') H (c : ℤ)
  let z := homologyMap (((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex
    (.up ℤ)).map (canonicalAmbientResolutionCompLift C.jP k J).hom') (c : ℤ)
  Rₘ.inv ≫ Sd.hom ≫ z = (restrictFunctor g).map S.hom ≫ T

private theorem sourceSquareTransport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M H : C} {M' H' K : D}
    (s t : M ≅ H) (s' t' : M' ≅ H') (r : F.obj M ⟶ M')
    (T : F.obj H ⟶ K) (z : H' ⟶ K) (hs : s = t) (ht : s' = t')
    (h : r ≫ t'.hom ≫ z = F.map t.hom ≫ T) :
    r ≫ s'.hom ≫ z = F.map s.hom ≫ T := by
  cases hs
  cases ht
  exact h

private theorem nativePrefactorSourceSquare
    {W' W U V' V P : Scheme.{u}} (f : U ⟶ P) [IsClosedImmersion f]
    {L : P.Modules} (J : InjectiveResolution L)
    (a : W ⟶ U) (j : V ⟶ P) (b : W ⟶ V)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsClosedImmersion b]
    (H : IsPullback a b f j)
    (g : W' ⟶ W) (k : V' ⟶ V) (b' : W' ⟶ V')
    [IsOpenImmersion g] [IsOpenImmersion k] [IsClosedImmersion b']
    (H' : IsPullback g b' b k)
    (a' : W' ⟶ U) [IsOpenImmersion a']
    (Hd : IsPullback a' b' f (k ≫ j)) (h : a' = g ≫ a)
    (n m : ℤ) (hnm : n = m) :
    let M := (DerivedCategory.Plus.homologyFunctor U.Modules n).obj
      ((closedImmersionRightAdjoint f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L))
    let R := (restrictFunctorCongr h).app M ≪≫ (restrictFunctorComp g a).app M
    let S := closedImmersionChartModelHomologyIsoInDegree f J a j b H n m hnm
    let Sd := closedImmersionChartModelHomologyIsoInDegree f J a' (k ≫ j) b' Hd n m hnm
    let T := closedImmersionChartModelStepHomologyMap b (canonicalAmbientChartResolution J j)
      g k b' H' m
    let z := homologyMap (((closedImmersionRightAdjoint b').mapHomologicalComplex
      (.up ℤ)).map (canonicalAmbientResolutionCompLift j k J).hom') m
    R.inv ≫ Sd.hom ≫ z = (restrictFunctor g).map S.hom ≫ T := by
  intro M R S Sd T z
  let Sc := closedImmersionChartModelHomologyIsoInDegree f J (g ≫ a) (k ≫ j) b'
    (H'.paste_horiz H) n m hnm
  have hComp := closedImmersionChartModelHomologyIsoInDegree_comp f J a j b H
    g k b' H' n m hnm
  have hCongr := closedImmersionChartModelHomologyIsoInDegree_congr f J a' (g ≫ a)
    (k ≫ j) b' Hd (H'.paste_horiz H) h n m hnm
  have hs₀ := congrArg (fun w => (restrictFunctorCongr h).hom.app M ≫ w) hComp
  have hs₁ := congrArg (fun w => w ≫ z) hCongr
  have hs : R.hom ≫ (restrictFunctor g).map S.hom ≫ T = Sd.hom ≫ z := by
    have h₀ : R.hom ≫ (restrictFunctor g).map S.hom ≫ T =
        (restrictFunctorCongr h).hom.app M ≫ Sc.hom ≫ z := by
      simpa only [R, S, Sc, Iso.trans_hom, Iso.app_hom, Category.assoc] using hs₀
    have h₁ : (restrictFunctorCongr h).hom.app M ≫ Sc.hom ≫ z = Sd.hom ≫ z := by
      simpa only [Sc, Sd, Iso.app_hom, Category.assoc] using hs₁
    exact h₀.trans h₁
  rw [← hs, R.inv_hom_id_assoc]

/-- The native original fixed-resolution comparisons give the actual principal source square. -/
theorem canonicalPrincipalChart_prefactor :
    CanonicalPrincipalChartPrefactorSquare i p n d J C r hr := by
  unfold CanonicalPrincipalChartPrefactorSquare
  intro D c hc φ g k t q q' J₀ H h M Rₘ S Sd T z
  let : IsClosedImmersion (Spec.map q) :=
    IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
  let : IsClosedImmersion (Spec.map q') :=
    IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
  let a := C.quotientSource
  let a' := D.quotientSource
  let S₀ : M.restrict a ≅ regularListModelTopHomologyAt (Ideal.ofList C.regularList) J₀ c :=
    closedImmersionChartModelHomologyIsoInDegree i J a C.jP (Spec.map q)
      C.quotientChart.cartesian ((n : ℤ) - d) (c : ℤ) (canonicalChartCodimensionEq C c rfl)
  let Sd₀ :=
    closedImmersionChartModelHomologyIsoInDegree i J a' (k ≫ C.jP) (Spec.map q')
      D.quotientChart.cartesian ((n : ℤ) - d) (c : ℤ) (canonicalChartCodimensionEq C c rfl)
  have hSData : S = S₀ := rfl
  have hSdData : Sd = Sd₀ := rfl
  have hNative : Rₘ.inv ≫ Sd₀.hom ≫ z = (restrictFunctor g).map S₀.hom ≫ T :=
    nativePrefactorSourceSquare i J a C.jP (Spec.map q) C.quotientChart.cartesian
      g k (Spec.map q') H a' D.quotientChart.cartesian h ((n : ℤ) - d) (c : ℤ)
      (canonicalChartCodimensionEq C c rfl)
  exact sourceSquareTransport (restrictFunctor g) S S₀ Sd Sd₀ Rₘ.inv T z
    hSData hSdData hNative

end AlgebraicGeometry.Scheme.Modules
