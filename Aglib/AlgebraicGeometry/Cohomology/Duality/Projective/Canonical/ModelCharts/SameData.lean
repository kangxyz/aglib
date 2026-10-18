/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AtIdeal.Data
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AtIdeal.Restriction
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.TopRestriction
public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.GeneratorMatrix

/-!
# Original chart arrows with the same ambient data and kernel ideal

The actual rank equations provide the common normal degree. The original
generator comparison then identifies the fixed-model factors, and the
closed immersion identifies their actual source opens. Genuine quotient
transport gives the resulting square for the original whole chart arrows.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem factorSquare {V : Type*} [Category V]
    {M M' N N' H T : V} (a : M ⟶ M') (b : N ⟶ N')
    (P : M ≅ H) (P' : M' ≅ H) (U : N ≅ T) (U' : N' ≅ T)
    (f g : H ⟶ T) (hP : a ≫ P'.hom = P.hom) (hU : b ≫ U'.hom = U.hom)
    (hf : f = g) :
    a ≫ (P'.hom ≫ g ≫ U'.inv) = (P.hom ≫ f ≫ U.inv) ≫ b := by
  have hUi : U.inv ≫ b = U'.inv := by
    apply (cancel_mono U'.hom).mp
    rw [Category.assoc, hU, Iso.inv_hom_id, Iso.inv_hom_id]
  simpa only [Category.assoc, hUi, hf] using
    congrArg (fun t => t ≫ g ≫ U'.inv) hP

private theorem restrictionSquarePaste {W V X : Scheme.{u}}
    (a b : W ⟶ X) [IsOpenImmersion a] [IsOpenImmersion b]
    (g : W ⟶ V) [IsOpenImmersion g] (j : V ⟶ X) [IsOpenImmersion j]
    (h : a = b) (h' : b = g ≫ j) (M N : X.Modules)
    (f : M.restrict a ⟶ N.restrict a) (f' : M.restrict b ⟶ N.restrict b)
    (k : M.restrict j ⟶ N.restrict j)
    (hf : (restrictFunctorCongr h).hom.app M ≫ f' =
      f ≫ (restrictFunctorCongr h).hom.app N)
    (hk : (restrictFunctorCongr h').hom.app M ≫ (restrictFunctorComp g j).hom.app M ≫
      (restrictFunctor g).map k =
      f' ≫ (restrictFunctorCongr h').hom.app N ≫ (restrictFunctorComp g j).hom.app N) :
    (restrictFunctorCongr (h.trans h')).hom.app M ≫
      (restrictFunctorComp g j).hom.app M ≫ (restrictFunctor g).map k =
    f ≫ (restrictFunctorCongr (h.trans h')).hom.app N ≫
      (restrictFunctorComp g j).hom.app N := by
  subst b
  have hff : f' = f := by
    simpa only [canonicalRestrictionCongr_refl, Category.id_comp, Category.comp_id] using hf
  subst f'
  exact hk

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance sameDataStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}

private theorem chartSourceRelativeSquare
    (C : SmoothClosedImmersionLocalChart i p n d x) (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I) :
    canonicalChartSourceAtIdeal C I hI ≫ (i ≫ p) =
      Spec.map (C.α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        C.A ⟶ CommRingCat.of (C.A ⧸ I))) ≫ C.jY := by
  rw [Spec.map_comp, Category.assoc, C.ambientSquare, ← Category.assoc,
    ← canonicalChartSourceAtIdeal_closedSquare C I hI, Category.assoc]

private theorem chartSourceTopFormula
    (C : SmoothClosedImmersionLocalChart i p n d x) (I : Ideal C.A)
    (hI : Ideal.ofList C.regularList = I)
    (h : canonicalChartSourceAtIdeal C I hI ≫ (i ≫ p) =
      Spec.map (C.α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        C.A ⟶ CommRingCat.of (C.A ⧸ I))) ≫ C.jY) :
    canonicalChartSourceTopIsoAtIdeal C I hI =
      relativeTopDifferentialRestrictionIso (i ≫ p) (canonicalChartSourceAtIdeal C I hI)
        (Spec.map (C.α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
          C.A ⟶ CommRingCat.of (C.A ⧸ I)))) C.jY h d := by
  subst I
  rfl

/-- Equality of the actual ambient chart data and generated ideal identifies the original
whole chart arrows through their genuine spectral quotient transport. -/
theorem canonicalCommonModelChartHomologyIso_sameData
    (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i] (n d : ℕ)
    (J : InjectiveResolution (relativeCanonicalModule p n))
    (C D : SmoothClosedImmersionLocalChart i p n d x)
    (hR : C.R = D.R) (hA : C.A = D.A) (hα : HEq C.α D.α)
    (hY : HEq C.jY D.jY) (hP : HEq C.jP D.jP)
    (hI : HEq (Ideal.ofList C.regularList) (Ideal.ofList D.regularList)) :
    ∃ e : Spec C.quotientChart.B ≅ Spec D.quotientChart.B,
    ∃ he : e.hom ≫ D.quotientChart.jX = C.quotientChart.jX,
      let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
        (closedImmersionCanonicalValue i p n)
      let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
      (restrictFunctorCongr he.symm).hom.app M ≫
        (restrictFunctorComp e.hom D.quotientChart.jX).hom.app M ≫
        (restrictFunctor e.hom).map (canonicalCommonModelChartHomologyIso i p n d J D).hom =
      (canonicalCommonModelChartHomologyIso i p n d J C).hom ≫
        (restrictFunctorCongr he.symm).hom.app N ≫
        (restrictFunctorComp e.hom D.quotientChart.jX).hom.app N := by
  classical
  rcases C with ⟨R, A, B, α, σ, hσ, jY, jP, jX, oY, oP, oX, hAmb, hClosed,
    hCart, point, hp, s, hs, hker, hsmA, hsmB⟩
  rcases D with ⟨R', A', B', α', σ', hσ', jY', jP', jX', oY', oP', oX', hAmb',
    hClosed', hCart', point', hp', t, ht, hker', hsmA', hsmB'⟩
  cases hR
  cases hA
  have hα' : α = α' := eq_of_heq hα
  subst α'
  have hY' : jY = jY' := eq_of_heq hY
  subst jY'
  have hP' : jP = jP' := eq_of_heq hP
  subst jP'
  let C : SmoothClosedImmersionLocalChart i p n d x :=
    ⟨R, A, B, α, σ, hσ, jY, jP, jX, oY, oP, oX, hAmb, hClosed, hCart,
      point, hp, s, hs, hker, hsmA, hsmB⟩
  let D : SmoothClosedImmersionLocalChart i p n d x :=
    ⟨R, A, B', α, σ', hσ', jY, jP, jX', oY', oP', oX', hAmb', hClosed', hCart',
      point', hp', t, ht, hker', hsmA', hsmB'⟩
  let := oY
  let := oP
  let I : Ideal A := Ideal.ofList s
  let c := s.length
  have hsI : Ideal.ofList C.regularList = I := rfl
  have htI : Ideal.ofList D.regularList = I := (eq_of_heq hI).symm
  have hsc : C.regularList.length = c := rfl
  have htc : D.regularList.length = c := by
    have hC : n = C.regularList.length + d := C.dimension_eq
    have hD : n = D.regularList.length + d := D.dimension_eq
    omega
  obtain ⟨matrix, hmatrix⟩ := exists_canonicalGeneratorMatrix C.regularList D.regularList
    (hsc.trans htc.symm) (le_of_eq (htI.trans hsI.symm))
  let a := canonicalChartSourceAtIdeal C I hsI
  let b := canonicalChartSourceAtIdeal D I htI
  have hab : a = b := canonicalQuotientSources_eq i I jP a b
    (canonicalChartSourceAtIdeal_closedSquare C I hsI)
    (canonicalChartSourceAtIdeal_closedSquare D I htI)
  let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
    (closedImmersionCanonicalValue i p n)
  let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
  let := canonicalChartCoefficientQuasicoherent C c hsc
  have hE : canonicalChartCoefficientAtDegree D c htc =
      canonicalChartCoefficientAtDegree C c hsc := by rfl
  have hmodel :
      regularListCanonicalModelMapAt C.α I c (canonicalAmbientChartResolution J C.jP)
        (canonicalChartCoefficientGammaFrame C c hsc)
        (canonicalChartDeterminantAtIdeal C I hsI c hsc) C.regularList C.weaklyRegular hsI hsc =
      regularListCanonicalModelMapAt D.α I c (canonicalAmbientChartResolution J D.jP)
        (canonicalChartCoefficientGammaFrame D c htc)
        (canonicalChartDeterminantAtIdeal D I htI c htc) D.regularList D.weaklyRegular htI htc := by
    simpa only [canonicalChartDeterminantAtIdeal, hE] using
      affineRegularListCanonicalModelMapAt_overlap C.α I c d C.quotientChart.ambientFormallySmooth
        (canonicalChartSourceFormallySmoothAtIdeal C I hsI)
        (canonicalChartAmbientBasisAtDegree C c hsc) (canonicalChartAmbientBasisAtDegree D c htc)
        (canonicalChartSourceBasisAtIdeal C I hsI) (canonicalChartSourceBasisAtIdeal D I htI)
        (canonicalAmbientChartResolution J C.jP)
        (canonicalChartCoefficientGammaFrame C c hsc) (canonicalChartCoefficientGammaFrame D c htc)
        (canonicalChartCoefficientAtDegree C c hsc) C.regularList D.regularList C.weaklyRegular
        D.weaklyRegular hsI htI hsc htc matrix hmatrix
  have hpre : (restrictFunctorCongr hab).hom.app M ≫
      (canonicalChartModelPrefactorAtIdeal D J I htI c htc).hom =
      (canonicalChartModelPrefactorAtIdeal C J I hsI c hsc).hom := by
    let q : A ⟶ CommRingCat.of (A ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
    let := IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
    exact closedImmersionChartModelHomologyIsoInDegree_congr i J a b jP (Spec.map q)
      (canonicalChartCartesianAtIdeal C I hsI) (canonicalChartCartesianAtIdeal D I htI)
      hab ((n : ℤ) - d) (c : ℤ) (canonicalChartCodimensionEq C c hsc)
  have htop : (restrictFunctorCongr hab).hom.app N ≫
      (canonicalChartSourceTopIsoAtIdeal D I htI).hom =
      (canonicalChartSourceTopIsoAtIdeal C I hsI).hom := by
    rw [chartSourceTopFormula C I hsI (chartSourceRelativeSquare C I hsI),
      chartSourceTopFormula D I htI (chartSourceRelativeSquare D I htI)]
    exact canonicalTopDifferentialRestriction_congr (i ≫ p) a b
      (Spec.map (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        A ⟶ CommRingCat.of (A ⧸ I)))) jY
      (chartSourceRelativeSquare C I hsI) (chartSourceRelativeSquare D I htI) hab d
  have hfactor : (restrictFunctorCongr hab).hom.app M ≫
      canonicalChartModelFactorAtIdeal D J I htI c htc =
      canonicalChartModelFactorAtIdeal C J I hsI c hsc ≫
        (restrictFunctorCongr hab).hom.app N := by
    rw [canonicalChartModelFactorAtIdeal_formula, canonicalChartModelFactorAtIdeal_formula]
    exact factorSquare ((restrictFunctorCongr hab).hom.app M)
      ((restrictFunctorCongr hab).hom.app N)
      (canonicalChartModelPrefactorAtIdeal C J I hsI c hsc)
      (canonicalChartModelPrefactorAtIdeal D J I htI c htc)
      (canonicalChartSourceTopIsoAtIdeal C I hsI) (canonicalChartSourceTopIsoAtIdeal D I htI)
      _ _ hpre htop hmodel
  have hchart : (restrictFunctorCongr hab).hom.app M ≫
      (canonicalCommonModelChartHomologyIsoAtIdeal i p n d J D I htI).hom =
      (canonicalCommonModelChartHomologyIsoAtIdeal i p n d J C I hsI).hom ≫
        (restrictFunctorCongr hab).hom.app N := by
    simpa only [canonicalChartModelFactorAtIdeal_eq] using hfactor
  let g := Spec.map (Ideal.quotEquivOfEq htI).toCommRingCatIso.hom
  let e : Spec C.quotientChart.B ≅ Spec D.quotientChart.B := asIso g
  have he : e.hom ≫ D.quotientChart.jX = C.quotientChart.jX :=
    (hab.trans (canonicalChartSourceAtIdeal_spec D I htI)).symm
  refine ⟨e, he, ?_⟩
  exact restrictionSquarePaste a b g D.quotientChart.jX hab
    (canonicalChartSourceAtIdeal_spec D I htI) M N
    (canonicalCommonModelChartHomologyIsoAtIdeal i p n d J C I hsI).hom
    (canonicalCommonModelChartHomologyIsoAtIdeal i p n d J D I htI).hom
    (canonicalCommonModelChartHomologyIso i p n d J D).hom hchart
    (canonicalCommonModelChartHomologyIsoAtIdeal_restrict i p n d J D I htI)

end AlgebraicGeometry.Scheme.Modules
