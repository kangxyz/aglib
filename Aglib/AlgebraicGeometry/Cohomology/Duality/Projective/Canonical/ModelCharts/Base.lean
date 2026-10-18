/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.BaseDifferentials
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AtIdeal.Data
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseChart

/-!
# The original whole chart arrow under actual changes of affine base

The source model and its original resolution remain the same. The
original base comparison identifies the normal-first determinant, while
the native top-differential comparison identifies the coefficient and
target factors. Both sections frames may be the original independent
chart frames.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Cohomology

universe u w
namespace AlgebraicGeometry.Scheme.Modules

section Primitive
variable {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A) (α : R ⟶ A)
  (hα : ρ ≫ β = α) (s : List A) [IsOpenImmersion (Spec.map ρ)]
  (HA : 𝟙 (Spec A) ≫ Spec.map α = Spec.map β ≫ Spec.map ρ)
  (HQ : 𝟙 (Spec (regularListQuotientRing s)) ≫
      Spec.map (α ≫ regularListQuotientMap s) =
    Spec.map (β ≫ regularListQuotientMap s) ≫ Spec.map ρ)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  (hA : α.hom.FormallySmooth) (hQ : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
  (hA' : β.hom.FormallySmooth) (hQ' : (β ≫ regularListQuotientMap s).hom.FormallySmooth)
  {d : ℕ}
  (bA : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential α))
  (bA' : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential β))
  (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
    (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
  (bQ' : Module.Basis (Fin d) (regularListQuotientRing s)
    (CommRingCat.KaehlerDifferential (β ≫ regularListQuotientMap s)))
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (E : L ≅ moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α))
    (s.length + d))
  (J : InjectiveResolution L) (e f : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  [HasExt.{w} (ModuleCat.{u} A)]

local notation "τA" => Functor.mapIso (moduleExteriorPowerFunctor (Spec A) (s.length + d))
  (restrictFunctorId.symm.app (relativeDifferentialSheaf (Spec.map α)) ≪≫
    relativeDifferentialOpenSquareIso (Spec.map α) (𝟙 (Spec A)) (Spec.map β) (Spec.map ρ) HA)
local notation "τQ" =>
  Functor.mapIso (moduleExteriorPowerFunctor (Spec (regularListQuotientRing s)) d)
    (restrictFunctorId.symm.app
      (relativeDifferentialSheaf (Spec.map (α ≫ regularListQuotientMap s))) ≪≫
      relativeDifferentialOpenSquareIso (Spec.map (α ≫ regularListQuotientMap s))
        (𝟙 (Spec (regularListQuotientRing s)))
        (Spec.map (β ≫ regularListQuotientMap s)) (Spec.map ρ) HQ)

include hα in
private theorem modelBaseOfEq :
    regularListCanonicalModelMapAt α (Ideal.ofList s) s.length J e
        (regularListCanonicalCoefficientDeterminantAt α s hs s.length d
          hA hQ bA bQ rfl E) s hs rfl rfl ≫ (τQ).hom =
      regularListCanonicalModelMapAt β (Ideal.ofList s) s.length J f
        (regularListCanonicalCoefficientDeterminantAt β s hs s.length d
          hA' hQ' bA' bQ' rfl (E ≪≫ τA)) s hs rfl rfl := by
  subst α
  exact regularListCanonicalModelMapAt_base ρ β s HA HQ hs hA hQ hA' hQ'
    bA bA' bQ bQ' E J e f

end Primitive

private theorem topBase
    {X Z Y Y₀ Y₁ : Scheme.{u}}
    (p : X ⟶ Y) (a : Z ⟶ X) (q₀ : Z ⟶ Y₀) (j₀ : Y₀ ⟶ Y)
    (q₁ : Z ⟶ Y₁) (j₁ : Y₁ ⟶ Y₀)
    [IsOpenImmersion a] [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    (h₀ : a ≫ p = q₀ ≫ j₀) (h₁ : 𝟙 Z ≫ q₀ = q₁ ≫ j₁)
    (h : a ≫ p = q₁ ≫ (j₁ ≫ j₀)) (m : ℕ) :
    (relativeTopDifferentialRestrictionIso p a q₀ j₀ h₀ m).hom ≫
      ((moduleExteriorPowerFunctor Z m).mapIso
        (restrictFunctorId.symm.app (relativeDifferentialSheaf q₀) ≪≫
          relativeDifferentialOpenSquareIso q₀ (𝟙 Z) q₁ j₁ h₁)).hom =
    (relativeTopDifferentialRestrictionIso p a q₁ (j₁ ≫ j₀) h m).hom := by
  simpa only [canonicalTopDifferentialRestrictionInDegree, Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id] using
    canonicalTopDifferentialRestrictionInDegree_base p a q₀ j₀ q₁ j₁ h₀ h₁ h m m rfl

private theorem factorBase {V : Type*} [Category V]
    {M H N T T' : V} (P : M ≅ H) (U : N ≅ T) (U' : N ≅ T')
    (f : H ⟶ T) (f' : H ⟶ T') (τ : T ≅ T')
    (hf : f ≫ τ.hom = f') (hU : U.hom ≫ τ.hom = U'.hom) :
    P.hom ≫ f ≫ U.inv = P.hom ≫ f' ≫ U'.inv := by
  have hInv : U.inv ≫ U'.hom = τ.hom := by
    rw [← hU, Iso.inv_hom_id_assoc]
  apply (cancel_mono U'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hInv, hf]

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance baseChartStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ}
  {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)

private theorem coefficientFormula (c : ℕ) (hc : C.regularList.length = c)
    (hnd : n = c + d) :
    canonicalChartCoefficientAtDegree C c hc =
      canonicalTopDifferentialRestrictionInDegree p C.jP (Spec.map C.α) C.jY
        C.ambientSquare.symm n (c + d) hnd := rfl

private theorem sourceSquare :
    C.quotientSource ≫ (i ≫ p) =
      Spec.map (C.α ≫ regularListQuotientMap C.regularList) ≫ C.jY := by
  rw [Spec.map_comp, Category.assoc, C.ambientSquare, ← Category.assoc,
    ← C.quotientSource_square, Category.assoc]

private theorem sourceTopFormula
    (h : C.quotientSource ≫ (i ≫ p) =
      Spec.map (C.α ≫ regularListQuotientMap C.regularList) ≫ C.jY) :
    canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList C.regularList) rfl =
      relativeTopDifferentialRestrictionIso (i ≫ p) C.quotientSource
        (Spec.map (C.α ≫ regularListQuotientMap C.regularList)) C.jY h d := rfl

private def changeBaseChart {S : CommRingCat.{u}} (ρ : C.R ⟶ S) (β : S ⟶ C.A)
    [IsOpenImmersion (Spec.map ρ)] (hα : ρ ≫ β = C.α)
    (hA : RingHom.IsStandardSmoothOfRelativeDimension n β.hom)
    (hB : RingHom.IsStandardSmoothOfRelativeDimension d (β ≫ C.σ).hom) :
    SmoothClosedImmersionLocalChart i p n d x where
  R := S
  A := C.A
  B := C.B
  α := β
  σ := C.σ
  surjective := C.surjective
  jY := Spec.map ρ ≫ C.jY
  jP := C.jP
  jX := C.jX
  openY := inferInstance
  openP := C.openP
  openX := C.openX
  ambientSquare := by
    rw [← Category.assoc, ← Spec.map_comp, hα, C.ambientSquare]
  closedSquare := C.closedSquare
  cartesian := C.cartesian
  point := C.point
  point_eq := C.point_eq
  regularList := C.regularList
  weaklyRegular := C.weaklyRegular
  kernel := C.kernel
  ambientSmooth := hA
  sourceSmooth := hB

private theorem baseSquare {R S A : CommRingCat.{u}}
    (ρ : R ⟶ S) (β : S ⟶ A) (α : R ⟶ A) (hα : ρ ≫ β = α) :
    𝟙 (Spec A) ≫ Spec.map α = Spec.map β ≫ Spec.map ρ := by
  rw [Category.id_comp, ← Spec.map_comp, hα]

section ChangeBase
variable {S : CommRingCat.{u}} (ρ : C.R ⟶ S) (β : S ⟶ C.A)
  [IsOpenImmersion (Spec.map ρ)] (hα : ρ ≫ β = C.α)
  (hA : RingHom.IsStandardSmoothOfRelativeDimension n β.hom)
  (hB : RingHom.IsStandardSmoothOfRelativeDimension d (β ≫ C.σ).hom)

private theorem changeBaseRegularList :
    (changeBaseChart C ρ β hα hA hB).regularList = C.regularList := rfl

private def ambientBaseTop :
    moduleExteriorPower (Spec C.A) (relativeDifferentialSheaf (Spec.map C.α))
        (C.regularList.length + d) ≅
      moduleExteriorPower (Spec C.A) (relativeDifferentialSheaf (Spec.map β))
        (C.regularList.length + d) :=
  (moduleExteriorPowerFunctor (Spec C.A) (C.regularList.length + d)).mapIso
    (restrictFunctorId.symm.app (relativeDifferentialSheaf (Spec.map C.α)) ≪≫
      relativeDifferentialOpenSquareIso (Spec.map C.α) (𝟙 (Spec C.A))
        (Spec.map β) (Spec.map ρ) (baseSquare ρ β C.α hα))

include hα in
omit [IsOpenImmersion (Spec.map ρ)] in
private theorem quotientBaseSquare :
    𝟙 (Spec (regularListQuotientRing C.regularList)) ≫
        Spec.map (C.α ≫ regularListQuotientMap C.regularList) =
      Spec.map (β ≫ regularListQuotientMap C.regularList) ≫ Spec.map ρ :=
  baseSquare ρ (β ≫ regularListQuotientMap C.regularList)
    (C.α ≫ regularListQuotientMap C.regularList)
    ((Category.assoc ρ β _).symm.trans
      (congrArg (fun t => t ≫ regularListQuotientMap C.regularList) hα))

private def sourceBaseTop :
    regularListTangentTopAt C.α (Ideal.ofList C.regularList) d ≅
      regularListTangentTopAt β (Ideal.ofList C.regularList) d :=
  (moduleExteriorPowerFunctor (Spec (regularListQuotientRing C.regularList)) d).mapIso
    (restrictFunctorId.symm.app
      (relativeDifferentialSheaf (Spec.map (C.α ≫ regularListQuotientMap C.regularList))) ≪≫
      relativeDifferentialOpenSquareIso
        (Spec.map (C.α ≫ regularListQuotientMap C.regularList))
        (𝟙 (Spec (regularListQuotientRing C.regularList)))
        (Spec.map (β ≫ regularListQuotientMap C.regularList)) (Spec.map ρ)
        (quotientBaseSquare C ρ β hα))

private theorem changeBaseCoefficient :
    canonicalChartCoefficientAtDegree C C.regularList.length rfl ≪≫
        ambientBaseTop C ρ β hα =
      canonicalChartCoefficientAtDegree (changeBaseChart C ρ β hα hA hB)
        C.regularList.length rfl := by
  apply Iso.ext
  rw [coefficientFormula C C.regularList.length rfl C.dimension_eq,
    coefficientFormula (changeBaseChart C ρ β hα hA hB)
      C.regularList.length rfl C.dimension_eq]
  exact canonicalTopDifferentialRestrictionInDegree_base p C.jP (Spec.map C.α) C.jY
    (Spec.map β) (Spec.map ρ) C.ambientSquare.symm (baseSquare ρ β C.α hα)
    (changeBaseChart C ρ β hα hA hB).ambientSquare.symm n
    (C.regularList.length + d) C.dimension_eq

private theorem changeBaseSourceTop :
    (canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList C.regularList) rfl).hom ≫
        (sourceBaseTop C ρ β hα).hom =
      (canonicalChartSourceTopIsoAtIdeal (changeBaseChart C ρ β hα hA hB)
        (Ideal.ofList C.regularList) rfl).hom := by
  have hD := sourceTopFormula (changeBaseChart C ρ β hα hA hB)
    (sourceSquare (changeBaseChart C ρ β hα hA hB))
  simp only [changeBaseRegularList] at hD
  rw [sourceTopFormula C (sourceSquare C), hD]
  exact topBase (i ≫ p) C.quotientSource
    (Spec.map (C.α ≫ regularListQuotientMap C.regularList)) C.jY
    (Spec.map (β ≫ regularListQuotientMap C.regularList)) (Spec.map ρ)
    (sourceSquare C) (quotientBaseSquare C ρ β hα)
    (sourceSquare (changeBaseChart C ρ β hα hA hB)) d

end ChangeBase

variable [IsClosedImmersion i] (J : InjectiveResolution (relativeCanonicalModule p n))

private def chartModelCore :
    regularListModelTopHomologyAt (Ideal.ofList C.regularList)
        (canonicalAmbientChartResolution J C.jP) C.regularList.length ⟶
      regularListTangentTopAt C.α (Ideal.ofList C.regularList) d := by
  letI := canonicalChartCoefficientQuasicoherent C C.regularList.length rfl
  exact regularListCanonicalModelMapAt C.α (Ideal.ofList C.regularList) C.regularList.length
    (canonicalAmbientChartResolution J C.jP)
    (canonicalChartCoefficientGammaFrame C C.regularList.length rfl)
    (canonicalChartDeterminantAtIdeal C (Ideal.ofList C.regularList) rfl
      C.regularList.length rfl) C.regularList C.weaklyRegular rfl rfl

private theorem wholeChartFormula :
    (canonicalCommonModelChartHomologyIso i p n d J C).hom =
      (canonicalChartModelPrefactorAtIdeal C J (Ideal.ofList C.regularList) rfl
        C.regularList.length rfl).hom ≫ chartModelCore C J ≫
      (canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList C.regularList) rfl).inv :=
  (canonicalChartModelFactorAtIdeal_eq C J (Ideal.ofList C.regularList) rfl
    C.regularList.length rfl).symm.trans
      (canonicalChartModelFactorAtIdeal_formula C J (Ideal.ofList C.regularList) rfl
        C.regularList.length rfl)

section WholeChangeBase
variable {S : CommRingCat.{u}} (ρ : C.R ⟶ S) (β : S ⟶ C.A)
  [IsOpenImmersion (Spec.map ρ)] (hα : ρ ≫ β = C.α)
  (hA : RingHom.IsStandardSmoothOfRelativeDimension n β.hom)
  (hB : RingHom.IsStandardSmoothOfRelativeDimension d (β ≫ C.σ).hom)

omit [IsClosedImmersion i] in
private theorem changeBaseModelCore :
    chartModelCore C J ≫ (sourceBaseTop C ρ β hα).hom =
      chartModelCore (changeBaseChart C ρ β hα hA hB) J := by
  let D := changeBaseChart C ρ β hα hA hB
  let := canonicalChartCoefficientQuasicoherent C C.regularList.length rfl
  have h := modelBaseOfEq ρ β C.α hα C.regularList (baseSquare ρ β C.α hα)
    (quotientBaseSquare C ρ β hα) C.weaklyRegular
    C.quotientChart.ambientFormallySmooth
    (canonicalChartSourceFormallySmoothAtIdeal C (Ideal.ofList C.regularList) rfl)
    D.quotientChart.ambientFormallySmooth
    (canonicalChartSourceFormallySmoothAtIdeal D (Ideal.ofList C.regularList) rfl)
    (canonicalChartAmbientBasisAtDegree C C.regularList.length rfl)
    (canonicalChartAmbientBasisAtDegree D C.regularList.length rfl)
    (canonicalChartSourceBasisAtIdeal C (Ideal.ofList C.regularList) rfl)
    (canonicalChartSourceBasisAtIdeal D (Ideal.ofList C.regularList) rfl)
    (canonicalChartCoefficientAtDegree C C.regularList.length rfl)
    (canonicalAmbientChartResolution J C.jP)
    (canonicalChartCoefficientGammaFrame C C.regularList.length rfl)
    (canonicalChartCoefficientGammaFrame D C.regularList.length rfl)
  have hE := changeBaseCoefficient C ρ β hα hA hB
  dsimp only [ambientBaseTop] at hE
  rw [hE] at h
  exact h

private theorem changeBasePrefactor :
    canonicalChartModelPrefactorAtIdeal C J (Ideal.ofList C.regularList) rfl
        C.regularList.length rfl =
      canonicalChartModelPrefactorAtIdeal (changeBaseChart C ρ β hα hA hB) J
        (Ideal.ofList C.regularList) rfl C.regularList.length rfl := rfl

private theorem wholeChartChangeBase :
    (canonicalCommonModelChartHomologyIso i p n d J C).hom =
      (canonicalCommonModelChartHomologyIso i p n d J (changeBaseChart C ρ β hα hA hB)).hom := by
  rw [wholeChartFormula C J, wholeChartFormula (changeBaseChart C ρ β hα hA hB) J]
  simp only [changeBaseRegularList]
  rw [← changeBasePrefactor C J ρ β hα hA hB]
  exact factorBase _ _ _ _ _ (sourceBaseTop C ρ β hα)
    (changeBaseModelCore C J ρ β hα hA hB) (changeBaseSourceTop C ρ β hα hA hB)

end WholeChangeBase

/-- Reparametrizing the base preserves the original whole normalized chart arrow. -/
theorem canonicalCommonModelChartHomologyIso_baseIso
    (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i] (n d : ℕ)
    (J : InjectiveResolution (relativeCanonicalModule p n))
    (C : SmoothClosedImmersionLocalChart i p n d x)
    {R' : CommRingCat.{u}} (eR : C.R ≅ R') :
    (canonicalCommonModelChartHomologyIso i p n d J C).hom =
      (canonicalCommonModelChartHomologyIso i p n d J (C.baseIsoChart eR)).hom := by
  let D := C.baseIsoChart eR
  have hα : eR.hom ≫ D.α = C.α := eR.hom_inv_id_assoc C.α
  exact wholeChartChangeBase C J eR.hom D.α hα D.ambientSmooth D.sourceSmooth

/-- The actual base principal chart has the same whole arrow as the ambient principal chart. -/
theorem canonicalCommonModelChartHomologyIso_basePrincipal
    (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i] (n d : ℕ)
    (J : InjectiveResolution (relativeCanonicalModule p n))
    (C : SmoothClosedImmersionLocalChart i p n d x)
    (r : C.R) (hr : C.σ (C.α r) ∉ C.point.asIdeal) :
    (canonicalCommonModelChartHomologyIso i p n d J (C.principalChart (C.α r) hr)).hom =
      (canonicalCommonModelChartHomologyIso i p n d J (C.basePrincipalChart r hr)).hom := by
  let D₀ := C.principalChart (C.α r) hr
  let D := C.basePrincipalChart r hr
  let ρ : C.R ⟶ CommRingCat.of (Localization.Away r) :=
    CommRingCat.ofHom (algebraMap C.R (Localization.Away r))
  have hα : ρ ≫ D.α = D₀.α := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change IsLocalization.Away.map (Localization.Away r) (Localization.Away (C.α r))
        C.α.hom r (algebraMap C.R (Localization.Away r) z) =
      algebraMap C.A (Localization.Away (C.α r)) (C.α z)
    simp only [IsLocalization.Away.map, IsLocalization.map_eq]
  exact wholeChartChangeBase D₀ J ρ D.α hα D.ambientSmooth D.sourceSmooth

end AlgebraicGeometry.Scheme.Modules
