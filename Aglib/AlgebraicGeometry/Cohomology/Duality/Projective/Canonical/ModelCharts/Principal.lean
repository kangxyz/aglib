/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module


public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.PrincipalDifferentials
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.ModelCore
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.PrincipalModel
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.PrincipalPrefactor
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.CoefficientTransport
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Pasting
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenComparison.Principal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.GeneratorOverlap.NormalDegree

/-!
# The original whole chart arrow on an actual principal refinement

The direct native source prefactor, the original principal model square,
the original direct-to-iterated resolution lift and native differential
pasting compare the original chart arrows. All factors and compatibility
statements are produced from the actual chart and principal localization.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u w z
namespace AlgebraicGeometry.Scheme.Modules

private theorem transportCoefficientDeterminant {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) {L N Ω : C} {V : D}
    (Δ : V ≅ P.obj Ω) (E : L ≅ Ω) (E' : N ≅ Ω) (η : L ≅ N)
    (hE : E = η ≪≫ E') :
    (Δ ≪≫ P.mapIso E.symm) ≪≫ P.mapIso η = Δ ≪≫ P.mapIso E'.symm := by
  rw [hE]
  apply Iso.ext
  change (Δ.hom ≫ P.map (E'.inv ≫ η.inv)) ≫ P.map η.hom = Δ.hom ≫ P.map E'.inv
  rw [P.map_comp, Category.assoc, Category.assoc,
    ← P.map_comp η.inv η.hom, η.inv_hom_id, P.map_id, Category.comp_id]

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance principalChartArrowStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

local instance {A : CommRingCat.{u}} (s : List A) :
    IsClosedImmersion (Spec.map (regularListQuotientMap s)) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

section PrimitiveModelSquare
variable {R A A' : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (t : List A')
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  (ht : RingTheory.Sequence.IsWeaklyRegular A' t)
  (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  (h : φ ≫ regularListQuotientMap t = regularListQuotientMap s ≫ ψ)
  (hA : α.hom.FormallySmooth)
  (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
  (hA' : (α ≫ φ).hom.FormallySmooth)
  (hB' : ((α ≫ φ) ≫ regularListQuotientMap t).hom.FormallySmooth)
  {d : ℕ} (bA : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential α))
  (bA' : Module.Basis (Fin (s.length + d)) A' (CommRingCat.KaehlerDifferential (α ≫ φ)))
  (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
    (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
  (bQ' : Module.Basis (Fin d) (regularListQuotientRing t)
    (CommRingCat.KaehlerDifferential ((α ≫ φ) ≫ regularListQuotientMap t)))
  (hc : t.length = s.length)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (J : InjectiveResolution L) (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  (E : L ≅ moduleExteriorPower (Spec A)
    (relativeDifferentialSheaf (Spec.map α)) (s.length + d))
  [HasExt.{w} (ModuleCat.{u} A)] [HasExt.{z} (ModuleCat.{u} A')]

local notation "J'" => affineOpenRestrictedInjectiveResolution φ J
local notation "e'" => regularListOpenCoefficientFrame φ e (affineRestrictGlobalSectionsIso φ L)
local notation "E'" => Functor.mapIso (restrictFunctor (Spec.map φ)) E ≪≫
  canonicalAmbientTopOpenIso α φ (s.length + d)
local notation "D₀" => regularListCanonicalCoefficientDeterminantAt α s hs s.length d
  hA hB bA bQ rfl E
local notation "D₁" => regularListCanonicalCoefficientDeterminantAt (α ≫ φ) t ht s.length d
  hA' hB' bA' bQ' hc E'

/-- The same original open-model equation, in the genuine fixed-ideal presentation. -/
theorem canonicalModelOpenSquareAt
    (T : ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
        (s.length : ℤ)).restrict (Spec.map ψ) ⟶
      (closedImmersionRightAdjointRegularListResolutionComplex t J').homology (s.length : ℤ))
    (hT : CanonicalRegularListModelOpenSquare α s t hs ht φ ψ h hA hB hA' hB'
      bA bA' bQ bQ' hc J e E T) :
    (restrictFunctor (Spec.map ψ)).map
        (regularListCanonicalModelMapAt α (Ideal.ofList s) s.length J e D₀ s hs rfl rfl) ≫
      canonicalExteriorOpenMap (Spec.map ψ)
        (relativeDifferentialSheaf (Spec.map (α ≫ regularListQuotientMap s)))
        (relativeDifferentialSheaf (Spec.map ((α ≫ φ) ≫ regularListQuotientMap t))) d
        (canonicalAmbientConormalTangentIso α φ (regularListQuotientMap s)
          (regularListQuotientMap t) ψ h).hom =
    T ≫ regularListCanonicalModelMapAt (α ≫ φ) (Ideal.ofList t) s.length J' e' D₁
      t ht rfl hc := by
  have hi := regularListCanonicalModelMapAt_eq_commonNormal (α ≫ φ) t ht J' e'
    s.length hc D₁
  have hSource : regularListCanonicalModelMapAt α (Ideal.ofList s) s.length J e D₀
      s hs rfl rfl = (regularListCanonicalModelTopHomologyIso s hs e α J D₀).hom := rfl
  rw [hSource, hi]
  exact hT

end PrimitiveModelSquare

/-- Native coefficient transport retains any equal original determinant presentation. -/
theorem canonicalModelCoefficientSquare {R A : CommRingCat.{u}} (α : R ⟶ A)
    (I : Ideal A) (c : ℕ) {L N : (Spec A).Modules} [L.IsQuasicoherent] [N.IsQuasicoherent]
    (J : InjectiveResolution L) (K : InjectiveResolution N)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
    (f : moduleSpecΓFunctor.obj N ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]
    (E : L ≅ N) (φ : InjectiveResolution.Hom J K E.hom)
    {Q : (Spec (CommRingCat.of (A ⧸ I))).Modules}
    (Δ : tensorSheaf _ (regularListNormalAt I c) Q ≅
      (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        A ⟶ CommRingCat.of (A ⧸ I)))).obj L)
    (Δ' : tensorSheaf _ (regularListNormalAt I c) Q ≅
      (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        A ⟶ CommRingCat.of (A ⧸ I)))).obj N)
    (hΔ : Δ ≪≫ (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
      A ⟶ CommRingCat.of (A ⧸ I)))).mapIso E = Δ')
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    homologyMap (((closedImmersionRightAdjoint
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
          A ⟶ CommRingCat.of (A ⧸ I)))).mapHomologicalComplex (.up ℤ)).map φ.hom') (c : ℤ) ≫
      regularListCanonicalModelMapAt α I c K f Δ' s hs hI hc =
    regularListCanonicalModelMapAt α I c J e Δ s hs hI hc := by
  subst Δ'
  exact regularListCanonicalModelMapAt_coefficient α I c J K e f E φ Δ s hs hI hc

private theorem moveIsoLeft {C : Type*} [Category C] {X Y Z : C}
    (e : X ≅ Y) (f : Y ⟶ Z) (g : X ⟶ Z) (h : e.hom ≫ f = g) :
    e.inv ≫ g = f := by
  rw [← h, e.inv_hom_id_assoc]

private theorem wholeSquareOfInverse {C : Type*} [Category C] {M M' N N' : C}
    (s : M' ≅ M) (t : N' ≅ N) (f : M ⟶ N) (g : M' ⟶ N')
    (h : f ≫ t.inv = s.inv ≫ g) : s.hom ≫ f = g ≫ t.hom := by
  have hh := congrArg (fun w => s.hom ≫ w ≫ t.hom) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using hh

private theorem wholeChartPaste {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M H Q N : C} {M' H' H'' Q' N' : D}
    (s : M ≅ H) (s' : M' ≅ H') (u : N ≅ Q) (u' : N' ≅ Q')
    (f : H ⟶ Q) (f' : H' ⟶ Q') (f'' : H'' ⟶ Q')
    (rM : M' ≅ F.obj M) (rN : N' ≅ F.obj N)
    (T : F.obj H ⟶ H'') (z : H' ⟶ H'') (v : F.obj Q ⟶ Q')
    (hs : rM.inv ≫ s'.hom ≫ z = F.map s.hom ≫ T)
    (hf : F.map f ≫ v = T ≫ f'') (hz : z ≫ f'' = f')
    (hu : F.map u.hom ≫ v = rN.inv ≫ u'.hom)
    (c : M ⟶ N) (c' : M' ⟶ N')
    (hc : s.hom ≫ f ≫ u.inv = c) (hc' : s'.hom ≫ f' ≫ u'.inv = c') :
    rM.hom ≫ F.map c = c' ≫ rN.hom := by
  have hw := canonicalChartArrow_paste F s s' u u' f f' f''
    rM.inv rN.inv T z v hs hf hz hu
  rw [hc, hc'] at hw
  exact wholeSquareOfInverse rM rN (F.map c) c' hw

private theorem modelSquareTransport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {H Q : C} {K Q' : D}
    (f f₀ : H ⟶ Q) (v : F.obj Q ⟶ Q') (T T₀ : F.obj H ⟶ K)
    (fi fi₀ : K ⟶ Q') (hf : f = f₀) (hT : T₀ = T) (hfi : fi = fi₀)
    (h : F.map f₀ ≫ v = T₀ ≫ fi₀) :
    F.map f ≫ v = T ≫ fi := by
  cases hf
  cases hT
  cases hfi
  exact h

private theorem sourceSquareTransport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M H : C} {M' H' K : D}
    (s t : M ≅ H) (s' t' : M' ≅ H') (r : F.obj M ⟶ M')
    (T : F.obj H ⟶ K) (z : H' ⟶ K) (hs : s = t) (ht : s' = t')
    (h : r ≫ t'.hom ≫ z = F.map t.hom ≫ T) :
    r ≫ s'.hom ≫ z = F.map s.hom ≫ T := by
  cases hs
  cases ht
  exact h

private theorem sourceCoreNative
    {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
    (C : SmoothClosedImmersionLocalChart i p n d x)
    (J : InjectiveResolution (relativeCanonicalModule p n))
    (c : ℕ) (hc : C.regularList.length = c) :
    letI := canonicalChartCoefficientQuasicoherent C c hc
    canonicalChartModelCoreAtDegree C J c hc =
      regularListCanonicalModelMapAt C.α (Ideal.ofList C.regularList) c
        (canonicalAmbientChartResolution J C.jP) (canonicalChartCoefficientGammaFrame C c hc)
        (regularListCanonicalCoefficientDeterminantAt C.α C.regularList C.weaklyRegular c d
          C.quotientChart.ambientFormallySmooth C.quotientChart.sourceFormallySmooth
          (canonicalChartAmbientBasisAtDegree C c hc)
          (canonicalChartSourceBasisAtIdeal C (Ideal.ofList C.regularList) rfl)
          hc (canonicalChartCoefficientAtDegree C c hc))
        C.regularList C.weaklyRegular rfl hc :=
  canonicalChartModelCoreAtDegree_representation C J c hc

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i]
  (n d : ℕ) (J : InjectiveResolution (relativeCanonicalModule p n))
  {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)
  (r : C.A) (hr : C.σ r ∉ C.point.asIdeal)

omit [IsClosedImmersion i] in
private theorem principalTargetTopGetter :
    (canonicalChartSourceTopIsoAtIdeal (C.principalChart r hr)
      (Ideal.ofList (regularListPrincipalList C.regularList r)) rfl).hom =
    (canonicalChartSourceTopIsoAtIdeal (C.principalChart r hr)
      (Ideal.ofList (C.principalChart r hr).regularList) rfl).hom := rfl

/-- The literal original whole-arrow square for an actual principal chart refinement. -/
def CanonicalPrincipalChartArrowSquare : Prop :=
  let D := C.principalChart r hr
  let g := Spec.map (regularListPrincipalLiteralQuotientMap C.regularList r)
  let h := canonicalPrincipalChart_source C r hr
  let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
    (closedImmersionCanonicalValue i p n)
  let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
  (restrictFunctorCongr h).hom.app M ≫
      (restrictFunctorComp g C.quotientChart.jX).hom.app M ≫
      (restrictFunctor g).map (canonicalCommonModelChartHomologyIso i p n d J C).hom =
    (canonicalCommonModelChartHomologyIso i p n d J D).hom ≫
      (restrictFunctorCongr h).hom.app N ≫
      (restrictFunctorComp g C.quotientChart.jX).hom.app N

/-- The same original whole-arrow square with each restriction isomorphism kept together. -/
private def CanonicalPrincipalChartPastedSquare : Prop :=
  let D := C.principalChart r hr
  let g := Spec.map (regularListPrincipalLiteralQuotientMap C.regularList r)
  let h := canonicalPrincipalChart_source C r hr
  let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
    (closedImmersionCanonicalValue i p n)
  let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
  let Rₘ := (restrictFunctorCongr h).app M ≪≫
    (restrictFunctorComp g C.quotientChart.jX).app M
  let Rₙ := (restrictFunctorCongr h).app N ≪≫
    (restrictFunctorComp g C.quotientChart.jX).app N
  Rₘ.hom ≫ (restrictFunctor g).map (canonicalCommonModelChartHomologyIso i p n d J C).hom =
    (canonicalCommonModelChartHomologyIso i p n d J D).hom ≫ Rₙ.hom

omit [IsClosedImmersion i] in
/-- The native producer predicate, with all target objects from the original chart. -/
private theorem principalNativeModelSquare :
    let D := C.principalChart r hr
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let hc := canonicalPrincipalChart_length C r hr c rfl
    let φ : C.A ⟶ D.A := CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      regularListPrincipalLiteralQuotientMap s r
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap t
    let hφ : φ ≫ q' = q ≫ ψ := regularListPrincipalLiteralQuotientMap_square s r
    let J₀ := canonicalAmbientChartResolution J C.jP
    let E := canonicalChartCoefficientAtDegree C c rfl
    letI := canonicalChartCoefficientQuasicoherent C c rfl
    CanonicalRegularListModelOpenSquare (A' := D.A) C.α s t C.weaklyRegular D.weaklyRegular
      φ ψ hφ C.quotientChart.ambientFormallySmooth C.quotientChart.sourceFormallySmooth
      D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth
      (canonicalChartAmbientBasisAtDegree C c rfl) (canonicalChartAmbientBasisAtDegree D c hc)
      (canonicalChartSourceBasisAtIdeal C (Ideal.ofList s) rfl)
      (canonicalChartSourceBasisAtIdeal D (Ideal.ofList t) rfl) hc
      J₀ (canonicalChartCoefficientGammaFrame C c rfl) E
      (regularListPrincipalLiteralSheafHomologyMap s r J₀ (c : ℤ)) := by
  intro D s t c hc φ ψ q q' hφ J₀ E
  let := canonicalChartCoefficientQuasicoherent C c rfl
  exact regularListCanonicalModelTopHomologyIso_principal C.α s r C.weaklyRegular
    D.weaklyRegular C.quotientChart.ambientFormallySmooth
    C.quotientChart.sourceFormallySmooth D.quotientChart.ambientFormallySmooth
    D.quotientChart.sourceFormallySmooth
    (canonicalChartAmbientBasisAtDegree C c rfl) (canonicalChartAmbientBasisAtDegree D c hc)
    (canonicalChartSourceBasisAtIdeal C (Ideal.ofList s) rfl)
    (canonicalChartSourceBasisAtIdeal D (Ideal.ofList t) rfl)
    J₀ (canonicalChartCoefficientGammaFrame C c rfl) E

omit [IsClosedImmersion i] in
/-- The existing raw model map on the iterated restricted resolution. -/
private def principalIteratedCore :
    let D := C.principalChart r hr
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let φ : C.A ⟶ D.A :=
      CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    regularListModelTopHomologyAt (Ideal.ofList t)
        (canonicalAmbientChartResolution (canonicalAmbientChartResolution J C.jP) (Spec.map φ)) c ⟶
      regularListTangentTopAt D.α (Ideal.ofList t) d := by
  intro D s t c φ
  let hc := canonicalPrincipalChart_length C r hr c rfl
  let k := Spec.map φ
  let j := C.jP
  let L := relativeCanonicalModule p n
  let J₀ := canonicalAmbientChartResolution J j
  let Ji := affineOpenRestrictedInjectiveResolution φ J₀
  let E := canonicalChartCoefficientAtDegree C c rfl
  let Ei := (restrictFunctor k).mapIso E ≪≫ canonicalAmbientTopOpenIso C.α φ (c + d)
  let := canonicalChartCoefficientQuasicoherent C c rfl
  let : ((L.restrict j).restrict k).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor k (L.restrict j)
  let e := canonicalChartCoefficientGammaFrame C c rfl
  let ei := regularListOpenCoefficientFrame φ
    (E' := moduleSpecΓFunctor.obj ((restrictFunctor k).obj (L.restrict j))) e
    (affineRestrictGlobalSectionsIso φ (L.restrict j))
  let bA' := canonicalChartAmbientBasisAtDegree D c hc
  let bQ' := canonicalChartSourceBasisAtIdeal D (Ideal.ofList t) rfl
  let Δi := regularListCanonicalCoefficientDeterminantAt (C.α ≫ φ) t D.weaklyRegular c d
    D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth bA' bQ' hc Ei
  exact regularListCanonicalModelMapAt (C.α ≫ φ) (Ideal.ofList t) c Ji ei Δi t
    D.weaklyRegular rfl hc

omit [IsClosedImmersion i] in
/-- The target alias has exactly the same native producer representation. -/
private theorem principalIteratedCore_representation :
    let D := C.principalChart r hr
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let φ : C.A ⟶ D.A :=
      CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    let hc := canonicalPrincipalChart_length C r hr c rfl
    let k := Spec.map φ
    let j := C.jP
    let L := relativeCanonicalModule p n
    let J₀ := canonicalAmbientChartResolution J j
    let Ji := affineOpenRestrictedInjectiveResolution φ J₀
    let E := canonicalChartCoefficientAtDegree C c rfl
    let Ei := (restrictFunctor k).mapIso E ≪≫ canonicalAmbientTopOpenIso C.α φ (c + d)
    letI := canonicalChartCoefficientQuasicoherent C c rfl
    letI : ((L.restrict j).restrict k).IsQuasicoherent :=
      isQuasicoherent_restrictFunctor k (L.restrict j)
    let e := canonicalChartCoefficientGammaFrame C c rfl
    let ei := regularListOpenCoefficientFrame φ
      (E' := moduleSpecΓFunctor.obj ((restrictFunctor k).obj (L.restrict j))) e
      (affineRestrictGlobalSectionsIso φ (L.restrict j))
    let bA' := canonicalChartAmbientBasisAtDegree D c hc
    let bQ' := canonicalChartSourceBasisAtIdeal D (Ideal.ofList t) rfl
    let Δi := regularListCanonicalCoefficientDeterminantAt (C.α ≫ φ) t D.weaklyRegular c d
      D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth bA' bQ' hc Ei
    principalIteratedCore i p n d J C r hr =
      regularListCanonicalModelMapAt (C.α ≫ φ) (Ideal.ofList t) c Ji ei Δi t
        D.weaklyRegular rfl hc := by
  rfl

omit [IsClosedImmersion i] in
/-- The original native literal step, with the original target model object. -/
private theorem principalNativeStep :
    let D := C.principalChart r hr
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let φ : C.A ⟶ D.A := CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      regularListPrincipalLiteralQuotientMap s r
    let g := Spec.map ψ
    let k := Spec.map φ
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap t
    letI := IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
    letI := IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
    let H : IsPullback g (Spec.map q') (Spec.map q) k :=
      regularListPrincipalLiteralIsPullback s r
    let J₀ := canonicalAmbientChartResolution J C.jP
    let Hi := regularListModelTopHomologyAt (Ideal.ofList t)
      (canonicalAmbientChartResolution J₀ k) c
    let T₀ : (regularListModelTopHomologyAt (Ideal.ofList s) J₀ c).restrict g ⟶ Hi :=
      regularListPrincipalLiteralSheafHomologyMap s r J₀ (c : ℤ)
    T₀ = closedImmersionChartModelStepHomologyMap (Spec.map q) J₀ g k (Spec.map q') H (c : ℤ) := by
  intro D s t c φ ψ g k q q' H J₀ Hi T₀
  let : IsClosedImmersion (Spec.map q) :=
    IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
  let : IsClosedImmersion (Spec.map q') :=
    IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
  exact regularListPrincipalLiteralSheafHomologyMap_eq_step s r J₀ (c : ℤ)

omit [IsClosedImmersion i] in
/-- The native model supplier on the original target model and tangent objects. -/
private theorem principalNativeAtSquare :
    let D := C.principalChart r hr
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let hc := canonicalPrincipalChart_length C r hr c rfl
    let φ : C.A ⟶ D.A := CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      regularListPrincipalLiteralQuotientMap s r
    let g := Spec.map ψ
    let k := Spec.map φ
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap t
    let hφ : φ ≫ q' = q ≫ ψ := regularListPrincipalLiteralQuotientMap_square s r
    let L := (relativeCanonicalModule p n).restrict C.jP
    let J₀ := canonicalAmbientChartResolution J C.jP
    let Hi := regularListModelTopHomologyAt (Ideal.ofList t)
      (canonicalAmbientChartResolution J₀ k) c
    let Qd := regularListTangentTopAt D.α (Ideal.ofList t) d
    let E := canonicalChartCoefficientAtDegree C c rfl
    letI := canonicalChartCoefficientQuasicoherent C c rfl
    letI : ((restrictFunctor k).obj L).IsQuasicoherent := isQuasicoherent_restrictFunctor k L
    let e := canonicalChartCoefficientGammaFrame C c rfl
    let bA := canonicalChartAmbientBasisAtDegree C c rfl
    let bA' := canonicalChartAmbientBasisAtDegree D c hc
    let bQ := canonicalChartSourceBasisAtIdeal C (Ideal.ofList s) rfl
    let bQ' := canonicalChartSourceBasisAtIdeal D (Ideal.ofList t) rfl
    let Δ := regularListCanonicalCoefficientDeterminantAt C.α s C.weaklyRegular c d
      C.quotientChart.ambientFormallySmooth C.quotientChart.sourceFormallySmooth bA bQ rfl E
    let Ei := (restrictFunctor k).mapIso E ≪≫ canonicalAmbientTopOpenIso C.α φ (c + d)
    let ei := regularListOpenCoefficientFrame φ
      (E' := moduleSpecΓFunctor.obj ((restrictFunctor k).obj L)) e
      (affineRestrictGlobalSectionsIso φ L)
    let Δi := regularListCanonicalCoefficientDeterminantAt (C.α ≫ φ) t D.weaklyRegular c d
      D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth bA' bQ' hc Ei
    let f₀ := regularListCanonicalModelMapAt C.α (Ideal.ofList s) c J₀ e Δ s C.weaklyRegular rfl rfl
    let fi₀ : Hi ⟶ Qd := regularListCanonicalModelMapAt (C.α ≫ φ) (Ideal.ofList t) c
      (affineOpenRestrictedInjectiveResolution φ J₀) ei Δi t D.weaklyRegular rfl hc
    let T₀ : (regularListModelTopHomologyAt (Ideal.ofList s) J₀ c).restrict g ⟶ Hi :=
      regularListPrincipalLiteralSheafHomologyMap s r J₀ (c : ℤ)
    let v := canonicalExteriorOpenMap g
      (relativeDifferentialSheaf (Spec.map (C.α ≫ q)))
      (relativeDifferentialSheaf (Spec.map ((C.α ≫ φ) ≫ q'))) d
      (canonicalAmbientConormalTangentIso C.α φ q q' ψ hφ).hom
    (restrictFunctor g).map f₀ ≫ v = T₀ ≫ fi₀ := by
  intro D s t c hc φ ψ g k q q' hφ L J₀ Hi Qd E e bA bA' bQ bQ' Δ Ei ei Δi f₀ fi₀ T₀ v
  let := canonicalChartCoefficientQuasicoherent C c rfl
  let : ((restrictFunctor k).obj L).IsQuasicoherent := isQuasicoherent_restrictFunctor k L
  exact canonicalModelOpenSquareAt C.α s t C.weaklyRegular D.weaklyRegular φ ψ hφ
    C.quotientChart.ambientFormallySmooth C.quotientChart.sourceFormallySmooth
    D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth
    bA bA' bQ bQ' hc J₀ e E
    (regularListPrincipalLiteralSheafHomologyMap s r J₀ (c : ℤ))
    (principalNativeModelSquare i p n d J C r hr)

omit [IsClosedImmersion i] in
/-- The original source core has the native principal-localization square. -/
private theorem principalCoreOpenSquare :
    let D := C.principalChart r hr
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let _hc := canonicalPrincipalChart_length C r hr c rfl
    let φ : C.A ⟶ D.A :=
      CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      regularListPrincipalLiteralQuotientMap s r
    let g := Spec.map ψ
    let k := Spec.map φ
    let j := C.jP
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap (A := D.A) t
    letI := IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
    letI := IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
    let H : IsPullback g (Spec.map q') (Spec.map q) k :=
      regularListPrincipalLiteralIsPullback s r
    let J₀ := canonicalAmbientChartResolution J j
    let _Ji := canonicalAmbientChartResolution J₀ k
    let f := canonicalChartModelCoreAtDegree C J c rfl
    let T := closedImmersionChartModelStepHomologyMap (Spec.map q) J₀ g k (Spec.map q') H (c : ℤ)
    let hφ : φ ≫ q' = q ≫ ψ := regularListPrincipalLiteralQuotientMap_square s r
    let v := canonicalExteriorOpenMap g
      (relativeDifferentialSheaf (Spec.map (C.α ≫ q)))
      (relativeDifferentialSheaf (Spec.map ((C.α ≫ φ) ≫ q'))) d
      (canonicalAmbientConormalTangentIso C.α φ q q' ψ hφ).hom
    (restrictFunctor g).map f ≫ v = T ≫ principalIteratedCore i p n d J C r hr := by
  intro D s t c hc φ ψ g k j q q' H J₀ Ji f T hφ v
  let : IsClosedImmersion (Spec.map q) :=
    IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
  let : IsClosedImmersion (Spec.map q') :=
    IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
  let L := relativeCanonicalModule p n
  let E := canonicalChartCoefficientAtDegree C c rfl
  let := canonicalChartCoefficientQuasicoherent C c rfl
  let e := canonicalChartCoefficientGammaFrame C c rfl
  let bA := canonicalChartAmbientBasisAtDegree C c rfl
  let bA' := canonicalChartAmbientBasisAtDegree D c hc
  let bQ := canonicalChartSourceBasisAtIdeal C (Ideal.ofList s) rfl
  let bQ' := canonicalChartSourceBasisAtIdeal D (Ideal.ofList t) rfl
  have hF := sourceCoreNative C J c rfl
  have hh := principalNativeAtSquare i p n d J C r hr
  exact modelSquareTransport (restrictFunctor g) f _ v T _
    (principalIteratedCore i p n d J C r hr) _ hF
    (principalNativeStep i p n d J C r hr)
    (principalIteratedCore_representation i p n d J C r hr) hh

omit [IsClosedImmersion i] in
/-- The same iterated model map composes with the original resolution lift. -/
private theorem principalCoreResolutionSquare :
    let D := C.principalChart r hr
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let hc := canonicalPrincipalChart_length C r hr c rfl
    let φ : C.A ⟶ D.A :=
      CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    let k := Spec.map φ
    let j := C.jP
    let q' := regularListQuotientMap (A := D.A) t
    letI := IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
    let J₀ := canonicalAmbientChartResolution J j
    let _Jd := canonicalAmbientChartResolution J (k ≫ j)
    let _Ji := affineOpenRestrictedInjectiveResolution φ J₀
    let fd := canonicalChartModelCoreAtDegree D J c hc
    let z := homologyMap (((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex
      (.up ℤ)).map (canonicalAmbientResolutionCompLift j k J).hom') (c : ℤ)
    z ≫ principalIteratedCore i p n d J C r hr = fd := by
  intro D s t c hc φ k j q' J₀ Jd Ji fd z
  let : IsClosedImmersion (Spec.map q') :=
    IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
  let L := relativeCanonicalModule p n
  let E := canonicalChartCoefficientAtDegree C c rfl
  let Ed := canonicalChartCoefficientAtDegree D c hc
  let η := (restrictFunctorComp k j).app L
  let Ei := (restrictFunctor k).mapIso E ≪≫ canonicalAmbientTopOpenIso C.α φ (c + d)
  let := canonicalChartCoefficientQuasicoherent C c rfl
  let := canonicalChartCoefficientQuasicoherent D c hc
  let : (L.restrict (k ≫ j)).IsQuasicoherent :=
    canonicalChartCoefficientQuasicoherent D c hc
  let : ((L.restrict j).restrict k).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor k (L.restrict j)
  let e := canonicalChartCoefficientGammaFrame C c rfl
  let ed := canonicalChartCoefficientGammaFrame D c hc
  let ei := regularListOpenCoefficientFrame φ
    (E' := moduleSpecΓFunctor.obj ((restrictFunctor k).obj (L.restrict j))) e
    (affineRestrictGlobalSectionsIso φ (L.restrict j))
  let Δd := canonicalChartDeterminantAtIdeal D (Ideal.ofList t) rfl c hc
  let bA' := canonicalChartAmbientBasisAtDegree D c hc
  let bQ' := canonicalChartSourceBasisAtIdeal D (Ideal.ofList t) rfl
  let Δi := regularListCanonicalCoefficientDeterminantAt (C.α ≫ φ) t D.weaklyRegular c d
    D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth bA' bQ' hc Ei
  have hFd := canonicalChartModelCoreAtDegree_representation D J c hc
  have hE : Ed = η ≪≫ Ei := by
    apply Iso.ext
    simpa only [η, Ei, Ed, E, D, L, k, j, φ, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc] using
      (canonicalPrincipalChart_coefficient C r hr c rfl).symm
  have hΔ : Δd ≪≫ (pullback (Spec.map q')).mapIso η = Δi := by
    exact transportCoefficientDeterminant (pullback (Spec.map q'))
      (regularListCanonicalDeterminantAt D.α (Ideal.ofList t) c d
        D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth
        bA' bQ' t D.weaklyRegular rfl hc) Ed Ei η hE
  have hΔraw : Δd ≪≫ (pullback (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList t)) :
        D.A ⟶ CommRingCat.of (D.A ⧸ Ideal.ofList t)))).mapIso η = Δi := hΔ
  exact (canonicalModelCoefficientSquare D.α (Ideal.ofList t) c Jd Ji ed ei η
    (canonicalAmbientResolutionCompLift j k J) Δd Δi hΔraw t D.weaklyRegular rfl hc).trans
      hFd.symm

/-- The original target getter has the same native tangent-restriction square. -/
private theorem principalPostfactorSquare :
    let D := C.principalChart r hr
    let s := C.regularList
    let t : List (CommRingCat.of (Localization.Away r)) := regularListPrincipalList s r
    let φ : C.A ⟶ CommRingCat.of (Localization.Away r) :=
      CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    let ψ := regularListPrincipalLiteralQuotientMap s r
    let g := Spec.map ψ
    let a : Spec (regularListQuotientRing s) ⟶ X := C.quotientSource
    let a' : Spec (regularListQuotientRing t) ⟶ X := D.quotientSource
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap (A := CommRingCat.of (Localization.Away r)) t
    let hφ := regularListPrincipalLiteralQuotientMap_square s r
    let h : a' = g ≫ a := by
      simpa only [canonicalChartQuotientSource_eq] using canonicalPrincipalChart_source C r hr
    let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
    let Rₙ := (restrictFunctorCongr h).app N ≪≫ (restrictFunctorComp g a).app N
    let U := canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList s) rfl
    let Ud := canonicalChartSourceTopIsoAtIdeal D (Ideal.ofList D.regularList) rfl
    let v := canonicalExteriorOpenMap g
      (relativeDifferentialSheaf (Spec.map (C.α ≫ q)))
      (relativeDifferentialSheaf (Spec.map ((C.α ≫ φ) ≫ q'))) d
      (canonicalAmbientConormalTangentIso C.α φ q q' ψ hφ).hom
    (restrictFunctor g).map U.hom ≫ v = Rₙ.inv ≫ Ud.hom := by
  intro D s t φ ψ g a a' q q' hφ h N Rₙ U Ud v
  have ht : Rₙ.hom ≫ (restrictFunctor g).map U.hom ≫ v = Ud.hom := by
    have hOld : Rₙ.hom ≫ (restrictFunctor g).map U.hom ≫ v =
        (canonicalChartSourceTopIsoAtIdeal D (Ideal.ofList t) rfl).hom := by
      simpa only [CanonicalPrincipalChartTangentSquare, Rₙ, U, v, a, a',
        canonicalChartQuotientSource_eq, Iso.trans_hom, Iso.app_hom, Category.assoc] using
          canonicalPrincipalChart_tangent C r hr
    exact hOld.trans (principalTargetTopGetter i p n d C r hr)
  exact (moveIsoLeft Rₙ ((restrictFunctor g).map U.hom ≫ v) Ud.hom ht).symm

/-- Keep the native prefactor equation in the original target chart's literal presentation. -/
private theorem principalPrefactorSquare :
    let D := C.principalChart r hr
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let hc := canonicalPrincipalChart_length C r hr c rfl
    let φ : C.A ⟶ D.A := CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      regularListPrincipalLiteralQuotientMap s r
    let g := Spec.map ψ
    let k := Spec.map φ
    let a : Spec (regularListQuotientRing s) ⟶ X := C.quotientSource
    let a' : Spec (regularListQuotientRing t) ⟶ X := D.quotientSource
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap (A := D.A) t
    letI := IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
    letI := IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
    let H : IsPullback g (Spec.map q') (Spec.map q) k :=
      regularListPrincipalLiteralIsPullback s r
    let h : a' = g ≫ a := by
      simpa only [a, a', g, ψ, s, canonicalChartQuotientSource_eq] using
        canonicalPrincipalChart_source C r hr
    let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
      (closedImmersionCanonicalValue i p n)
    let Rₘ : M.restrict a' ≅ (M.restrict a).restrict g :=
      (restrictFunctorCongr h).app M ≪≫ (restrictFunctorComp g a).app M
    let J₀ := canonicalAmbientChartResolution J C.jP
    let S := canonicalChartModelPrefactorAtIdeal C J (Ideal.ofList s) rfl c rfl
    let Sd := canonicalChartModelPrefactorAtIdeal D J (Ideal.ofList D.regularList) rfl c hc
    let T := closedImmersionChartModelStepHomologyMap (Spec.map q) J₀ g k (Spec.map q') H (c : ℤ)
    let z := homologyMap (((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex
      (.up ℤ)).map (canonicalAmbientResolutionCompLift C.jP k J).hom') (c : ℤ)
    Rₘ.inv ≫ Sd.hom ≫ z = (restrictFunctor g).map S.hom ≫ T := by
  exact canonicalPrincipalChart_prefactor i p n d J C r hr

set_option maxHeartbeats 400000 in
-- The original principal chart getters use definitionally equal restriction and
-- quotient presentations; their combined conversions exceed the 200k default.
/-- Paste the original chart factors before expanding the restriction composites. -/
private theorem principalWholeChartPaste :
    CanonicalPrincipalChartPastedSquare i p n d J C r hr := by
  let D := C.principalChart r hr
  let s := C.regularList
  let t := D.regularList
  let c := s.length
  have hc : D.regularList.length = c := canonicalPrincipalChart_length C r hr c rfl
  let φ : C.A ⟶ D.A :=
    CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
  let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      regularListPrincipalLiteralQuotientMap s r
  let g := Spec.map ψ
  let k := Spec.map φ
  let a : Spec (regularListQuotientRing s) ⟶ X := C.quotientSource
  let a' : Spec (regularListQuotientRing t) ⟶ X := D.quotientSource
  let j := C.jP
  let q := regularListQuotientMap s
  let q' := regularListQuotientMap (A := D.A) t
  let : IsClosedImmersion (Spec.map q) :=
    IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
  let : IsClosedImmersion (Spec.map q') :=
    IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
  let H : IsPullback g (Spec.map q') (Spec.map q) k :=
      regularListPrincipalLiteralIsPullback s r
  have h : a' = g ≫ a := by
    simpa only [a, a', g, ψ, s, canonicalChartQuotientSource_eq] using
      canonicalPrincipalChart_source C r hr
  let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
    (closedImmersionCanonicalValue i p n)
  let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
  let Rₘ : M.restrict a' ≅ (M.restrict a).restrict g :=
    (restrictFunctorCongr h).app M ≪≫ (restrictFunctorComp g a).app M
  let Rₙ : N.restrict a' ≅ (N.restrict a).restrict g :=
    (restrictFunctorCongr h).app N ≪≫ (restrictFunctorComp g a).app N
  let J₀ := canonicalAmbientChartResolution J j
  let f := canonicalChartModelCoreAtDegree C J c rfl
  let fd := canonicalChartModelCoreAtDegree D J c hc
  let S := canonicalChartModelPrefactorAtIdeal C J (Ideal.ofList s) rfl c rfl
  let Sd := canonicalChartModelPrefactorAtIdeal D J (Ideal.ofList D.regularList) rfl c hc
  let U := canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList s) rfl
  let Ud := canonicalChartSourceTopIsoAtIdeal D (Ideal.ofList D.regularList) rfl
  let T := closedImmersionChartModelStepHomologyMap (Spec.map q) J₀ g k (Spec.map q') H (c : ℤ)
  let hφ : φ ≫ q' = q ≫ ψ := regularListPrincipalLiteralQuotientMap_square s r
  let v := canonicalExteriorOpenMap g
    (relativeDifferentialSheaf (Spec.map (C.α ≫ q)))
    (relativeDifferentialSheaf (Spec.map ((C.α ≫ φ) ≫ q'))) d
    (canonicalAmbientConormalTangentIso C.α φ q q' ψ hφ).hom
  let z := homologyMap (((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex
    (.up ℤ)).map (canonicalAmbientResolutionCompLift j k J).hom') (c : ℤ)
  let fi := principalIteratedCore i p n d J C r hr
  have hf := principalCoreOpenSquare i p n d J C r hr
  have hz := principalCoreResolutionSquare i p n d J C r hr
  have hS := principalPrefactorSquare i p n d J C r hr
  have hU := principalPostfactorSquare i p n d C r hr
  have hC := canonicalChartModelCoreAtDegree_factor C J c rfl
  have hD := canonicalChartModelCoreAtDegree_factor D J c hc
  have hw := wholeChartPaste
    (C := (Spec (regularListQuotientRing s)).Modules)
    (D := (Spec (regularListQuotientRing t)).Modules)
    (M := M.restrict a)
    (H := regularListModelTopHomologyAt (Ideal.ofList s) J₀ c)
    (Q := regularListTangentTopAt C.α (Ideal.ofList s) d)
    (N := N.restrict a)
    (M' := M.restrict a')
    (H' := regularListModelTopHomologyAt (Ideal.ofList D.regularList)
      (canonicalAmbientChartResolution J D.jP) c)
    (H'' := regularListModelTopHomologyAt (Ideal.ofList D.regularList)
      (canonicalAmbientChartResolution J₀ k) c)
    (Q' := regularListTangentTopAt D.α (Ideal.ofList D.regularList) d)
    (N' := N.restrict a')
    (restrictFunctor g) S Sd U Ud f fd fi Rₘ Rₙ T z v hS hf hz hU _ _ hC hD
  exact hw

/-- The original whole chart arrows agree on the actual principal refinement. -/
theorem canonicalCommonModelChartHomologyIso_principal :
    CanonicalPrincipalChartArrowSquare i p n d J C r hr := by
  let g := Spec.map (regularListPrincipalLiteralQuotientMap C.regularList r)
  let h := canonicalPrincipalChart_source C r hr
  let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
    (closedImmersionCanonicalValue i p n)
  have hPaste := principalWholeChartPaste i p n d J C r hr
  exact (Category.assoc ((restrictFunctorCongr h).hom.app M)
    ((restrictFunctorComp g C.quotientChart.jX).hom.app M)
    ((restrictFunctor g).map
      (canonicalCommonModelChartHomologyIso i p n d J C).hom)).symm.trans hPaste

end AlgebraicGeometry.Scheme.Modules
