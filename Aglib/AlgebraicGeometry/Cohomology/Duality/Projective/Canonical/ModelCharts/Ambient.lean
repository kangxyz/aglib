/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Principal
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AmbientGeometry
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AmbientModel
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenComparison.Ambient

/-!
# The original whole chart arrow under an ambient isomorphism

The original ambient model comparison, the same resolution composition
and the original differential factors compare the actual chart arrows.
The quotient map and all determinant and coefficient comparisons are
produced from the given ambient isomorphism.
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

private theorem sourceSquareTransport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M H : C} {M' H' K : D}
    (s t : M ≅ H) (s' t' : M' ≅ H') (r : F.obj M ⟶ M')
    (T : F.obj H ⟶ K) (z : H' ⟶ K) (hs : s = t) (ht : s' = t')
    (h : r ≫ t'.hom ≫ z = F.map t.hom ≫ T) :
    r ≫ s'.hom ≫ z = F.map s.hom ≫ T := by
  cases hs
  cases ht
  exact h

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

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance ambientChartArrowStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

local instance {A : CommRingCat.{u}} (s : List A) :
    IsClosedImmersion (Spec.map (regularListQuotientMap s)) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

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

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) [IsClosedImmersion i]
  (n d : ℕ) (J : InjectiveResolution (relativeCanonicalModule p n))
  {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)
  {A' : CommRingCat.{u}} (eA : C.A ≅ A')

omit [IsClosedImmersion i] in
private theorem ambientTargetTopGetter :
    (canonicalChartSourceTopIsoAtIdeal (C.ambientIsoChart eA)
      (Ideal.ofList (C.regularList.map eA.hom.hom)) rfl).hom =
    (canonicalChartSourceTopIsoAtIdeal (C.ambientIsoChart eA)
      (Ideal.ofList (C.ambientIsoChart eA).regularList) rfl).hom := rfl

/-- The original whole-arrow equation on the actual ambient-normalized quotient chart. -/
def CanonicalAmbientChartArrowSquare : Prop :=
  let D := C.ambientIsoChart eA
  let g := Spec.map (canonicalAmbientIsoChartQuotientMap C eA)
  let h := canonicalAmbientIsoChart_source C eA
  let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
    (closedImmersionCanonicalValue i p n)
  let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
  (restrictFunctorCongr h).hom.app M ≫
      (restrictFunctorComp g C.quotientSource).hom.app M ≫
      (restrictFunctor g).map (canonicalCommonModelChartHomologyIso i p n d J C).hom =
    (canonicalCommonModelChartHomologyIso i p n d J D).hom ≫
      (restrictFunctorCongr h).hom.app N ≫
      (restrictFunctorComp g C.quotientSource).hom.app N

/-- The same whole-arrow equation with the restriction isomorphisms kept together. -/
private def CanonicalAmbientChartPastedSquare : Prop :=
  let D := C.ambientIsoChart eA
  let g := Spec.map (canonicalAmbientIsoChartQuotientMap C eA)
  let h := canonicalAmbientIsoChart_source C eA
  let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
    (closedImmersionCanonicalValue i p n)
  let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
  let Rₘ := (restrictFunctorCongr h).app M ≪≫
    (restrictFunctorComp g C.quotientSource).app M
  let Rₙ := (restrictFunctorCongr h).app N ≪≫
    (restrictFunctorComp g C.quotientSource).app N
  Rₘ.hom ≫ (restrictFunctor g).map (canonicalCommonModelChartHomologyIso i p n d J C).hom =
    (canonicalCommonModelChartHomologyIso i p n d J D).hom ≫ Rₙ.hom

omit [IsClosedImmersion i] in
/-- The native producer predicate, with all target objects from the original chart. -/
private theorem ambientNativeModelSquare :
    let D := C.ambientIsoChart eA
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let hc := C.ambientIsoChart_regularList_length eA
    let φ : C.A ⟶ D.A := eA.hom
    let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      canonicalAmbientIsoChartQuotientMap C eA
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap t
    let hφ : φ ≫ q' = q ≫ ψ := canonicalAmbientIsoChart_ringSquare C eA
    let H : IsPullback (Spec.map ψ) (Spec.map q') (Spec.map q) (Spec.map φ) :=
      canonicalAmbientIsoChart_isPullback C eA
    let J₀ := canonicalAmbientChartResolution J C.jP
    let E := canonicalChartCoefficientAtDegree C c rfl
    letI := canonicalChartCoefficientQuasicoherent C c rfl
    CanonicalRegularListModelOpenSquare (A' := D.A) C.α s t C.weaklyRegular D.weaklyRegular
      φ ψ hφ C.quotientChart.ambientFormallySmooth C.quotientChart.sourceFormallySmooth
      D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth
      (canonicalChartAmbientBasisAtDegree C c rfl) (canonicalChartAmbientBasisAtDegree D c hc)
      (canonicalChartSourceBasisAtIdeal C (Ideal.ofList s) rfl)
      (canonicalChartSourceBasisAtIdeal D (Ideal.ofList D.regularList) rfl) hc
      J₀ (canonicalChartCoefficientGammaFrame C c rfl) E
      (canonicalAmbientSheafHomologyMap φ q q' ψ H J₀ (c : ℤ)) := by
  intro D s t c hc φ ψ q q' hφ H J₀ E
  let := canonicalChartCoefficientQuasicoherent C c rfl
  exact regularListCanonicalModelTopHomologyIso_ambient C.α eA.commRingCatIsoToRingEquiv
    s C.weaklyRegular
    D.weaklyRegular C.quotientChart.ambientFormallySmooth
    C.quotientChart.sourceFormallySmooth D.quotientChart.ambientFormallySmooth
    D.quotientChart.sourceFormallySmooth
    (canonicalChartAmbientBasisAtDegree C c rfl) (canonicalChartAmbientBasisAtDegree D c hc)
    (canonicalChartSourceBasisAtIdeal C (Ideal.ofList s) rfl)
    (canonicalChartSourceBasisAtIdeal D (Ideal.ofList D.regularList) rfl)
    J₀ (canonicalChartCoefficientGammaFrame C c rfl) E

omit [IsClosedImmersion i] in
/-- The existing raw model map on the iterated restricted resolution. -/
private def ambientIteratedCore :
    let D := C.ambientIsoChart eA
    let s := C.regularList
    let _t := D.regularList
    let c := s.length
    let φ : C.A ⟶ D.A :=
      eA.hom
    regularListModelTopHomologyAt (Ideal.ofList D.regularList)
        (canonicalAmbientChartResolution (canonicalAmbientChartResolution J C.jP) (Spec.map φ)) c ⟶
      regularListTangentTopAt D.α (Ideal.ofList D.regularList) d := by
  intro D s t c φ
  let hc := C.ambientIsoChart_regularList_length eA
  let k := Spec.map φ
  let j := C.jP
  let L := relativeCanonicalModule p n
  let J₀ := canonicalAmbientChartResolution J j
  let Ji := canonicalAmbientChartResolution J₀ k
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
  let bQ' := canonicalChartSourceBasisAtIdeal D (Ideal.ofList D.regularList) rfl
  let Δi := regularListCanonicalCoefficientDeterminantAt (C.α ≫ φ) t D.weaklyRegular c d
    D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth bA' bQ' hc Ei
  exact regularListCanonicalModelMapAt (C.α ≫ φ) (Ideal.ofList D.regularList) c Ji ei Δi t
    D.weaklyRegular rfl hc

omit [IsClosedImmersion i] in
/-- The target alias has exactly the same native producer representation. -/
private theorem ambientIteratedCore_representation :
    let D := C.ambientIsoChart eA
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let φ : C.A ⟶ D.A :=
      eA.hom
    let hc := C.ambientIsoChart_regularList_length eA
    let k := Spec.map φ
    let j := C.jP
    let L := relativeCanonicalModule p n
    let J₀ := canonicalAmbientChartResolution J j
    let Ji := canonicalAmbientChartResolution J₀ k
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
    let bQ' := canonicalChartSourceBasisAtIdeal D (Ideal.ofList D.regularList) rfl
    let Δi := regularListCanonicalCoefficientDeterminantAt (C.α ≫ φ) t D.weaklyRegular c d
      D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth bA' bQ' hc Ei
    ambientIteratedCore i p n d J C eA =
      regularListCanonicalModelMapAt (C.α ≫ φ) (Ideal.ofList D.regularList) c Ji ei Δi t
        D.weaklyRegular rfl hc := by
  rfl

omit [IsClosedImmersion i] in
/-- The original native literal step, with the original target model object. -/
private theorem ambientNativeStep :
    let D := C.ambientIsoChart eA
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let φ : C.A ⟶ D.A := eA.hom
    let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      canonicalAmbientIsoChartQuotientMap C eA
    let g := Spec.map ψ
    let k := Spec.map φ
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap t
    letI := IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
    letI := IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
    let H : IsPullback g (Spec.map q') (Spec.map q) k :=
      canonicalAmbientIsoChart_isPullback C eA
    let J₀ := canonicalAmbientChartResolution J C.jP
    let Hi := regularListModelTopHomologyAt (Ideal.ofList D.regularList)
      (canonicalAmbientChartResolution J₀ k) c
    let T₀ : (regularListModelTopHomologyAt (Ideal.ofList s) J₀ c).restrict g ⟶ Hi :=
      canonicalAmbientSheafHomologyMap φ q q' ψ H J₀ (c : ℤ)
    T₀ = closedImmersionChartModelStepHomologyMap (Spec.map q) J₀ g k (Spec.map q') H (c : ℤ) := by
  intro D s t c φ ψ g k q q' H J₀ Hi T₀
  let : IsClosedImmersion (Spec.map q) :=
    IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
  let : IsClosedImmersion (Spec.map q') :=
    IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
  exact canonicalAmbientSheafHomologyMap_eq_step φ q q' ψ H J₀ (c : ℤ)

omit [IsClosedImmersion i] in
/-- The native model supplier on the original target model and tangent objects. -/
private theorem ambientNativeAtSquare :
    let D := C.ambientIsoChart eA
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let hc := C.ambientIsoChart_regularList_length eA
    let φ : C.A ⟶ D.A := eA.hom
    let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      canonicalAmbientIsoChartQuotientMap C eA
    let g := Spec.map ψ
    let k := Spec.map φ
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap t
    let hφ : φ ≫ q' = q ≫ ψ := canonicalAmbientIsoChart_ringSquare C eA
    let H : IsPullback g (Spec.map q') (Spec.map q) k :=
      canonicalAmbientIsoChart_isPullback C eA
    let L := (relativeCanonicalModule p n).restrict C.jP
    let J₀ := canonicalAmbientChartResolution J C.jP
    let Hi := regularListModelTopHomologyAt (Ideal.ofList D.regularList)
      (canonicalAmbientChartResolution J₀ k) c
    let Qd := regularListTangentTopAt D.α (Ideal.ofList D.regularList) d
    let E := canonicalChartCoefficientAtDegree C c rfl
    letI := canonicalChartCoefficientQuasicoherent C c rfl
    letI : ((restrictFunctor k).obj L).IsQuasicoherent := isQuasicoherent_restrictFunctor k L
    let e := canonicalChartCoefficientGammaFrame C c rfl
    let bA := canonicalChartAmbientBasisAtDegree C c rfl
    let bA' := canonicalChartAmbientBasisAtDegree D c hc
    let bQ := canonicalChartSourceBasisAtIdeal C (Ideal.ofList s) rfl
    let bQ' := canonicalChartSourceBasisAtIdeal D (Ideal.ofList D.regularList) rfl
    let Δ := regularListCanonicalCoefficientDeterminantAt C.α s C.weaklyRegular c d
      C.quotientChart.ambientFormallySmooth C.quotientChart.sourceFormallySmooth bA bQ rfl E
    let Ei := (restrictFunctor k).mapIso E ≪≫ canonicalAmbientTopOpenIso C.α φ (c + d)
    let ei := regularListOpenCoefficientFrame φ
      (E' := moduleSpecΓFunctor.obj ((restrictFunctor k).obj L)) e
      (affineRestrictGlobalSectionsIso φ L)
    let Δi := regularListCanonicalCoefficientDeterminantAt (C.α ≫ φ) t D.weaklyRegular c d
      D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth bA' bQ' hc Ei
    let f₀ := regularListCanonicalModelMapAt C.α (Ideal.ofList s) c J₀ e Δ s C.weaklyRegular rfl rfl
    let fi₀ : Hi ⟶ Qd := regularListCanonicalModelMapAt (C.α ≫ φ) (Ideal.ofList D.regularList) c
      (canonicalAmbientChartResolution J₀ k) ei Δi t D.weaklyRegular rfl hc
    let T₀ : (regularListModelTopHomologyAt (Ideal.ofList s) J₀ c).restrict g ⟶ Hi :=
      canonicalAmbientSheafHomologyMap φ q q' ψ H J₀ (c : ℤ)
    let v := canonicalExteriorOpenMap g
      (relativeDifferentialSheaf (Spec.map (C.α ≫ q)))
      (relativeDifferentialSheaf (Spec.map ((C.α ≫ φ) ≫ q'))) d
      (canonicalAmbientConormalTangentIso C.α φ q q' ψ hφ).hom
    (restrictFunctor g).map f₀ ≫ v = T₀ ≫ fi₀ := by
  intro D s t c hc φ ψ g k q q' hφ H L J₀ Hi Qd E e bA bA' bQ bQ' Δ Ei ei Δi f₀ fi₀ T₀ v
  let := canonicalChartCoefficientQuasicoherent C c rfl
  let : ((restrictFunctor k).obj L).IsQuasicoherent := isQuasicoherent_restrictFunctor k L
  exact canonicalModelOpenSquareAt C.α s t C.weaklyRegular D.weaklyRegular φ ψ hφ
    C.quotientChart.ambientFormallySmooth C.quotientChart.sourceFormallySmooth
    D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth
    bA bA' bQ bQ' hc J₀ e E
    (canonicalAmbientSheafHomologyMap φ q q' ψ H J₀ (c : ℤ))
    (ambientNativeModelSquare i p n d J C eA)

omit [IsClosedImmersion i] in
/-- The original source core has the native ambient-isomorphism square. -/
private theorem ambientCoreOpenSquare :
    let D := C.ambientIsoChart eA
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let _hc := C.ambientIsoChart_regularList_length eA
    let φ : C.A ⟶ D.A :=
      eA.hom
    let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      canonicalAmbientIsoChartQuotientMap C eA
    let g := Spec.map ψ
    let k := Spec.map φ
    let j := C.jP
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap (A := D.A) t
    letI := IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
    letI := IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
    let H : IsPullback g (Spec.map q') (Spec.map q) k :=
      canonicalAmbientIsoChart_isPullback C eA
    let J₀ := canonicalAmbientChartResolution J j
    let _Ji := canonicalAmbientChartResolution J₀ k
    let f := canonicalChartModelCoreAtDegree C J c rfl
    let T := closedImmersionChartModelStepHomologyMap (Spec.map q) J₀ g k (Spec.map q') H (c : ℤ)
    let hφ : φ ≫ q' = q ≫ ψ := canonicalAmbientIsoChart_ringSquare C eA
    let v := canonicalExteriorOpenMap g
      (relativeDifferentialSheaf (Spec.map (C.α ≫ q)))
      (relativeDifferentialSheaf (Spec.map ((C.α ≫ φ) ≫ q'))) d
      (canonicalAmbientConormalTangentIso C.α φ q q' ψ hφ).hom
    (restrictFunctor g).map f ≫ v = T ≫ ambientIteratedCore i p n d J C eA := by
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
  let bQ' := canonicalChartSourceBasisAtIdeal D (Ideal.ofList D.regularList) rfl
  have hF := sourceCoreNative C J c rfl
  have hh := ambientNativeAtSquare i p n d J C eA
  exact modelSquareTransport (restrictFunctor g) f _ v T _
    (ambientIteratedCore i p n d J C eA) _ hF
    (ambientNativeStep i p n d J C eA)
    (ambientIteratedCore_representation i p n d J C eA) hh

omit [IsClosedImmersion i] in
/-- The same iterated model map composes with the original resolution lift. -/
private theorem ambientCoreResolutionSquare :
    let D := C.ambientIsoChart eA
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let hc := C.ambientIsoChart_regularList_length eA
    let φ : C.A ⟶ D.A :=
      eA.hom
    let k := Spec.map φ
    let j := C.jP
    let q' := regularListQuotientMap (A := D.A) t
    letI := IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
    let J₀ := canonicalAmbientChartResolution J j
    let _Jd := canonicalAmbientChartResolution J (k ≫ j)
    let _Ji := canonicalAmbientChartResolution J₀ k
    let fd := canonicalChartModelCoreAtDegree D J c hc
    let z := homologyMap (((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex
      (.up ℤ)).map (canonicalAmbientResolutionCompLift j k J).hom') (c : ℤ)
    z ≫ ambientIteratedCore i p n d J C eA = fd := by
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
  let Δd := canonicalChartDeterminantAtIdeal D (Ideal.ofList D.regularList) rfl c hc
  let bA' := canonicalChartAmbientBasisAtDegree D c hc
  let bQ' := canonicalChartSourceBasisAtIdeal D (Ideal.ofList D.regularList) rfl
  let Δi := regularListCanonicalCoefficientDeterminantAt (C.α ≫ φ) t D.weaklyRegular c d
    D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth bA' bQ' hc Ei
  have hFd := canonicalChartModelCoreAtDegree_representation D J c hc
  have hE : Ed = η ≪≫ Ei := by
    apply Iso.ext
    simpa only [η, Ei, Ed, E, D, L, k, j, φ, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc] using
      (canonicalAmbientIsoChart_coefficient C eA c rfl).symm
  have hΔ : Δd ≪≫ (pullback (Spec.map q')).mapIso η = Δi := by
    exact transportCoefficientDeterminant (pullback (Spec.map q'))
      (regularListCanonicalDeterminantAt D.α (Ideal.ofList D.regularList) c d
        D.quotientChart.ambientFormallySmooth D.quotientChart.sourceFormallySmooth
        bA' bQ' t D.weaklyRegular rfl hc) Ed Ei η hE
  have hΔraw : Δd ≪≫ (pullback (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList D.regularList)) :
        D.A ⟶ CommRingCat.of (D.A ⧸ Ideal.ofList D.regularList)))).mapIso η = Δi := hΔ
  exact (canonicalModelCoefficientSquare D.α (Ideal.ofList D.regularList) c Jd Ji ed ei η
    (canonicalAmbientResolutionCompLift j k J) Δd Δi hΔraw t D.weaklyRegular rfl hc).trans
      hFd.symm

/-- The original target getter has the same native tangent-restriction square. -/
private theorem ambientPostfactorSquare :
    let D := C.ambientIsoChart eA
    let s := C.regularList
    let t := D.regularList
    let φ : C.A ⟶ D.A :=
      eA.hom
    let ψ := canonicalAmbientIsoChartQuotientMap C eA
    let g := Spec.map ψ
    let a : Spec (regularListQuotientRing s) ⟶ X := C.quotientSource
    let a' : Spec (regularListQuotientRing t) ⟶ X := D.quotientSource
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap (A := D.A) t
    let hφ := canonicalAmbientIsoChart_ringSquare C eA
    let h : a' = g ≫ a := canonicalAmbientIsoChart_source C eA
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
        (canonicalChartSourceTopIsoAtIdeal D
          (Ideal.ofList (C.regularList.map eA.hom.hom)) rfl).hom := by
      have hNative := canonicalAmbientIsoChart_tangent C eA
      simp only [CanonicalAmbientIsoChartTangentSquare, Rₙ, U, v, a, a',
        D, s, t, φ, ψ, g, q, q', N,
        SmoothClosedImmersionLocalChart.ambientIsoChart_regularList,
        AlgebraicGeometry.Scheme.Modules.restrict, Functor.comp_obj,
        Iso.trans_hom, Iso.app_hom, Category.assoc] at hNative ⊢
      exact hNative
    exact hOld.trans (ambientTargetTopGetter i p n d C eA)
  exact (moveIsoLeft Rₙ ((restrictFunctor g).map U.hom ≫ v) Ud.hom ht).symm

/-- Keep the native prefactor equation in the original target chart's literal presentation. -/
private theorem ambientPrefactorSquare :
    let D := C.ambientIsoChart eA
    let s := C.regularList
    let t := D.regularList
    let c := s.length
    let hc := C.ambientIsoChart_regularList_length eA
    let φ : C.A ⟶ D.A := eA.hom
    let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      canonicalAmbientIsoChartQuotientMap C eA
    let g := Spec.map ψ
    let k := Spec.map φ
    let a : Spec (regularListQuotientRing s) ⟶ X := C.quotientSource
    let a' : Spec (regularListQuotientRing t) ⟶ X := D.quotientSource
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap (A := D.A) t
    letI := IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
    letI := IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
    let H : IsPullback g (Spec.map q') (Spec.map q) k :=
      canonicalAmbientIsoChart_isPullback C eA
    let h : a' = g ≫ a := canonicalAmbientIsoChart_source C eA
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
  intro D s t c hc φ ψ g k a a' q q' H h M Rₘ J₀ S Sd T z
  let : IsClosedImmersion (Spec.map q) :=
    IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
  let : IsClosedImmersion (Spec.map q') :=
    IsClosedImmersion.spec_of_surjective q' Ideal.Quotient.mk_surjective
  let S₀ : M.restrict a ≅ regularListModelTopHomologyAt (Ideal.ofList s) J₀ c :=
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

set_option maxHeartbeats 400000 in
-- The original ambient chart getters have several equal restriction and quotient
-- presentations; their combined conversions in this paste exceed the 200k default.
/-- Paste the original chart factors before expanding the restriction composites. -/
private theorem ambientWholeChartPaste :
    CanonicalAmbientChartPastedSquare i p n d J C eA := by
  let D := C.ambientIsoChart eA
  let s := C.regularList
  let t := D.regularList
  let c := s.length
  have hc : D.regularList.length = c := C.ambientIsoChart_regularList_length eA
  let φ : C.A ⟶ D.A :=
    eA.hom
  let ψ : regularListQuotientRing s ⟶ regularListQuotientRing t :=
      canonicalAmbientIsoChartQuotientMap C eA
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
      canonicalAmbientIsoChart_isPullback C eA
  have h : a' = g ≫ a := canonicalAmbientIsoChart_source C eA
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
  let hφ : φ ≫ q' = q ≫ ψ := canonicalAmbientIsoChart_ringSquare C eA
  let v := canonicalExteriorOpenMap g
    (relativeDifferentialSheaf (Spec.map (C.α ≫ q)))
    (relativeDifferentialSheaf (Spec.map ((C.α ≫ φ) ≫ q'))) d
    (canonicalAmbientConormalTangentIso C.α φ q q' ψ hφ).hom
  let z := homologyMap (((closedImmersionRightAdjoint (Spec.map q')).mapHomologicalComplex
    (.up ℤ)).map (canonicalAmbientResolutionCompLift j k J).hom') (c : ℤ)
  let fi := ambientIteratedCore i p n d J C eA
  have hf := ambientCoreOpenSquare i p n d J C eA
  have hz := ambientCoreResolutionSquare i p n d J C eA
  have hS := ambientPrefactorSquare i p n d J C eA
  have hU := ambientPostfactorSquare i p n d C eA
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

/-- The original whole chart arrows agree on the actual ambient isomorphism. -/
theorem canonicalCommonModelChartHomologyIso_ambientIso :
    CanonicalAmbientChartArrowSquare i p n d J C eA := by
  let g := Spec.map (canonicalAmbientIsoChartQuotientMap C eA)
  let h := canonicalAmbientIsoChart_source C eA
  let M := (DerivedCategory.Plus.homologyFunctor X.Modules ((n : ℤ) - d)).obj
    (closedImmersionCanonicalValue i p n)
  have hPaste := ambientWholeChartPaste i p n d J C eA
  exact (Category.assoc ((restrictFunctorCongr h).hom.app M)
    ((restrictFunctorComp g C.quotientSource).hom.app M)
    ((restrictFunctor g).map
      (canonicalCommonModelChartHomologyIso i p n d J C).hom)).symm.trans hPaste

end AlgebraicGeometry.Scheme.Modules
