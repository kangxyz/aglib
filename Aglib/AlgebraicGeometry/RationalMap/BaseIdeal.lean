/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FractionalIdeal.Denominator
public import Aglib.RingTheory.Ideal.LocalizedRange
public import Mathlib.RingTheory.Localization.Algebra
public import Aglib.AlgebraicGeometry.Modules.RationalFunctions.CommonFractionalIdeal
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Subobjects
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus
public import Aglib.AlgebraicGeometry.IdealSheaf.Artinian
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.RingTheory.RegularLocalRing.Factorial
public import Aglib.RingTheory.RegularLocalRing.HeightOnePrincipal
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Actual denominator and base ideals of original rational coordinates

A finite tuple in the original function field defines a pullback of actual
module sheaves. Its denominator projection is monic. The native image-ideal
construction produces the actual denominator and base ideal sheaves, with
original module-linear coordinate maps. No affine denominator family or
projective presentation is supplied as input.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.RationalFunctions
open AlgebraicGeometry.Scheme.Modules.Invertible

open scoped nonZeroDivisors

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

namespace AlgebraicGeometry.Scheme.RationalCoordinates

variable (X : Scheme.{u}) [IsIntegral X]

private theorem unit_finitePresentation (Y : Scheme.{u}) :
    (SheafOfModules.unit Y.ringCatSheaf).IsFinitePresentation := by
  let e : SheafOfModules.free (R := Y.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit Y.ringCatSheaf :=
    Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf)
  exact (finitePresentation_iff_of_iso e).mp (finitePresentation_free (X := Y) PUnit.{u + 1})

private theorem genericInclusion_isAffineHom :
    IsAffineHom (X.fromSpecStalk (genericPoint X)) := by
  constructor
  intro U _
  by_cases hU : Nonempty U
  · let := hU
    rw [CommonFractionalIdeal.generic_preimage_eq_top X U]
    exact isAffineOpen_top _
  · have hbot : U = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hU ⟨⟨x, hx⟩⟩).elim
      · simp
    simpa only [hbot, Scheme.Hom.preimage_bot] using
      isAffineOpen_bot (Spec X.functionField)

private theorem rationalModule_quasicoherent :
    (CommonFractionalIdeal.rationalFunctions X).IsQuasicoherent := by
  let : IsAffineHom (X.fromSpecStalk (genericPoint X)) := genericInclusion_isAffineHom X
  have : (SheafOfModules.unit (Spec X.functionField).ringCatSheaf).IsFinitePresentation :=
    unit_finitePresentation (Spec X.functionField)
  exact isQuasicoherent_pushforward_of_isAffineHom
    (X.fromSpecStalk (genericPoint X)) (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)

/-- Multiplication by the specified original function, including zero. -/
def multiplier (a : X.functionField) :
    CommonFractionalIdeal.rationalFunctions X ⟶ CommonFractionalIdeal.rationalFunctions X := by
  classical
  exact if ha : a = 0 then 0 else
    (CommonFractionalIdeal.rationalMultiplier X (Units.mk0 a ha)).hom

theorem multiplier_value (a : X.functionField) (U : X.Opens) [Nonempty U]
    (s : (CommonFractionalIdeal.rationalFunctions X).val.obj (op U)) :
    CommonFractionalIdeal.rationalValue X U ((multiplier X a).val.app (op U) s) =
      a * CommonFractionalIdeal.rationalValue X U s := by
  classical
  by_cases ha : a = 0
  · subst a
    let ev := SheafOfModules.evaluation X.ringCatSheaf (op U)
    have hz : ev.map (0 : CommonFractionalIdeal.rationalFunctions X ⟶
        CommonFractionalIdeal.rationalFunctions X) = 0 := ev.map_zero _ _
    have hs : (0 : CommonFractionalIdeal.rationalFunctions X ⟶
        CommonFractionalIdeal.rationalFunctions X).val.app (op U) s = 0 :=
      congrArg (fun g ↦ g.hom s) hz
    rw [show multiplier X 0 = 0 by simp [multiplier]]
    exact (congrArg (CommonFractionalIdeal.rationalValue X U) hs).trans
      ((CommonFractionalIdeal.rationalValue X U).map_zero.trans (zero_mul _).symm)
  · rw [show multiplier X a = (CommonFractionalIdeal.rationalMultiplier X
        (Units.mk0 a ha)).hom by simp only [multiplier, dite_eq_right ha]]
    change CommonFractionalIdeal.rationalValue X U
        ((CommonFractionalIdeal.rationalMultiplier X (Units.mk0 a ha)).hom.app U s) = _
    exact CommonFractionalIdeal.rationalMultiplier_value X (Units.mk0 a ha) U s

/-- The actual regular-coordinate map into the product of rational modules. -/
def regularTupleMap (ι : Type u) :
    (∏ᶜ fun _ : ι ↦ CommonFractionalIdeal.regularModule X) ⟶
      ∏ᶜ fun _ : ι ↦ CommonFractionalIdeal.rationalFunctions X :=
  Limits.Pi.map (fun _ ↦ CommonFractionalIdeal.regularMap X)

instance regularTupleMapMono (ι : Type u) : Mono (regularTupleMap X ι) := by
  dsimp only [regularTupleMap]
  infer_instance

/-- The row retains the originally specified function at every coordinate. -/
def coordinateRow {ι : Type u} (f : ι → X.functionField) :
    CommonFractionalIdeal.regularModule X ⟶
      ∏ᶜ fun _ : ι ↦ CommonFractionalIdeal.rationalFunctions X :=
  Limits.Pi.lift (fun i ↦ CommonFractionalIdeal.regularMap X ≫ multiplier X (f i))

/-- The actual simultaneous denominator and numerator relation module. -/
def relationModule {ι : Type u} (f : ι → X.functionField) : X.Modules :=
  Limits.pullback (regularTupleMap X ι) (coordinateRow X f)

/-- The original integral denominator projection. -/
def relationInclusion {ι : Type u} (f : ι → X.functionField) :
    relationModule X f ⟶ CommonFractionalIdeal.regularModule X :=
  Limits.pullback.snd _ _

instance relationInclusionMono {ι : Type u} (f : ι → X.functionField) :
    Mono (relationInclusion X f) := by
  dsimp only [relationInclusion]
  infer_instance

/-- The actual original numerator at the specified coordinate. -/
def relationNumerator {ι : Type u} (f : ι → X.functionField) (i : ι) :
    relationModule X f ⟶ CommonFractionalIdeal.regularModule X :=
  Limits.pullback.fst _ _ ≫ Limits.Pi.π (fun _ : ι ↦ CommonFractionalIdeal.regularModule X) i

@[reassoc]
theorem relationNumerator_regularMap {ι : Type u} (f : ι → X.functionField) (i : ι) :
    relationNumerator X f i ≫ CommonFractionalIdeal.regularMap X =
      relationInclusion X f ≫ CommonFractionalIdeal.regularMap X ≫ multiplier X (f i) := by
  have hc : Limits.pullback.fst (regularTupleMap X ι) (coordinateRow X f) ≫
      regularTupleMap X ι =
      Limits.pullback.snd (regularTupleMap X ι) (coordinateRow X f) ≫ coordinateRow X f :=
    Limits.pullback.condition
  have h := congrArg
    (fun g ↦ g ≫ Limits.Pi.π (fun _ : ι ↦ CommonFractionalIdeal.rationalFunctions X) i) hc
  simpa only [relationNumerator, relationInclusion, regularTupleMap, coordinateRow,
    Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π] using h

theorem relationNumerator_value {ι : Type u} (f : ι → X.functionField) (i : ι)
    (U : X.Opens) [Nonempty U] (s : (relationModule X f).val.obj (op U)) :
    X.germToFunctionField U ((relationNumerator X f i).val.app (op U) s) =
      X.germToFunctionField U ((relationInclusion X f).val.app (op U) s) * f i := by
  have h := congrArg (fun g ↦ g.val.app (op U) s) (relationNumerator_regularMap X f i)
  have hv := congrArg (CommonFractionalIdeal.rationalValue X U) h
  change CommonFractionalIdeal.rationalValue X U
      ((CommonFractionalIdeal.regularMap X).val.app (op U)
        ((relationNumerator X f i).val.app (op U) s)) =
    CommonFractionalIdeal.rationalValue X U ((multiplier X (f i)).val.app (op U)
      ((CommonFractionalIdeal.regularMap X).val.app (op U)
        ((relationInclusion X f).val.app (op U) s))) at hv
  calc
    _ = CommonFractionalIdeal.rationalValue X U
        ((CommonFractionalIdeal.regularMap X).val.app (op U)
          ((relationNumerator X f i).val.app (op U) s)) :=
      (CommonFractionalIdeal.regularMap_value X U _).symm
    _ = _ := hv
    _ = f i * CommonFractionalIdeal.rationalValue X U
        ((CommonFractionalIdeal.regularMap X).val.app (op U)
          ((relationInclusion X f).val.app (op U) s)) := multiplier_value X (f i) U _
    _ = f i * X.germToFunctionField U
        ((relationInclusion X f).val.app (op U) s) :=
      congrArg (fun z ↦ f i * z)
        (CommonFractionalIdeal.regularMap_value X U _)
    _ = _ := mul_comm _ _

instance relationModuleQuasicoherent {ι : Type u} [Finite ι] (f : ι → X.functionField) :
    (relationModule X f).IsQuasicoherent := by
  have : (CommonFractionalIdeal.regularModule X).IsFinitePresentation :=
    unit_finitePresentation X
  have : (CommonFractionalIdeal.rationalFunctions X).IsQuasicoherent :=
    rationalModule_quasicoherent X
  have hO : (CommonFractionalIdeal.regularModule X).IsQuasicoherent := inferInstance
  have hQ : (CommonFractionalIdeal.rationalFunctions X).IsQuasicoherent := inferInstance
  have hPO : (∏ᶜ fun _ : ι ↦ CommonFractionalIdeal.regularModule X).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_pi _ (fun _ ↦ hO)
  have hPQ : (∏ᶜ fun _ : ι ↦ CommonFractionalIdeal.rationalFunctions X).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_pi _ (fun _ ↦ hQ)
  apply (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit
    (Limits.pullback.isLimit (regularTupleMap X ι) (coordinateRow X f))
  intro j
  cases j with
  | none => exact hPQ
  | some j =>
    cases j with
    | left => exact hPO
    | right => exact hO

/-- The genuine ideal-sheaf data of the original denominator inclusion. -/
def denominatorIdeal {ι : Type u} (f : ι → X.functionField) : X.IdealSheafData :=
  Hom.imageIdealData (relationInclusion X f)

/-- The actual module of the canonical denominator ideal. -/
def denominatorModule {ι : Type u} (f : ι → X.functionField) : X.Modules :=
  Hom.idealModule (Hom.zeroInclusion (relationInclusion X f))

/-- Its original embedded ideal inclusion. -/
def denominatorInclusion {ι : Type u} (f : ι → X.functionField) :
    denominatorModule X f ⟶ CommonFractionalIdeal.regularModule X :=
  Hom.idealInclusion _

instance denominatorInclusionMono {ι : Type u} (f : ι → X.functionField) :
    Mono (denominatorInclusion X f) := by
  dsimp only [denominatorInclusion]
  infer_instance

/-- The actual relation module is canonically the actual ideal module. -/
def denominatorIso {ι : Type u} [Finite ι] (f : ι → X.functionField) :
    relationModule X f ≅ denominatorModule X f := by
  let h := Hom.imageIdealLocalizes_of_isQuasicoherent (relationInclusion X f)
  have := Hom.zeroIdealFactor_isIso (relationInclusion X f) h
  exact asIso (Hom.zeroIdealFactor (relationInclusion X f) h)

@[reassoc (attr := simp)]
theorem denominatorIso_hom_inclusion {ι : Type u} [Finite ι] (f : ι → X.functionField) :
    (denominatorIso X f).hom ≫ denominatorInclusion X f = relationInclusion X f :=
  Hom.zeroIdealFactor_inclusion (relationInclusion X f)
    (Hom.imageIdealLocalizes_of_isQuasicoherent (relationInclusion X f))

@[reassoc (attr := simp)]
theorem denominatorIso_inv_relationInclusion {ι : Type u} [Finite ι]
    (f : ι → X.functionField) :
    (denominatorIso X f).inv ≫ relationInclusion X f = denominatorInclusion X f := by
  rw [← denominatorIso_hom_inclusion X f, Iso.inv_hom_id_assoc]

instance denominatorModuleQuasicoherent {ι : Type u} [Finite ι]
    (f : ι → X.functionField) : (denominatorModule X f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (denominatorIso X f) inferInstance

/-- The coordinate numerator on the actual denominator ideal module. -/
def numeratorMap {ι : Type u} [Finite ι] (f : ι → X.functionField) (i : ι) :
    denominatorModule X f ⟶ CommonFractionalIdeal.regularModule X :=
  (denominatorIso X f).inv ≫ relationNumerator X f i

theorem numeratorMap_value {ι : Type u} [Finite ι] (f : ι → X.functionField) (i : ι)
    (U : X.Opens) [Nonempty U] (s : (denominatorModule X f).val.obj (op U)) :
    X.germToFunctionField U ((numeratorMap X f i).val.app (op U) s) =
      X.germToFunctionField U ((denominatorInclusion X f).val.app (op U) s) * f i := by
  have hd := congrArg (fun g ↦ g.val.app (op U) s)
    (denominatorIso_inv_relationInclusion X f)
  change (relationInclusion X f).val.app (op U)
    ((denominatorIso X f).inv.val.app (op U) s) = _ at hd
  change X.germToFunctionField U ((relationNumerator X f i).val.app (op U)
    ((denominatorIso X f).inv.val.app (op U) s)) = _
  rw [← hd]
  exact relationNumerator_value X f i U _

/-- The original finite numerator row. -/
def totalNumerator {ι : Type u} [Fintype ι] (f : ι → X.functionField) :
    (⨁ fun _ : ι ↦ denominatorModule X f) ⟶ CommonFractionalIdeal.regularModule X :=
  Limits.biproduct.desc (fun i ↦ numeratorMap X f i)

instance numeratorSourceQuasicoherent {ι : Type u} [Finite ι]
    (f : ι → X.functionField) :
    (⨁ fun _ : ι ↦ denominatorModule X f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit
    (Limits.biproduct.isLimit (fun _ : ι ↦ denominatorModule X f))
      (by
        intro i
        change (denominatorModule X f).IsQuasicoherent
        infer_instance)

/-- The genuine normalized base ideal generated by the original numerator row. -/
def baseIdeal {ι : Type u} [Fintype ι] (f : ι → X.functionField) : X.IdealSheafData :=
  Hom.imageIdealData (totalNumerator X f)

/-- The actual module of the normalized base ideal. -/
def baseModule {ι : Type u} [Fintype ι] (f : ι → X.functionField) : X.Modules :=
  Hom.idealModule (Hom.zeroInclusion (totalNumerator X f))

/-- The original embedded base-ideal inclusion. -/
def baseInclusion {ι : Type u} [Fintype ι] (f : ι → X.functionField) :
    baseModule X f ⟶ CommonFractionalIdeal.regularModule X := Hom.idealInclusion _

instance baseInclusionMono {ι : Type u} [Fintype ι] (f : ι → X.functionField) :
    Mono (baseInclusion X f) := by
  dsimp only [baseInclusion]
  infer_instance

/-- The original coordinate, factored into the actual normalized base ideal. -/
def coordinateMap {ι : Type u} [Fintype ι] (f : ι → X.functionField) (i : ι) :
    denominatorModule X f ⟶ baseModule X f := by
  have : (⨁ fun _ : ι ↦ denominatorModule X f).IsQuasicoherent :=
    numeratorSourceQuasicoherent X f
  exact Limits.biproduct.ι (fun _ : ι ↦ denominatorModule X f) i ≫
    Hom.zeroIdealFactor (totalNumerator X f)
      (Hom.imageIdealLocalizes_of_isQuasicoherent (totalNumerator X f))

@[reassoc (attr := simp)]
theorem coordinateMap_inclusion {ι : Type u} [Fintype ι] (f : ι → X.functionField) (i : ι) :
    coordinateMap X f i ≫ baseInclusion X f = numeratorMap X f i := by
  simp only [coordinateMap, baseInclusion, Category.assoc, Hom.zeroIdealFactor_inclusion,
    totalNumerator, Limits.biproduct.ι_desc]

theorem coordinateMap_value {ι : Type u} [Fintype ι] (f : ι → X.functionField) (i : ι)
    (U : X.Opens) [Nonempty U] (s : (denominatorModule X f).val.obj (op U)) :
    X.germToFunctionField U ((baseInclusion X f).val.app (op U)
      ((coordinateMap X f i).val.app (op U) s)) =
        X.germToFunctionField U ((denominatorInclusion X f).val.app (op U) s) * f i := by
  have h := congrArg (fun g ↦ g.val.app (op U) s) (coordinateMap_inclusion X f i)
  change (baseInclusion X f).val.app (op U) ((coordinateMap X f i).val.app (op U) s) = _ at h
  rw [h]
  exact numeratorMap_value X f i U s

omit [IsIntegral X] in
private theorem idealModule_quasicoherent_of_affine {Y : Scheme.{u}}
    (g : Y ⟶ X) [IsAffineHom g] : (Hom.idealModule g).IsQuasicoherent := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation := unit_finitePresentation X
  have : (SheafOfModules.unit Y.ringCatSheaf).IsFinitePresentation := unit_finitePresentation Y
  have : ((pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom g _
  exact QuasiCoherent.quasicoherent_kernel (Hom.structureModuleMap g)

instance baseModuleQuasicoherent {ι : Type u} [Fintype ι] (f : ι → X.functionField) :
    (baseModule X f).IsQuasicoherent :=
  idealModule_quasicoherent_of_affine X (Hom.zeroInclusion (totalNumerator X f))

theorem denominatorModule_coherent [IsNoetherian X] {ι : Type u} [Finite ι]
    (f : ι → X.functionField) : affineLocallyFiniteType X (denominatorModule X f) := by
  have hO : (CommonFractionalIdeal.regularModule X).IsFinitePresentation :=
    unit_finitePresentation X
  exact Coherent.affineLocallyFiniteType_of_quasicoherent_mono (denominatorInclusion X f)
    ((Coherent.affineLocallyFiniteType_iff_finitePresentation _).mpr hO)

theorem baseModule_coherent [IsNoetherian X] {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) : affineLocallyFiniteType X (baseModule X f) := by
  have hO : (CommonFractionalIdeal.regularModule X).IsFinitePresentation :=
    unit_finitePresentation X
  exact Coherent.affineLocallyFiniteType_of_quasicoherent_mono (baseInclusion X f)
    ((Coherent.affineLocallyFiniteType_iff_finitePresentation _).mpr hO)


private theorem section_product_exists {Y : Scheme.{u}} {ι : Type u}
    (M : ι → Y.Modules) (U : Y.Opens) (s : ∀ i, (M i).val.obj (op U)) :
    ∃ t : (∏ᶜ M).val.obj (op U),
      ∀ i, (Limits.Pi.π M i).val.app (op U) t = s i := by
  let ev : Y.Modules ⥤ ModuleCat Γ(Y, U) := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  have : PreservesLimits ev := inferInstanceAs
    (PreservesLimits (SheafOfModules.evaluation Y.ringCatSheaf (op U)))
  let c : Cone (Discrete.functor M ⋙ ev) := {
    pt := ModuleCat.of Γ(Y, U) Γ(Y, U)
    π := Discrete.natTrans (fun i ↦ ModuleCat.ofHom
      (LinearMap.toSpanSingleton Γ(Y, U) _ (s i.as))) }
  let l := (isLimitOfPreserves ev (productIsProduct M)).lift c
  let t : (∏ᶜ M).val.obj (op U) := l (1 : Γ(Y, U))
  refine ⟨t, ?_⟩
  intro i
  have h := (isLimitOfPreserves ev (productIsProduct M)).fac c ⟨i⟩
  change (l ≫ ev.map (Limits.Pi.π M i)) (1 : Γ(Y, U)) = s i
  exact (congrArg (fun g ↦ g.hom (1 : Γ(Y, U))) h).trans (one_smul _ _)

private theorem section_product_ext {Y : Scheme.{u}} {ι : Type u}
    (M : ι → Y.Modules) (U : Y.Opens)
    (s t : (∏ᶜ M).val.obj (op U))
    (h : ∀ i, (Limits.Pi.π M i).val.app (op U) s =
      (Limits.Pi.π M i).val.app (op U) t) : s = t := by
  let ev : Y.Modules ⥤ ModuleCat Γ(Y, U) := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  have : PreservesLimits ev := inferInstanceAs
    (PreservesLimits (SheafOfModules.evaluation Y.ringCatSheaf (op U)))
  let a : ModuleCat.of Γ(Y, U) Γ(Y, U) ⟶ ev.obj (∏ᶜ M) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton Γ(Y, U) _ s)
  let b : ModuleCat.of Γ(Y, U) Γ(Y, U) ⟶ ev.obj (∏ᶜ M) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton Γ(Y, U) _ t)
  have hab : a = b := by
    apply (isLimitOfPreserves ev (productIsProduct M)).hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (Limits.Pi.π M i.as).val.app (op U) (r • s) =
      (Limits.Pi.π M i.as).val.app (op U) (r • t)
    rw [((Limits.Pi.π M i.as).val.app (op U)).hom.map_smul,
      ((Limits.Pi.π M i.as).val.app (op U)).hom.map_smul, h i.as]
  have hv := congrArg (fun g ↦ g (1 : Γ(Y, U))) hab
  change (1 : Γ(Y, U)) • s = (1 : Γ(Y, U)) • t at hv
  simpa only [one_smul] using hv

private theorem section_pullback_exists {Y : Scheme.{u}} {M N P : Y.Modules}
    (a : M ⟶ P) (b : N ⟶ P) (U : Y.Opens)
    (s : M.val.obj (op U)) (t : N.val.obj (op U))
    (h : a.val.app (op U) s = b.val.app (op U) t) :
    ∃ z : (Limits.pullback a b).val.obj (op U),
      (Limits.pullback.fst a b).val.app (op U) z = s ∧
      (Limits.pullback.snd a b).val.app (op U) z = t := by
  let ev : Y.Modules ⥤ ModuleCat Γ(Y, U) := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  have : PreservesLimits ev := inferInstanceAs
    (PreservesLimits (SheafOfModules.evaluation Y.ringCatSheaf (op U)))
  let e := PreservesPullback.iso ev a b
  let h₁ : ModuleCat.of Γ(Y, U) Γ(Y, U) ⟶ ev.obj M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton Γ(Y, U) _ s)
  let h₂ : ModuleCat.of Γ(Y, U) Γ(Y, U) ⟶ ev.obj N :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton Γ(Y, U) _ t)
  have hc : h₁ ≫ ev.map a = h₂ ≫ ev.map b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change a.val.app (op U) (r • s) = b.val.app (op U) (r • t)
    rw [(a.val.app (op U)).hom.map_smul, (b.val.app (op U)).hom.map_smul, h]
  let l := Limits.pullback.lift h₁ h₂ hc
  let z : (Limits.pullback a b).val.obj (op U) := (l ≫ e.inv) (1 : Γ(Y, U))
  refine ⟨z, ?_, ?_⟩
  · change (l ≫ e.inv ≫ ev.map (Limits.pullback.fst a b)) (1 : Γ(Y, U)) = s
    have hh : l ≫ e.inv ≫ ev.map (Limits.pullback.fst a b) = h₁ := by
      dsimp only [e]
      rw [PreservesPullback.iso_inv_fst, Limits.pullback.lift_fst]
    exact (congrArg (fun g ↦ g.hom (1 : Γ(Y, U))) hh).trans (one_smul _ _)
  · change (l ≫ e.inv ≫ ev.map (Limits.pullback.snd a b)) (1 : Γ(Y, U)) = t
    have hh : l ≫ e.inv ≫ ev.map (Limits.pullback.snd a b) = h₂ := by
      dsimp only [e]
      rw [PreservesPullback.iso_inv_snd, Limits.pullback.lift_snd]
    exact (congrArg (fun g ↦ g.hom (1 : Γ(Y, U))) hh).trans (one_smul _ _)

@[reassoc]
private theorem regularTupleMap_π (ι : Type u) (i : ι) :
    regularTupleMap X ι ≫ Limits.Pi.π (fun _ : ι ↦ CommonFractionalIdeal.rationalFunctions X) i =
      Limits.Pi.π (fun _ : ι ↦ CommonFractionalIdeal.regularModule X) i ≫
        CommonFractionalIdeal.regularMap X := Limits.Pi.map_π _ _

@[reassoc]
private theorem coordinateRow_π {ι : Type u} (f : ι → X.functionField) (i : ι) :
    coordinateRow X f ≫ Limits.Pi.π (fun _ : ι ↦ CommonFractionalIdeal.rationalFunctions X) i =
      CommonFractionalIdeal.regularMap X ≫ multiplier X (f i) := Limits.Pi.lift_comp_π _ _

/-- On each nonempty actual affine open, the native denominator ideal is
exactly the colon denominator of the original fractional coordinate span. -/
theorem denominatorIdeal_ideal {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (U : X.affineOpens) [Nonempty U.1] :
    letI := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    (denominatorIdeal X f).ideal U = FractionalIdeal.denominatorIdeal
      (FractionalIdeal.spanFinset Γ(X, U) Finset.univ f) := by
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  rw [denominatorIdeal, Hom.imageIdealData_eq (relationInclusion X f)
    (Hom.imageIdealLocalizes_of_isQuasicoherent (relationInclusion X f))]
  ext a
  rw [FractionalIdeal.mem_denominatorIdeal_spanFinset]
  constructor
  · rintro ⟨s, rfl⟩ i _
    apply (FractionalIdeal.mem_one_iff (nonZeroDivisors Γ(X, U))).mpr
    exact ⟨(relationNumerator X f i).val.app (op U.1) s,
      relationNumerator_value X f i U.1 s⟩
  · intro ha
    choose b hb using fun i : ι ↦
      (FractionalIdeal.mem_one_iff (nonZeroDivisors Γ(X, U))).mp (ha i (Finset.mem_univ i))
    obtain ⟨t, ht⟩ := section_product_exists
      (fun _ : ι ↦ CommonFractionalIdeal.regularModule X) U.1 b
    have hc : (regularTupleMap X ι).val.app (op U.1) t =
        (coordinateRow X f).val.app (op U.1) a := by
      apply section_product_ext (fun _ : ι ↦ CommonFractionalIdeal.rationalFunctions X) U.1
      intro i
      have hr := congrArg (fun g ↦ g.val.app (op U.1) t) (regularTupleMap_π X ι i)
      have hf := congrArg (fun g ↦ g.val.app (op U.1) a) (coordinateRow_π X f i)
      change (Limits.Pi.π (fun _ : ι ↦ CommonFractionalIdeal.rationalFunctions X) i).val.app
        (op U.1) ((regularTupleMap X ι).val.app (op U.1) t) =
          (CommonFractionalIdeal.regularMap X).val.app (op U.1)
            ((Limits.Pi.π (fun _ : ι ↦ CommonFractionalIdeal.regularModule X) i).val.app
              (op U.1) t) at hr
      change (Limits.Pi.π (fun _ : ι ↦ CommonFractionalIdeal.rationalFunctions X) i).val.app
        (op U.1) ((coordinateRow X f).val.app (op U.1) a) =
          (multiplier X (f i)).val.app (op U.1)
            ((CommonFractionalIdeal.regularMap X).val.app (op U.1) a) at hf
      rw [hr, hf, ht]
      apply (CommonFractionalIdeal.rationalValueEquiv X U.1).injective
      calc
        _ = X.germToFunctionField U.1 (b i) :=
          CommonFractionalIdeal.regularMap_value X U.1 _
        _ = X.germToFunctionField U.1 a * f i := hb i
        _ = f i * X.germToFunctionField U.1 a := mul_comm _ _
        _ = f i * CommonFractionalIdeal.rationalValue X U.1
            ((CommonFractionalIdeal.regularMap X).val.app (op U.1) a) :=
          congrArg (fun z ↦ f i * z)
            (CommonFractionalIdeal.regularMap_value X U.1 a).symm
        _ = _ := (multiplier_value X (f i) U.1 _).symm
    obtain ⟨z, _, hz⟩ := section_pullback_exists
      (regularTupleMap X ι) (coordinateRow X f) U.1 t a hc
    exact ⟨z, hz⟩

-- On an empty affine open the ideal is the unique zero-ring ideal;
-- no fractional-field algebra is installed.
omit [IsIntegral X] in
private theorem ideal_eq_top_of_isEmpty (I : X.IdealSheafData) (U : X.affineOpens)
    [hU : IsEmpty U.1] : I.ideal U = ⊤ := by
  have hbot : U.1 = ⊥ := by
    ext x
    constructor
    · intro hx
      exact hU.false ⟨x, hx⟩
    · simp
  have : Subsingleton Γ(X, U) := by rw [hbot]; infer_instance
  apply (Ideal.eq_top_iff_one (I.ideal U)).mpr
  rw [show (1 : Γ(X, U)) = 0 from Subsingleton.elim _ _]
  exact (I.ideal U).zero_mem

theorem denominatorIdeal_ideal_of_isEmpty {ι : Type u}
    (f : ι → X.functionField) (U : X.affineOpens) [IsEmpty U.1] :
    (denominatorIdeal X f).ideal U = ⊤ := ideal_eq_top_of_isEmpty X _ _

theorem baseIdeal_ideal_of_isEmpty {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (U : X.affineOpens) [IsEmpty U.1] :
    (baseIdeal X f).ideal U = ⊤ := ideal_eq_top_of_isEmpty X _ _

omit [IsIntegral X] in
private theorem zeroIdealFactor_affine_surjective {M : X.Modules}
    (φ : M ⟶ CommonFractionalIdeal.regularModule X)
    (h : Hom.ImageIdealLocalizes φ) (U : X.affineOpens) :
    Function.Surjective ((Hom.zeroIdealFactor φ h).val.app (op U.1)) := by
  intro a
  have ha := (Hom.idealSectionsEquiv (Hom.zeroInclusion φ) U.1 a).property
  have ha' : ((Hom.idealSectionsEquiv (Hom.zeroInclusion φ) U.1 a) : Γ(X, U)) ∈
      Hom.sectionImageIdeal φ U.1 :=
    (congrArg (fun I : Ideal Γ(X, U) ↦
      ((Hom.idealSectionsEquiv (Hom.zeroInclusion φ) U.1 a) : Γ(X, U)) ∈ I)
        (Hom.zeroInclusion_kernel φ h U)).mp ha
  obtain ⟨m, hm⟩ := ha'
  refine ⟨m, ?_⟩
  apply (Hom.idealSectionsEquiv (Hom.zeroInclusion φ) U.1).injective
  apply Subtype.ext
  rw [Hom.idealSectionsEquiv_val, Hom.idealSectionsEquiv_val]
  have hf := congrArg (fun ψ : M ⟶ CommonFractionalIdeal.regularModule X ↦
    ψ.val.app (op U.1) m) (Hom.zeroIdealFactor_inclusion φ h)
  exact hf.trans (hm.trans (Hom.idealSectionsEquiv_val (Hom.zeroInclusion φ) U.1 a))

omit [IsIntegral X] in
private theorem epi_of_surjective_on_affine {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.affineOpens, Function.Surjective (φ.val.app (op U.1))) : Epi φ := by
  constructor
  intro T g k hcomp
  apply moduleHom_ext_affine
  intro U
  ext a
  obtain ⟨m, rfl⟩ := h U a
  have h := congrArg (fun f ↦ f.val.app (op U.1) m) hcomp
  exact h

/-- The actual numerator row generates the actual normalized base ideal. -/
def generatingRow {ι : Type u} [Fintype ι] (f : ι → X.functionField) :
    (⨁ fun _ : ι ↦ denominatorModule X f) ⟶ baseModule X f := by
  have : (⨁ fun _ : ι ↦ denominatorModule X f).IsQuasicoherent :=
    numeratorSourceQuasicoherent X f
  exact Hom.zeroIdealFactor (totalNumerator X f)
    (Hom.imageIdealLocalizes_of_isQuasicoherent (totalNumerator X f))

instance generatingRowEpi {ι : Type u} [Fintype ι] (f : ι → X.functionField) :
    Epi (generatingRow X f) := by
  apply epi_of_surjective_on_affine
  intro U
  exact zeroIdealFactor_affine_surjective X (totalNumerator X f)
    (Hom.imageIdealLocalizes_of_isQuasicoherent (totalNumerator X f)) U

@[reassoc]
theorem coordinateMap_eq_ι_generatingRow {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (i : ι) :
    coordinateMap X f i = Limits.biproduct.ι (fun _ : ι ↦ denominatorModule X f) i ≫
      generatingRow X f := rfl

/-- The specified original coordinate one is the original ideal inclusion. -/
theorem numeratorMap_eq_inclusion_of_one {ι : Type u} [Finite ι]
    (f : ι → X.functionField) (i₀ : ι) (hi₀ : f i₀ = 1) :
    numeratorMap X f i₀ = denominatorInclusion X f := by
  apply moduleHom_ext_affine
  intro U
  ext s
  change (show Γ(X, U) from (numeratorMap X f i₀).val.app (op U.1) s) =
    (show Γ(X, U) from (denominatorInclusion X f).val.app (op U.1) s)
  by_cases hU : Nonempty U.1
  · let := hU
    apply X.germToFunctionField_injective U.1
    exact (numeratorMap_value X f i₀ U.1 s).trans (by rw [hi₀, mul_one])
  · have hbot : U.1 = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hU ⟨⟨x, hx⟩⟩).elim
      · simp
    have : Subsingleton Γ(X, U) := by rw [hbot]; infer_instance
    exact Subsingleton.elim _ _

@[reassoc]
theorem coordinateMap_one_inclusion {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (i₀ : ι) (hi₀ : f i₀ = 1) :
    coordinateMap X f i₀ ≫ baseInclusion X f = denominatorInclusion X f :=
  (coordinateMap_inclusion X f i₀).trans (numeratorMap_eq_inclusion_of_one X f i₀ hi₀)

/-- The original finite family generates the actual base ideal through the
native coproduct row, with unchanged coordinates and index set. -/
instance coordinateFamilyEpi {ι : Type u} [Fintype ι] (f : ι → X.functionField) :
    Epi (Limits.Sigma.desc (coordinateMap X f)) := by
  constructor
  intro T g k hcomp
  apply (cancel_epi (generatingRow X f)).mp
  apply Limits.biproduct.hom_ext'
  intro i
  have hi := congrArg
    (fun a ↦ Limits.Sigma.ι (fun _ : ι ↦ denominatorModule X f) i ≫ a) hcomp
  have hι : Limits.Sigma.ι (fun _ : ι ↦ denominatorModule X f) i ≫
      Limits.Sigma.desc (coordinateMap X f) = coordinateMap X f i :=
    Limits.Sigma.ι_comp_desc _ _
  have hi' : coordinateMap X f i ≫ g = coordinateMap X f i ≫ k := by
    calc
      _ = Limits.Sigma.ι (fun _ : ι ↦ denominatorModule X f) i ≫
          (Limits.Sigma.desc (coordinateMap X f) ≫ g) := by
        rw [← Category.assoc, hι]
      _ = _ := hi
      _ = _ := by rw [← Category.assoc, hι]
  calc
    _ = coordinateMap X f i ≫ g := by
      rw [← Category.assoc, ← coordinateMap_eq_ι_generatingRow]
    _ = _ := hi'
    _ = _ := by rw [← Category.assoc, ← coordinateMap_eq_ι_generatingRow]


/-- The original numerator equation is an equality of actual module maps into
the original generic pushforward, before choosing a local section or frame. -/
@[reassoc]
theorem numeratorMap_regularMap {ι : Type u} [Finite ι]
    (f : ι → X.functionField) (i : ι) :
    numeratorMap X f i ≫ CommonFractionalIdeal.regularMap X =
      denominatorInclusion X f ≫ CommonFractionalIdeal.regularMap X ≫
        multiplier X (f i) := by
  calc
    _ = (denominatorIso X f).inv ≫
        (relationNumerator X f i ≫ CommonFractionalIdeal.regularMap X) :=
      Category.assoc _ _ _
    _ = (denominatorIso X f).inv ≫
        (relationInclusion X f ≫ CommonFractionalIdeal.regularMap X ≫
          multiplier X (f i)) := by rw [relationNumerator_regularMap]
    _ = ((denominatorIso X f).inv ≫ relationInclusion X f) ≫
        CommonFractionalIdeal.regularMap X ≫ multiplier X (f i) := by
      rw [Category.assoc]
    _ = _ := by rw [denominatorIso_inv_relationInclusion]

/-- Each original coordinate has the specified scalar in the same original
function field through its actual denominator and base-ideal embeddings. -/
@[reassoc]
theorem coordinateMap_regularMap {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (i : ι) :
    coordinateMap X f i ≫ baseInclusion X f ≫ CommonFractionalIdeal.regularMap X =
      denominatorInclusion X f ≫ CommonFractionalIdeal.regularMap X ≫
        multiplier X (f i) := by
  rw [← Category.assoc, coordinateMap_inclusion, numeratorMap_regularMap]

/-- The same numerator identity on the actual stalk of the original
kernel module uses the canonical original stalk-to-function-field map. -/
theorem numeratorMap_stalk_value {ι : Type u} [Finite ι]
    (f : ι → X.functionField) (i : ι) (x : X)
    (m : (denominatorModule X f).presheaf.stalk x) :
    algebraMap (X.presheaf.stalk x) X.functionField
      (CommonFractionalIdeal.regularStalkEquiv X x
        (Scheme.Modules.moduleStalkMap x (numeratorMap X f i) m)) =
      algebraMap (X.presheaf.stalk x) X.functionField
        (CommonFractionalIdeal.regularStalkEquiv X x
          (Scheme.Modules.moduleStalkMap x (denominatorInclusion X f) m)) * f i := by
  obtain ⟨U, hx, s, rfl⟩ := (denominatorModule X f).presheaf.exists_germ_eq m
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  change algebraMap (X.presheaf.stalk x) X.functionField
      (CommonFractionalIdeal.regularStalkValue X x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (numeratorMap X f i).mapPresheaf
            ((denominatorModule X f).presheaf.germ U x hx s))) =
    algebraMap (X.presheaf.stalk x) X.functionField
      (CommonFractionalIdeal.regularStalkValue X x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (denominatorInclusion X f).mapPresheaf
            ((denominatorModule X f).presheaf.germ U x hx s))) * f i
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply,
    CommonFractionalIdeal.regularStalkValue_germ,
    CommonFractionalIdeal.regularStalkValue_germ,
    Scheme.algebraMap_germ_eq_germToFunctionField,
    Scheme.algebraMap_germ_eq_germToFunctionField]
  exact numeratorMap_value X f i U s


/-- Actual ideal sections, with their original inclusion, identify with the
original affine fractional denominator ideal. -/
def denominatorSectionsEquiv {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (U : X.affineOpens) [Nonempty U.1] :
    letI := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    (denominatorModule X f).val.obj (op U.1) ≃ₗ[Γ(X, U)]
      FractionalIdeal.denominatorIdeal (FractionalIdeal.spanFinset Γ(X, U) Finset.univ f) := by
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  have hker : RingHom.ker ((Hom.zeroInclusion (relationInclusion X f)).app U.1).hom =
      FractionalIdeal.denominatorIdeal
        (FractionalIdeal.spanFinset Γ(X, U) Finset.univ f) :=
    (IdealSheafData.ker_subschemeι_app (denominatorIdeal X f) U).trans
      (denominatorIdeal_ideal X f U)
  exact (Hom.idealSectionsEquiv (Hom.zeroInclusion (relationInclusion X f)) U.1).trans
    (LinearEquiv.ofEq _ _ hker)

theorem denominatorSectionsEquiv_val {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (U : X.affineOpens) [Nonempty U.1]
    (s : (denominatorModule X f).val.obj (op U.1)) :
    ((denominatorSectionsEquiv X f U s) : Γ(X, U)) =
      (denominatorInclusion X f).val.app (op U.1) s := by
  dsimp only [denominatorSectionsEquiv, LinearEquiv.trans_apply]
  rw [LinearEquiv.coe_ofEq_apply]
  exact Hom.idealSectionsEquiv_val (Hom.zeroInclusion (relationInclusion X f)) U.1 s

private theorem spanFinsetNumerator_value
    {R K : Type u} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {ι : Type u}
    (s : Finset ι) (f : ι → K) (i : s)
    (d : FractionalIdeal.denominatorIdeal (FractionalIdeal.spanFinset R s f)) :
    algebraMap R K (FractionalIdeal.spanFinsetNumeratorLinearMap s f i d) =
      algebraMap R K d * f i :=
  FractionalIdeal.map_numeratorLinearMap _
    ⟨f i, (FractionalIdeal.mem_coe (I := FractionalIdeal.spanFinset R s f)).mp
      (Submodule.subset_span ⟨i.val, i.property, rfl⟩)⟩ d

/-- The affine numerator is the canonical root numerator through the original
coefficient map into the same function field. -/
theorem numeratorMap_affine {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (U : X.affineOpens) [Nonempty U.1] (i : ι)
    (s : (denominatorModule X f).val.obj (op U.1)) :
    letI := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    (show Γ(X, U) from (numeratorMap X f i).val.app (op U.1) s) =
      FractionalIdeal.spanFinsetNumeratorLinearMap (R := Γ(X, U)) Finset.univ f
        ⟨i, Finset.mem_univ i⟩ (denominatorSectionsEquiv X f U s) := by
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  apply X.germToFunctionField_injective U.1
  calc
    _ = X.germToFunctionField U.1
        ((denominatorInclusion X f).val.app (op U.1) s) * f i :=
      numeratorMap_value X f i U.1 s
    _ = X.germToFunctionField U.1
        ((denominatorSectionsEquiv X f U s) : Γ(X, U)) * f i := by
      rw [denominatorSectionsEquiv_val]
    _ = _ := (spanFinsetNumerator_value Finset.univ f
      ⟨i, Finset.mem_univ i⟩ (denominatorSectionsEquiv X f U s)).symm

private def numeratorSectionLinear {ι : Type u} [Finite ι]
    (f : ι → X.functionField) (U : X.Opens) (i : ι) :
    (denominatorModule X f).val.obj (op U) →ₗ[Γ(X, U)] Γ(X, U) :=
  ((numeratorMap X f i).val.app (op U)).hom

private def totalNumeratorSectionLinear {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (U : X.Opens) :
    (⨁ fun _ : ι ↦ denominatorModule X f).val.obj (op U) →ₗ[Γ(X, U)] Γ(X, U) :=
  ((totalNumerator X f).val.app (op U)).hom

private theorem numeratorMap_affine_range {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (U : X.affineOpens) [Nonempty U.1] (i : ι) :
    letI := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    (numeratorSectionLinear X f U.1 i).range =
      (FractionalIdeal.spanFinsetNumeratorLinearMap (R := Γ(X, U)) Finset.univ f
        ⟨i, Finset.mem_univ i⟩).range := by
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  ext r
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨denominatorSectionsEquiv X f U s, (numeratorMap_affine X f U i s).symm⟩
  · rintro ⟨d, rfl⟩
    obtain ⟨s, hs⟩ := (denominatorSectionsEquiv X f U).surjective d
    exact ⟨s, (numeratorMap_affine X f U i s).trans
      (congrArg (FractionalIdeal.spanFinsetNumeratorLinearMap (R := Γ(X, U)) Finset.univ f
        ⟨i, Finset.mem_univ i⟩) hs)⟩

private theorem totalNumerator_apply {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (U : X.Opens)
    (s : (⨁ fun _ : ι ↦ denominatorModule X f).val.obj (op U)) :
    totalNumeratorSectionLinear X f U s =
      ∑ i, numeratorSectionLinear X f U i
        ((Limits.biproduct.π (fun _ : ι ↦ denominatorModule X f) i).val.app (op U) s) := by
  let ev : X.Modules ⥤ ModuleCat Γ(X, U) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  have : ev.Additive := by
    constructor
    intro M N a b
    rfl
  have ht : ∑ i, Limits.biproduct.π (fun _ : ι ↦ denominatorModule X f) i ≫
      Limits.biproduct.ι (fun _ : ι ↦ denominatorModule X f) i =
        𝟙 (⨁ fun _ : ι ↦ denominatorModule X f) :=
    Limits.IsBilimit.total (Limits.biproduct.isBilimit _)
  have hdesc : totalNumerator X f =
      ∑ i, Limits.biproduct.π (fun _ : ι ↦ denominatorModule X f) i ≫
        numeratorMap X f i := by
    calc
      _ = (∑ i, Limits.biproduct.π (fun _ : ι ↦ denominatorModule X f) i ≫
          Limits.biproduct.ι (fun _ : ι ↦ denominatorModule X f) i) ≫
            totalNumerator X f := by rw [ht, Category.id_comp]
      _ = _ := by
        simp only [Preadditive.sum_comp, Category.assoc, totalNumerator,
          Limits.biproduct.ι_desc]
  have h : ev.map (totalNumerator X f) =
      ∑ i, ev.map (Limits.biproduct.π (fun _ : ι ↦ denominatorModule X f) i ≫
        numeratorMap X f i) := by
    rw [hdesc, ev.map_sum]
  have hv := congrArg (fun g ↦ g.hom s) h
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, Functor.map_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply] at hv
  exact hv

private theorem baseIdeal_ideal_eq_iSup_range {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (U : X.affineOpens) :
    (baseIdeal X f).ideal U =
      ⨆ i : ι, (numeratorSectionLinear X f U.1 i).range := by
  have : (⨁ fun _ : ι ↦ denominatorModule X f).IsQuasicoherent :=
    numeratorSourceQuasicoherent X f
  rw [baseIdeal, Hom.imageIdealData_eq (totalNumerator X f)
    (Hom.imageIdealLocalizes_of_isQuasicoherent (totalNumerator X f))]
  apply le_antisymm
  · rintro r ⟨s, rfl⟩
    change totalNumeratorSectionLinear X f U.1 s ∈ _
    rw [totalNumerator_apply]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup (fun i : ι ↦
      (numeratorSectionLinear X f U.1 i).range) i)
        ⟨(Limits.biproduct.π (fun _ : ι ↦ denominatorModule X f) i).val.app (op U.1) s, rfl⟩
  · apply iSup_le
    intro i r hr
    obtain ⟨s, rfl⟩ := hr
    refine ⟨(Limits.biproduct.ι (fun _ : ι ↦ denominatorModule X f) i).val.app (op U.1) s, ?_⟩
    exact congrArg (fun g ↦ g.val.app (op U.1) s)
      (Limits.biproduct.ι_desc (fun i ↦ numeratorMap X f i) i)

/-- The actual normalized base ideal on every nonempty affine open is the
intrinsic integral product of the original denominator and coordinate span. -/
theorem baseIdeal_ideal {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (U : X.affineOpens) [Nonempty U.1] :
    letI := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    (baseIdeal X f).ideal U = FractionalIdeal.denominatorProductIdeal
      (FractionalIdeal.spanFinset Γ(X, U) Finset.univ f) := by
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  rw [baseIdeal_ideal_eq_iSup_range,
    FractionalIdeal.denominatorProductIdeal_spanFinset_eq_iSup_range]
  apply le_antisymm
  · apply iSup_le
    intro i
    exact (numeratorMap_affine_range X f U i).le.trans
      (le_iSup (fun j : (Finset.univ : Finset ι) ↦
        (FractionalIdeal.spanFinsetNumeratorLinearMap
          (R := Γ(X, U)) Finset.univ f j).range)
          ⟨i, Finset.mem_univ i⟩)
  · apply iSup_le
    intro i
    exact (numeratorMap_affine_range X f U i.val).ge.trans
      (le_iSup (fun j : ι ↦
        (numeratorSectionLinear X f U.1 j).range) i.val)


private theorem denominatorIdeal_spanFinset_eq_colon
    {R K : Type u} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {ι : Type u}
    (s : Finset ι) (f : ι → K) (d : R) (hd : d ≠ 0) (a : ι → R)
    (ha : ∀ i ∈ s, algebraMap R K (a i) = algebraMap R K d * f i) :
    FractionalIdeal.denominatorIdeal (FractionalIdeal.spanFinset R s f) =
      (Ideal.span {d}).colon (Ideal.span (a '' (s : Set ι)) : Set R) := by
  ext r
  rw [FractionalIdeal.mem_denominatorIdeal_spanFinset_iff_dvd s f d hd a ha,
    Ideal.colon_span, Submodule.mem_colon]
  constructor
  · rintro h _ ⟨i, hi, rfl⟩
    exact Ideal.mem_span_singleton.mpr (h i hi)
  · intro h i hi
    exact Ideal.mem_span_singleton.mp (h (a i) ⟨i, hi, rfl⟩)

private theorem map_denominatorIdeal_spanFinset
    {R S K : Type u} [CommRing R] [IsDomain R] [CommRing S]
    [Field K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K] (M : Submonoid R) [IsLocalization M S]
    {ι : Type u} (s : Finset ι) (f : ι → K) :
    (FractionalIdeal.denominatorIdeal (FractionalIdeal.spanFinset R s f)).map
        (algebraMap R S) =
      FractionalIdeal.denominatorIdeal (FractionalIdeal.spanFinset S s f) := by
  classical
  let d : nonZeroDivisors R := IsLocalization.commonDenom R⁰ s f
  let a (i : ι) : R := if hi : i ∈ s then
    IsLocalization.integerMultiple R⁰ s f ⟨i, hi⟩ else 0
  have hd : (d : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have ha (i : ι) (hi : i ∈ s) :
      algebraMap R K (a i) = algebraMap R K (d : R) * f i := by
    dsimp only [a]
    rw [dite_eq_left hi]
    simpa only [d, Submonoid.smul_def, Algebra.smul_def] using
      IsLocalization.map_integerMultiple R⁰ s f ⟨i, hi⟩
  have hdS : algebraMap R S (d : R) ≠ 0 := by
    intro hzero
    apply hd
    apply IsFractionRing.injective R K
    simpa only [← IsScalarTower.algebraMap_apply R S K, map_zero] using
      congrArg (algebraMap S K) hzero
  have haS (i : ι) (hi : i ∈ s) :
      algebraMap S K (algebraMap R S (a i)) =
        algebraMap S K (algebraMap R S (d : R)) * f i := by
    simpa only [← IsScalarTower.algebraMap_apply R S K] using ha i hi
  have hfg : (Ideal.span (a '' (s : Set ι))).FG :=
    Submodule.fg_span (s.finite_toSet.image a)
  have hspan : (Ideal.span (a '' (s : Set ι))).map (algebraMap R S) =
      Ideal.span ((fun i ↦ algebraMap R S (a i)) '' (s : Set ι)) := by
    rw [Ideal.map_span, Set.image_image]
  calc
    _ = ((Ideal.span {(d : R)}).colon
        (Ideal.span (a '' (s : Set ι)) : Set R)).map (algebraMap R S) :=
      congrArg (Ideal.map (algebraMap R S))
        (denominatorIdeal_spanFinset_eq_colon s f (d : R) hd a ha)
    _ = ((Ideal.span {(d : R)}).map (algebraMap R S)).colon
        ((Ideal.span (a '' (s : Set ι))).map (algebraMap R S) : Set S) :=
      IsLocalization.map_colon_of_fg M S _ _ hfg
    _ = (Ideal.span {algebraMap R S (d : R)}).colon
        (Ideal.span ((fun i ↦ algebraMap R S (a i)) '' (s : Set ι)) : Set S) := by
      rw [Ideal.map_span, Set.image_singleton, hspan]
    _ = _ := (denominatorIdeal_spanFinset_eq_colon s f
      (algebraMap R S (d : R)) hdS (fun i ↦ algebraMap R S (a i)) haS).symm

private theorem map_spanFinsetNumerator_range
    {R S K : Type u} [CommRing R] [IsDomain R] [CommRing S]
    [Field K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K] (M : Submonoid R) [IsLocalization M S]
    {ι : Type u} (s : Finset ι) (f : ι → K) (i : s) :
    Ideal.map (algebraMap R S)
        (FractionalIdeal.spanFinsetNumeratorLinearMap (R := R) s f i).range =
      (FractionalIdeal.spanFinsetNumeratorLinearMap (R := S) s f i).range := by
  let DR := FractionalIdeal.denominatorIdeal (FractionalIdeal.spanFinset R s f)
  let DS := FractionalIdeal.denominatorIdeal (FractionalIdeal.spanFinset S s f)
  let nR := FractionalIdeal.spanFinsetNumeratorLinearMap (R := R) s f i
  let nS := FractionalIdeal.spanFinsetNumeratorLinearMap (R := S) s f i
  have hD : DR.map (algebraMap R S) = DS := map_denominatorIdeal_spanFinset M s f
  let eD : DR.map (algebraMap R S) ≃ₗ[R] DS :=
    (LinearEquiv.ofEq _ _ hD).restrictScalars R
  let l : DR →ₗ[R] DS := eD.toLinearMap.comp (Algebra.idealMap S DR)
  let : IsLocalizedModule M l :=
    IsLocalizedModule.of_linearEquiv M (Algebra.idealMap S DR) eD
  have hl (d : DR) : (l d : S) = algebraMap R S d := rfl
  apply Ideal.map_range_of_isLocalizedModule M l nR nS
  intro d
  apply IsFractionRing.injective S K
  calc
    _ = algebraMap S K (l d) * f i := spanFinsetNumerator_value s f i (l d)
    _ = algebraMap R K d * f i := by rw [hl, ← IsScalarTower.algebraMap_apply R S K]
    _ = algebraMap R K (nR d) := (spanFinsetNumerator_value s f i d).symm
    _ = _ := IsScalarTower.algebraMap_apply R S K _

private theorem map_denominatorProductIdeal_spanFinset
    {R S K : Type u} [CommRing R] [IsDomain R] [CommRing S]
    [Field K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K] (M : Submonoid R) [IsLocalization M S]
    {ι : Type u} (s : Finset ι) (f : ι → K) :
    (FractionalIdeal.denominatorProductIdeal (FractionalIdeal.spanFinset R s f)).map
        (algebraMap R S) =
      FractionalIdeal.denominatorProductIdeal (FractionalIdeal.spanFinset S s f) := by
  rw [FractionalIdeal.denominatorProductIdeal_spanFinset_eq_iSup_range,
    Ideal.map_iSup, FractionalIdeal.denominatorProductIdeal_spanFinset_eq_iSup_range]
  apply iSup_congr
  intro i
  exact map_spanFinsetNumerator_range M s f i

/-- The actual denominator stalk is the original denominator ideal over the
actual local ring, with the original canonical map to the same function field. -/
theorem denominatorIdeal_stalkIdeal {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (x : X) :
    (denominatorIdeal X f).stalkIdeal x = FractionalIdeal.denominatorIdeal
      (FractionalIdeal.spanFinset (X.presheaf.stalk x) Finset.univ f) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let R := Γ(X, U)
  let S := X.presheaf.stalk x
  let : Algebra R S := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : IsFractionRing R X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsScalarTower R S X.functionField := functionField_isScalarTower X U ⟨x, hx⟩
  let M := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : IsLocalization M S := hU.isLocalization_stalk ⟨x, hx⟩
  rw [IdealSheafData.stalkIdeal_eq_map _ ⟨U, hU⟩ x hx,
    denominatorIdeal_ideal X f ⟨U, hU⟩]
  exact map_denominatorIdeal_spanFinset M Finset.univ f

/-- The actual base-ideal stalk is the intrinsic normalized product over the
original local ring. Both affine-to-stalk maps are the original germs. -/
theorem baseIdeal_stalkIdeal {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (x : X) :
    (baseIdeal X f).stalkIdeal x = FractionalIdeal.denominatorProductIdeal
      (FractionalIdeal.spanFinset (X.presheaf.stalk x) Finset.univ f) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let R := Γ(X, U)
  let S := X.presheaf.stalk x
  let : Algebra R S := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : IsFractionRing R X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsScalarTower R S X.functionField := functionField_isScalarTower X U ⟨x, hx⟩
  let M := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : IsLocalization M S := hU.isLocalization_stalk ⟨x, hx⟩
  rw [IdealSheafData.stalkIdeal_eq_map _ ⟨U, hU⟩ x hx, baseIdeal_ideal X f ⟨U, hU⟩]
  exact map_denominatorProductIdeal_spanFinset M Finset.univ f


private theorem denominatorIdeal_spanFinset_ne_bot
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {ι : Type u}
    (s : Finset ι) (f : ι → K) :
    FractionalIdeal.denominatorIdeal (FractionalIdeal.spanFinset R s f) ≠ ⊥ := by
  let d : nonZeroDivisors R := IsLocalization.commonDenom R⁰ s f
  have hd : (d : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hm : (d : R) ∈
      FractionalIdeal.denominatorIdeal (FractionalIdeal.spanFinset R s f) := by
    rw [FractionalIdeal.mem_denominatorIdeal_spanFinset]
    intro i hi
    apply (FractionalIdeal.mem_one_iff R⁰).mpr
    refine ⟨IsLocalization.integerMultiple R⁰ s f ⟨i, hi⟩, ?_⟩
    simpa only [d, Submonoid.smul_def, Algebra.smul_def] using
      IsLocalization.map_integerMultiple R⁰ s f ⟨i, hi⟩
  intro hzero
  exact hd (by simpa only [hzero, Ideal.mem_bot] using hm)

private theorem one_mem_spanFinset_of_coordinate_one
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ι : Type u} [Fintype ι]
    (f : ι → K) (i₀ : ι) (hi₀ : f i₀ = 1) :
    (1 : K) ∈ FractionalIdeal.spanFinset R Finset.univ f := by
  rw [← hi₀]
  apply (FractionalIdeal.mem_coe (I := FractionalIdeal.spanFinset R Finset.univ f)).mp
  exact Submodule.subset_span ⟨i₀, Finset.mem_univ i₀, rfl⟩

/-- The actual denominator ideal has a nonzero ideal in every original stalk.
No regularity or global denominator section is assumed. -/
theorem denominatorIdeal_stalk_ne_bot {ι : Type u} [Finite ι]
    (f : ι → X.functionField) (x : X) : (denominatorIdeal X f).stalkIdeal x ≠ ⊥ := by
  let := Fintype.ofFinite ι
  rw [denominatorIdeal_stalkIdeal]
  exact denominatorIdeal_spanFinset_ne_bot Finset.univ f

/-- The canonical denominator ideal is nonzero as actual ideal-sheaf data. -/
theorem denominatorIdeal_ne_bot {ι : Type u} [Finite ι]
    (f : ι → X.functionField) : denominatorIdeal X f ≠ ⊥ := by
  intro hzero
  apply denominatorIdeal_stalk_ne_bot X f (genericPoint X)
  rw [hzero]
  simp only [IdealSheafData.stalkIdeal, IdealSheafData.ideal_bot, Pi.bot_apply,
    Ideal.map_bot, iSup_bot]

/-- The specified original coordinate one embeds the original denominator
ideal in the original normalized base ideal. -/
theorem denominatorIdeal_le_baseIdeal {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (i₀ : ι) (hi₀ : f i₀ = 1) :
    denominatorIdeal X f ≤ baseIdeal X f := by
  apply IdealSheafData.le_iff_stalkIdeal_le.mpr
  intro x
  rw [denominatorIdeal_stalkIdeal, baseIdeal_stalkIdeal]
  exact FractionalIdeal.denominatorIdeal_le_denominatorProductIdeal _
    (one_mem_spanFinset_of_coordinate_one f i₀ hi₀)

/-- In particular the actual normalized base ideal is nonzero. -/
theorem baseIdeal_ne_bot {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (i₀ : ι) (hi₀ : f i₀ = 1) :
    baseIdeal X f ≠ ⊥ := by
  intro hzero
  exact denominatorIdeal_ne_bot X f
    (bot_unique (hzero ▸ denominatorIdeal_le_baseIdeal X f i₀ hi₀))

/-- Actual regular local factoriality gives a nonzero generator for each
original denominator stalk, without an ambient dimension bound. -/
theorem denominatorIdeal_stalk_exists_generator (hX : RegularStalks X)
    {ι : Type u} [Finite ι] (f : ι → X.functionField)
    (i₀ : ι) (hi₀ : f i₀ = 1) (x : X) :
    ∃ c : X.presheaf.stalk x, c ≠ 0 ∧
      (denominatorIdeal X f).stalkIdeal x = Ideal.span {c} := by
  let := Fintype.ofFinite ι
  let : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  let : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    IsRegularLocalRing.uniqueFactorizationMonoid_of_regularLocal _
  rw [denominatorIdeal_stalkIdeal]
  exact FractionalIdeal.exists_denominatorIdeal_spanFinset_generator
    Finset.univ f i₀ (Finset.mem_univ i₀) hi₀

/-- The native denominator kernel module is locally rank one on a regular
locally Noetherian integral scheme, in every dimension. -/
theorem denominatorModule_isLocallyRankOne [IsLocallyNoetherian X]
    (hX : RegularStalks X) {ι : Type u} [Finite ι]
    (f : ι → X.functionField) (i₀ : ι) (hi₀ : f i₀ = 1) :
    IsLocallyRankOne X (denominatorModule X f) := by
  apply Hom.idealModule_isLocallyRankOne_of_stalkKernelBasis
    (denominatorIdeal X f).subschemeι
  intro z
  let x := (denominatorIdeal X f).subschemeι z
  let : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  obtain ⟨c, hc, hD⟩ := denominatorIdeal_stalk_exists_generator X hX f i₀ hi₀ x
  have hk := (denominatorIdeal X f).stalkIdeal_subschemeι_eq_ker_stalkMap z
  rw [hk] at hD
  exact ⟨Ideal.regularPrincipalIdealBasis _ c
    (IsRegularLocalRing.isSMulRegular_of_regularLocal_ne_zero _ c hc) hD⟩

/-- No proper principal ideal contains an original normalized base-ideal
stalk. This is the actual primitive-numerator property. -/
theorem baseIdeal_stalk_not_le_span_singleton (hX : RegularStalks X)
    {ι : Type u} [Fintype ι] (f : ι → X.functionField)
    (i₀ : ι) (hi₀ : f i₀ = 1) (x : X) (p : X.presheaf.stalk x) (hp : ¬ IsUnit p) :
    ¬ (baseIdeal X f).stalkIdeal x ≤ Ideal.span {p} := by
  let : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  obtain ⟨c, hc, hD⟩ := denominatorIdeal_stalk_exists_generator X hX f i₀ hi₀ x
  rw [denominatorIdeal_stalkIdeal] at hD
  rw [baseIdeal_stalkIdeal]
  exact FractionalIdeal.denominatorProductIdeal_not_le_span_singleton _
    (one_mem_spanFinset_of_coordinate_one f i₀ hi₀) c hc hD p hp

/-- The normalized base ideal is the unit ideal at every original stalk of
Krull dimension at most one. -/
theorem baseIdeal_stalk_eq_top_of_dimension_le_one (hX : RegularStalks X)
    {ι : Type u} [Fintype ι] (f : ι → X.functionField)
    (i₀ : ι) (hi₀ : f i₀ = 1) (x : X)
    (hd : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    (baseIdeal X f).stalkIdeal x = ⊤ := by
  let R := X.presheaf.stalk x
  let : IsRegularLocalRing R := hX x
  let : IsPrincipalIdealRing R :=
    IsRegularLocalRing.isPrincipalIdealRing_of_regularLocal_dimension_le_one R hd
  let p := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal R)
  have hp : ¬ IsUnit p := mem_nonunits_iff.mp
    ((IsLocalRing.mem_maximalIdeal p).mp
      (Submodule.IsPrincipal.generator_mem (IsLocalRing.maximalIdeal R)))
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {p} :=
    (Submodule.IsPrincipal.span_singleton_generator _).symm
  by_contra hnot
  exact baseIdeal_stalk_not_le_span_singleton X hX f i₀ hi₀ x p hp
    (hm ▸ IsLocalRing.le_maximalIdeal hnot)

private theorem prime_isMaximal_of_baseIdeal_stalk_le
    (hX : RegularStalks X) {ι : Type u} [Fintype ι]
    (f : ι → X.functionField) (i₀ : ι) (hi₀ : f i₀ = 1) (x : X)
    (hd : ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (hJ : (baseIdeal X f).stalkIdeal x ≤ P) : P.IsMaximal := by
  let R := X.presheaf.stalk x
  let : IsRegularLocalRing R := hX x
  have hn : (IsLocalRing.maximalIdeal R).spanFinrank ≤ 2 := by
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal.trans_le hd
  have hcases : (IsLocalRing.maximalIdeal R).spanFinrank ≤ 1 ∨
      (IsLocalRing.maximalIdeal R).spanFinrank = 2 := by omega
  rcases hcases with hsmall | htwo
  · have hd1 : ringKrullDim R ≤ 1 := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
      exact_mod_cast hsmall
    have htop := baseIdeal_stalk_eq_top_of_dimension_le_one X hX f i₀ hi₀ x hd1
    exact (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime)
      (top_le_iff.mp (htop ▸ hJ))).elim
  · have hd2 : ringKrullDim R = 2 := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, htwo]
      rfl
    by_cases hPm : P = IsLocalRing.maximalIdeal R
    · rw [hPm]
      infer_instance
    · let : P.IsPrincipal :=
        IsRegularLocalRing.isPrincipal_of_prime_ne_maximalIdeal_of_dimension_two R hd2 P hPm
      let p := Submodule.IsPrincipal.generator P
      have hp : ¬ IsUnit p := by
        intro hunit
        exact (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime))
          (P.eq_top_of_isUnit_mem (Submodule.IsPrincipal.generator_mem P) hunit)
      have hP : P = Ideal.span {p} :=
        (Submodule.IsPrincipal.span_singleton_generator P).symm
      exact (baseIdeal_stalk_not_le_span_singleton X hX f i₀ hi₀ x p hp (hP ▸ hJ)).elim

/-- In dimension at most two the actual original quotient stalk module has
finite length. Finite colength is a conclusion of primitivity and regularity. -/
theorem baseIdeal_stalkQuotient_finiteLength (hX : RegularStalks X)
    {ι : Type u} [Fintype ι] (f : ι → X.functionField)
    (i₀ : ι) (hi₀ : f i₀ = 1) (x : X)
    (hd : ringKrullDim (X.presheaf.stalk x) ≤ 2) :
    IsFiniteLength (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (baseIdeal X f).stalkIdeal x) := by
  let R := X.presheaf.stalk x
  let J := (baseIdeal X f).stalkIdeal x
  let : IsRegularLocalRing R := hX x
  let : Ring.KrullDimLE 0 (R ⧸ J) :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr (by
      intro P hP
      let : P.IsPrime := hP.1.1
      exact prime_isMaximal_of_baseIdeal_stalk_le X hX f i₀ hi₀ x hd P hP.1.2)
  let : IsArtinianRing (R ⧸ J) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let : IsArtinian R (R ⧸ J) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- On a Noetherian regular integral scheme with actual stalk dimensions at
most two, the canonical normalized base ideal cuts out an Artinian subscheme. -/
theorem baseIdeal_isArtinian_subscheme [IsNoetherian X]
    (hX : RegularStalks X) (hd : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2)
    {ι : Type u} [Fintype ι] (f : ι → X.functionField)
    (i₀ : ι) (hi₀ : f i₀ = 1) : IsArtinianScheme (baseIdeal X f).subscheme := by
  let : IsLocallyArtinian (baseIdeal X f).subscheme :=
    (baseIdeal X f).isLocallyArtinian_subscheme_of_stalkQuotient_finiteLength
      (fun x ↦ baseIdeal_stalkQuotient_finiteLength X hX f i₀ hi₀ x (hd x))
  let : CompactSpace (baseIdeal X f).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (baseIdeal X f).subschemeι
  exact ⟨⟩

end AlgebraicGeometry.Scheme.RationalCoordinates
