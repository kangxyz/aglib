/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Curves.GenericExtension
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Comparison
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Native
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Stalk.OpenSmoothCurveDVR
public import Aglib.AlgebraicGeometry.Points.Closed
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.RingTheory.Valuation.IsTrivialOn

/-!
# Actual rational pencils and complements of a pole

The original rational function gives a literal generic morphism to polynomial
P1. Native extension and curve finiteness retain its original scalar and
generic triangles. Actual regularity on the original punctured open and a
strict pole at the original point identify the exact affine-chart inverse
image and prove that original complement affine.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open scoped WithZero

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

variable {k : Type u} [Field k]

private theorem polynomialLine_integral : IsIntegral (Scheme.ProjectiveLine.projectiveP1 k) :=
  IsIntegral.of_isIso (Scheme.ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1 k).hom

private theorem polynomialLine_dimension :
    topologicalKrullDim (Scheme.ProjectiveLine.projectiveP1 k) = 1 := by
  let e := Scheme.ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1 k
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm.trans
    (Projectivity.twoChartLine_topologicalKrullDim k)

section Valuation

variable (X : FScheme k) [IsIntegral X.left] [SmoothOfRelativeDimension 1 X.hom]

omit [IsIntegral X.left] in
/-- The original smooth field-curve structure supplies local Noetherianity. -/
theorem smoothCurveLocallyNoetherian : IsLocallyNoetherian X.left := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  exact LocallyOfFiniteType.isLocallyNoetherian X.hom

attribute [local instance] smoothCurveLocallyNoetherian

/-- Every supplied closed point has its actual discrete valuation stalk. -/
theorem closedPoint_isDiscreteValuationRing (q : Scheme.ClosedPoint X.left) :
    IsDiscreteValuationRing (X.left.presheaf.stalk q.val) := by
  have : SmoothOfRelativeDimension 1 (𝟙 X.left ≫ X.hom) := by
    simpa only [Category.id_comp] using (inferInstance : SmoothOfRelativeDimension 1 X.hom)
  exact Scheme.smoothChart_closedPoint_dvr (𝟙 X.left) X.hom q.val q.property

/-- The native valuation of the actual closed-point DVR in the original
function field. Its exponents are negatives of the local orders. -/
def poleValuation (q : Scheme.ClosedPoint X.left) : Valuation X.left.functionField ℤᵐ⁰ := by
  let := closedPoint_isDiscreteValuationRing X q
  exact (IsDiscreteValuationRing.maximalIdeal (X.left.presheaf.stalk q.val)).valuation
    X.left.functionField

/-- The original structural field action used by the point-pole valuation. -/
local instance instAlgebraFunctionFieldForPoleValuation : Algebra k X.left.functionField :=
  Scheme.functionFieldConstantsAlgebra X.left X.hom

/-- Nonzero original field constants are units in the actual stalk, hence
the pole valuation is trivial on the original scalar field. -/
instance poleValuation_trivial (q : Scheme.ClosedPoint X.left) :
    (poleValuation X q).IsTrivialOn k := by
  let := closedPoint_isDiscreteValuationRing X q
  let : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, by trivial⟩⟩
  constructor
  intro a ha
  let c : Γ(X.left, ⊤) := X.hom.appTop ((Scheme.ΓSpecIso (.of k)).inv a)
  have hc : IsUnit c := (isUnit_iff_ne_zero.mpr ha).map
    (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom)
  have hg : IsUnit ((X.left.presheaf.germ ⊤ q.val (by trivial)) c) :=
    hc.map (X.left.presheaf.germ ⊤ q.val (by trivial)).hom
  have H := Ring.ordFrac_of_isUnit (R := X.left.presheaf.stalk q.val)
    (K := X.left.functionField) hg
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at H
  rw [Ring.ordFrac_eq_valuation_inv] at H
  have H' := congrArg Inv.inv H
  change poleValuation X q (X.left.germToFunctionField ⊤ c) = 1
  dsimp only [poleValuation]
  simpa only [inv_inv, inv_one] using H'

/-- The native valuation exponent is the negative of the original geometric order. -/
theorem poleValuation_eq_exp_neg_order (q : Scheme.ClosedPoint X.left)
    (hq : Order.coheight q.val = 1) (z : X.left.functionField) (hz : z ≠ 0) :
    poleValuation X q z = WithZero.exp (-X.left.ord z q.val) := by
  let := closedPoint_isDiscreteValuationRing X q
  have H : Ring.ordFrac (X.left.presheaf.stalk q.val) z =
      WithZero.exp (X.left.ord z q.val) := by
    change X.left.ordHom q.val hq z = WithZero.exp (X.left.ord z q.val)
    exact (Scheme.ord_eq_iff hq hz).mp rfl
  rw [Ring.ordFrac_eq_valuation_inv] at H
  have H' := congrArg Inv.inv H
  dsimp only [poleValuation]
  simpa only [inv_inv, ← WithZero.exp_neg] using H'

/-- A genuine pole on the original curve makes the original rational
function transcendental over the original field. -/
theorem transcendental_of_negative_order (q : Scheme.ClosedPoint X.left)
    (z : X.left.functionField) (hz : X.left.ord z q.val < 0) : Transcendental k z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hq : Order.coheight q.val = 1 := by
    by_contra hq
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hq] at hz
    omega
  have hv : 1 < poleValuation X q z := by
    rw [poleValuation_eq_exp_neg_order X q hq z hz0]
    exact WithZero.one_lt_exp_iff.mpr (neg_pos.mpr hz)
  exact Valuation.transcendental_of_ne_one k (v := poleValuation X q) z hz0 (ne_of_gt hv)

end Valuation

attribute [local instance] smoothCurveLocallyNoetherian

section Pencil

variable (X : FScheme k) [IsIntegral X.left]

/-- The original rational function's actual map into the first polynomial
chart of literal projective P1. -/
def genericPencil (z : X.left.functionField) :
    Spec X.left.functionField ⟶ Scheme.ProjectiveLine.projectiveP1 k :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (Scheme.functionFieldConstants X.left X.hom) z)) ≫
      Scheme.ProjectiveLine.chart k 0

@[reassoc] theorem genericPencil_over (z : X.left.functionField) :
    genericPencil X z ≫ Scheme.ProjectiveLine.structureMap k =
      X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom := by
  rw [genericPencil, Category.assoc, Scheme.ProjectiveLine.chart_over, ← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap k k[X]) ≫
      CommRingCat.ofHom
        (Polynomial.eval₂RingHom (Scheme.functionFieldConstants X.left X.hom) z) =
      CommRingCat.ofHom (Scheme.functionFieldConstants X.left X.hom) := by
    ext a
    simp
  rw [h, Scheme.functionFieldConstants_specMap]

theorem genericPencil_dominant (z : X.left.functionField)
    (hz : letI := Scheme.functionFieldConstantsAlgebra X.left X.hom; Transcendental k z) :
    IsDominant (genericPencil X z) := by
  let := Scheme.functionFieldConstantsAlgebra X.left X.hom
  let φ := Polynomial.eval₂RingHom (Scheme.functionFieldConstants X.left X.hom) z
  have hinj : Function.Injective φ := transcendental_iff_injective.mp hz
  let : IsIntegral (Scheme.ProjectiveLine.projectiveP1 k) := polynomialLine_integral
  let : IsDominant (Scheme.ProjectiveLine.chart k 0) :=
    ⟨(Scheme.ProjectiveLine.chart k 0).isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let : IsDominant (Spec.map (CommRingCat.ofHom φ)) := ⟨by
    change DenseRange (PrimeSpectrum.comap φ)
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mpr
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hinj]
    exact bot_le⟩
  unfold genericPencil
  infer_instance

/-- An original transcendental rational function on a smooth proper integral
curve constructs a finite dominant P1 morphism, retaining both actual triangles. -/
theorem exists_finite_pencil [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
    (z : X.left.functionField)
    (hz : letI := Scheme.functionFieldConstantsAlgebra X.left X.hom; Transcendental k z) :
    ∃ f : X.left ⟶ Scheme.ProjectiveLine.projectiveP1 k,
      f ≫ Scheme.ProjectiveLine.structureMap k = X.hom ∧
      X.left.fromSpecStalk (genericPoint X.left) ≫ f = genericPencil X z ∧
      IsFinite f ∧ IsDominant f := by
  let : IsIntegral (Scheme.ProjectiveLine.projectiveP1 k) := polynomialLine_integral
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have hnormal := Scheme.smoothFieldNormality k X.left X.hom inferInstance
  obtain ⟨f, hf, hfg⟩ := normalProperCurveGenericExtension k X.left
    (Scheme.ProjectiveLine.projectiveP1 k) X.hom (Scheme.ProjectiveLine.structureMap k)
    inferInstance inferInstance hnormal inferInstance (genericPencil X z) (genericPencil_over X z)
  let : IsDominant (genericPencil X z) := genericPencil_dominant X z hz
  let : IsDominant (X.left.fromSpecStalk (genericPoint X.left) ≫ f) :=
    hfg.symm ▸ inferInstance
  let : IsDominant f := IsDominant.of_comp (X.left.fromSpecStalk (genericPoint X.left)) f
  have : IsProper (f ≫ Scheme.ProjectiveLine.structureMap k) := hf.symm ▸ inferInstance
  let : IsProper f := IsProper.of_comp f (Scheme.ProjectiveLine.structureMap k)
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := ⟨⟩
  have hd := Scheme.smoothFieldDimension k X.left X.hom 1 inferInstance inferInstance
  let : IsFinite f :=
    Projectivity.proper_dominant_curve_isFinite f hd.le polynomialLine_dimension
  exact ⟨f, hf, hfg, inferInstance, inferInstance⟩

/-- In particular, a genuine pole produces the finite pencil with its
original rational-function generic map; no transcendence premise remains. -/
theorem exists_finite_pencil_of_negative_order
    [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
    (q : Scheme.ClosedPoint X.left) (z : X.left.functionField)
    (hz : X.left.ord z q.val < 0) :
    ∃ f : X.left ⟶ Scheme.ProjectiveLine.projectiveP1 k,
      f ≫ Scheme.ProjectiveLine.structureMap k = X.hom ∧
      X.left.fromSpecStalk (genericPoint X.left) ≫ f = genericPencil X z ∧
      IsFinite f ∧ IsDominant f :=
  exists_finite_pencil X z (transcendental_of_negative_order X q z hz)

end Pencil
/-- The original open complement of the supplied closed point. -/
def complementOpen (Y : Scheme.{u}) (q : Scheme.ClosedPoint Y) : Y.Opens :=
  ⟨({q.val} : Set Y)ᶜ, q.property.isOpen_compl⟩

@[simp] theorem mem_complementOpen {Y : Scheme.{u}} (q : Scheme.ClosedPoint Y) (y : Y) :
    y ∈ complementOpen Y q ↔ y ≠ q.val := Iff.rfl

section LocalFunctions

variable (X : FScheme k) [IsIntegral X.left]

/-- Constants in an original open have their original generic-field values. -/
theorem genericGerm_constantSection (U : X.left.Opens) (hU : (U : Set X.left).Nonempty)
    (a : k) :
    X.left.presheaf.germ U (genericPoint X.left) (Scheme.generic_mem_open U hU)
        (Scheme.constantSection X U a) = Scheme.functionFieldConstants X.left X.hom a := by
  change X.left.presheaf.germ U (genericPoint X.left) (Scheme.generic_mem_open U hU)
      (X.left.presheaf.map (homOfLE le_top).op (Scheme.constants X a)) =
    X.left.presheaf.germ ⊤ (genericPoint X.left) (by trivial) (Scheme.constants X a)
  exact X.left.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X.left)
    (Scheme.generic_mem_open U hU) (Scheme.constants X a)

/-- The actual generic value map is linear and multiplicative for the
original structural constants on the original open and function field. -/
def openSectionValue (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) :
    letI := (Scheme.constantSection X U).toAlgebra
    letI := Scheme.functionFieldConstantsAlgebra X.left X.hom
    Γ(X.left, U) →ₐ[k] X.left.functionField := by
  letI := (Scheme.constantSection X U).toAlgebra
  letI := Scheme.functionFieldConstantsAlgebra X.left X.hom
  exact { (X.left.presheaf.germ U (genericPoint X.left) (Scheme.generic_mem_open U hU)).hom with
    commutes' := genericGerm_constantSection X U hU }

theorem openSectionValue_injective (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) :
    Function.Injective (openSectionValue X U hU) := by
  let : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  change Function.Injective (X.left.germToFunctionField U)
  exact X.left.germToFunctionField_injective U

/-- The actual generic value of an original regular section has nonnegative
order at every point of its original open. -/
theorem openSectionValue_order_nonneg [IsLocallyNoetherian X.left]
    (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) (s : Γ(X.left, U))
    (x : X.left) (hx : x ∈ U) : 0 ≤ X.left.ord (openSectionValue X U hU s) x := by
  let : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  change 0 ≤ X.left.ord (X.left.germToFunctionField U s) x
  by_cases hs : s = 0
  · simp [hs]
  have hOne : X.left.ord (1 : X.left.functionField) x = 0 := by
    simpa only [map_one] using
      (Scheme.ord_of_isUnit (X := X.left) (U := U) (f := 1) isUnit_one hx)
  have H := Scheme.ord_le_smul (X := X.left) (x := x) (U := U)
    hx hs (1 : X.left.functionField)
  simpa only [Algebra.smul_def, mul_one, hOne, RingHom.algebraMap_toAlgebra] using H

private theorem genericToOpen_toSpecΓ (U : X.left.Opens)
    (hU : (U : Set X.left).Nonempty) :
    Scheme.genericToOpen U hU ≫ U.toSpecΓ =
      Spec.map (X.left.presheaf.germ U (genericPoint X.left) (Scheme.generic_mem_open U hU)) :=
  Scheme.Opens.fromSpecStalkOfMem_toSpecΓ U (genericPoint X.left) (Scheme.generic_mem_open U hU)

omit [IsIntegral X.left] in
private theorem open_toSpec_factor (U : X.left.Opens) {R : CommRingCat.{u}}
    (f : U.toScheme ⟶ Spec R) :
    U.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ U.topIso.hom) = f := by
  rw [Scheme.Opens.toSpecΓ]
  simp only [Spec.map_comp, Category.assoc]
  rw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private theorem genericToOpen_toSpec (U : X.left.Opens) (hU : (U : Set X.left).Nonempty)
    {R : CommRingCat.{u}} (f : U.toScheme ⟶ Spec R) :
    Scheme.genericToOpen U hU ≫ f =
      Spec.map (((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ U.topIso.hom) ≫
        X.left.presheaf.germ U (genericPoint X.left) (Scheme.generic_mem_open U hU)) := by
  calc
    _ = Scheme.genericToOpen U hU ≫
        (U.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ U.topIso.hom)) :=
      congrArg (fun g => Scheme.genericToOpen U hU ≫ g) (open_toSpec_factor X U f).symm
    _ = _ := by rw [← Category.assoc, genericToOpen_toSpecΓ, ← Spec.map_comp]

omit [IsIntegral X.left] in
/-- The canonical map of an original open to its spectrum preserves the
original structural constants and the original field structure morphism. -/
theorem openToSpecΓ_constants (U : X.left.Opens) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Scheme.constantSection X U)) = U.ι ≫ X.hom := by
  change U.toSpecΓ ≫ Spec.map
    (((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ≫
      X.left.presheaf.map (homOfLE le_top).op) = _
  rw [Spec.map_comp, Spec.map_comp, ← Category.assoc,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private def localAffinePencil (U : X.left.Opens) (s : Γ(X.left, U)) :
    U.toScheme ⟶ Spec (.of k[X]) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Scheme.constantSection X U) s))

private def localPencil (U : X.left.Opens) (s : Γ(X.left, U)) :
    U.toScheme ⟶ Scheme.ProjectiveLine.projectiveP1 k :=
  localAffinePencil X U s ≫ Scheme.ProjectiveLine.chart k 0

omit [IsIntegral X.left] in
private theorem localPencil_over (U : X.left.Opens) (s : Γ(X.left, U)) :
    localPencil X U s ≫ Scheme.ProjectiveLine.structureMap k = U.ι ≫ X.hom := by
  rw [localPencil, Category.assoc, Scheme.ProjectiveLine.chart_over, localAffinePencil,
    Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap k k[X]) ≫
      CommRingCat.ofHom (Polynomial.eval₂RingHom (Scheme.constantSection X U) s) =
      CommRingCat.ofHom (Scheme.constantSection X U) := by
    ext a
    simp
  rw [h]
  exact openToSpecΓ_constants X U

private theorem localPencil_generic (U : X.left.Opens) (hU : (U : Set X.left).Nonempty)
    (s : Γ(X.left, U)) (z : X.left.functionField)
    (hs : X.left.presheaf.germ U (genericPoint X.left) (Scheme.generic_mem_open U hU) s = z) :
    Scheme.genericToOpen U hU ≫ localPencil X U s = genericPencil X z := by
  have hpoly : (X.left.presheaf.germ U (genericPoint X.left)
        (Scheme.generic_mem_open U hU)).hom.comp
      (Polynomial.eval₂RingHom (Scheme.constantSection X U) s) =
      Polynomial.eval₂RingHom (Scheme.functionFieldConstants X.left X.hom) z := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        using genericGerm_constantSection X U hU a
    · simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hs
  have hcat : CommRingCat.ofHom (Polynomial.eval₂RingHom (Scheme.constantSection X U) s) ≫
      X.left.presheaf.germ U (genericPoint X.left) (Scheme.generic_mem_open U hU) =
      CommRingCat.ofHom
        (Polynomial.eval₂RingHom (Scheme.functionFieldConstants X.left X.hom) z) := by
    apply CommRingCat.hom_ext
    exact hpoly
  rw [localPencil, localAffinePencil, ← Category.assoc, ← Category.assoc,
    genericToOpen_toSpecΓ, Category.assoc, ← Spec.map_comp_assoc, hcat]
  rfl

private theorem restriction_eq_localPencil
    (f : X.left ⟶ Scheme.ProjectiveLine.projectiveP1 k)
    (hf : f ≫ Scheme.ProjectiveLine.structureMap k = X.hom)
    (z : X.left.functionField)
    (hfg : X.left.fromSpecStalk (genericPoint X.left) ≫ f = genericPencil X z)
    (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) (s : Γ(X.left, U))
    (hs : X.left.presheaf.germ U (genericPoint X.left) (Scheme.generic_mem_open U hU) s = z) :
    U.ι ≫ f = localPencil X U s := by
  let : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : IsDominant (Scheme.genericToOpen U hU ≫ U.ι) := by
    rw [Scheme.genericToOpen_ι]
    infer_instance
  let : IsDominant (Scheme.genericToOpen U hU) :=
    IsDominant.of_comp_of_isOpenImmersion (Scheme.genericToOpen U hU) U.ι
  apply ext_of_isDominant_of_isSeparated (Scheme.ProjectiveLine.structureMap k)
    (by rw [Category.assoc, hf, localPencil_over]) (Scheme.genericToOpen U hU)
  rw [← Category.assoc, Scheme.genericToOpen_ι, hfg, localPencil_generic X U hU s z hs]

/-- An actual equality of generic maps to an affine scheme determines the
actual generic value of each original pulled-back coordinate. -/
theorem genericValue_of_specMap_eq (U : X.left.Opens)
    (hU : (U : Set X.left).Nonempty) {R : CommRingCat.{u}}
    (a : U.toScheme ⟶ Spec R) (ρ : R ⟶ X.left.functionField)
    (ha : Scheme.genericToOpen U hU ≫ a = Spec.map ρ) (r : R) :
    X.left.presheaf.germ U (genericPoint X.left) (Scheme.generic_mem_open U hU)
      (U.topIso.hom (a.appTop ((Scheme.ΓSpecIso R).inv r))) = ρ r := by
  have hRing := Spec.map_injective ((genericToOpen_toSpec X U hU a).symm.trans ha)
  exact congrArg (fun g : R ⟶ X.left.functionField => g r) hRing

private theorem affineCoordinate_generic_value (U : X.left.Opens)
    (hU : (U : Set X.left).Nonempty) (a : U.toScheme ⟶ Spec (.of k[X]))
    (z : X.left.functionField)
    (ha : Scheme.genericToOpen U hU ≫ a = Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom (Scheme.functionFieldConstants X.left X.hom) z))) :
    X.left.presheaf.germ U (genericPoint X.left) (Scheme.generic_mem_open U hU)
      (U.topIso.hom (a.appTop ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X))) = z := by
  refine (genericValue_of_specMap_eq X U hU a _ ha Polynomial.X).trans ?_
  change (Polynomial.eval₂RingHom (Scheme.functionFieldConstants X.left X.hom) z) Polynomial.X = z
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

end LocalFunctions

section Complement

variable (X : FScheme k) [IsIntegral X.left] [SmoothOfRelativeDimension 1 X.hom]

/-- The original generic point lies in the complement of every supplied
closed point of the original smooth curve. -/
theorem genericPoint_mem_complementOpen (q : Scheme.ClosedPoint X.left) :
    genericPoint X.left ∈ complementOpen X.left q := by
  change genericPoint X.left ≠ q.val
  intro h
  have hd := Scheme.smoothFieldDimension k X.left X.hom 1 inferInstance inferInstance
  apply Scheme.DimensionOne.genericPoint_not_isClosed_of_dimension_one X.left hd
  rw [h]
  exact q.property

/-- Regularity away from the original point is witnessed on the original
open by an actual section with the specified generic value. -/
def RegularAway (q : Scheme.ClosedPoint X.left) (z : X.left.functionField) : Prop :=
  ∃ s : Γ(X.left, complementOpen X.left q),
    X.left.presheaf.germ (complementOpen X.left q) (genericPoint X.left)
      (genericPoint_mem_complementOpen X q) s = z

private theorem not_mem_affineChart_of_negative_order
    (f : X.left ⟶ Scheme.ProjectiveLine.projectiveP1 k) (z : X.left.functionField)
    (hfg : X.left.fromSpecStalk (genericPoint X.left) ≫ f = genericPencil X z)
    (q : Scheme.ClosedPoint X.left) (hz : X.left.ord z q.val < 0) :
    f q.val ∉ (Scheme.ProjectiveLine.chart k 0).opensRange := by
  intro hq
  let V := f ⁻¹ᵁ (Scheme.ProjectiveLine.chart k 0).opensRange
  have hqV : q.val ∈ V := hq
  have hV : (V : Set X.left).Nonempty := ⟨q.val, hqV⟩
  let : Nonempty V := ⟨⟨q.val, hqV⟩⟩
  have hrange : Set.range (V.ι ≫ f) ⊆ Set.range (Scheme.ProjectiveLine.chart k 0) := by
    rintro _ ⟨v, rfl⟩
    exact v.property
  let a := IsOpenImmersion.lift (Scheme.ProjectiveLine.chart k 0) (V.ι ≫ f) hrange
  have ha : a ≫ Scheme.ProjectiveLine.chart k 0 = V.ι ≫ f :=
    IsOpenImmersion.lift_fac (Scheme.ProjectiveLine.chart k 0) (V.ι ≫ f) hrange
  have hag : Scheme.genericToOpen V hV ≫ a = Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom (Scheme.functionFieldConstants X.left X.hom) z)) := by
    apply (cancel_mono (Scheme.ProjectiveLine.chart k 0)).mp
    rw [Category.assoc, ha, ← Category.assoc, Scheme.genericToOpen_ι]
    exact hfg
  let s : Γ(X.left, V) := V.topIso.hom (a.appTop ((Scheme.ΓSpecIso (.of k[X])).inv Polynomial.X))
  have hs : X.left.germToFunctionField V s = z :=
    affineCoordinate_generic_value X V hV a z hag
  have hn := openSectionValue_order_nonneg X V hV s q.val hqV
  change 0 ≤ X.left.ord (X.left.germToFunctionField V s) q.val at hn
  rw [hs] at hn
  exact (not_le_of_gt hz) hn

/-- The actual extension of a function regular away from q and with a pole
at q has exactly the original punctured open as its affine-chart inverse image. -/
theorem pencil_preimage_affineChart
    (f : X.left ⟶ Scheme.ProjectiveLine.projectiveP1 k)
    (hf : f ≫ Scheme.ProjectiveLine.structureMap k = X.hom)
    (z : X.left.functionField)
    (hfg : X.left.fromSpecStalk (genericPoint X.left) ≫ f = genericPencil X z)
    (q : Scheme.ClosedPoint X.left) (hz : X.left.ord z q.val < 0)
    (hreg : RegularAway X q z) :
    f ⁻¹ᵁ (Scheme.ProjectiveLine.chart k 0).opensRange = complementOpen X.left q := by
  let U := complementOpen X.left q
  have hU : (U : Set X.left).Nonempty :=
    ⟨genericPoint X.left, genericPoint_mem_complementOpen X q⟩
  obtain ⟨s, hs⟩ := hreg
  have hlocal : U.ι ≫ f = localPencil X U s :=
    restriction_eq_localPencil X f hf z hfg U hU s hs
  ext x
  constructor
  · intro hx
    change x ≠ q.val
    intro he
    exact not_mem_affineChart_of_negative_order X f z hfg q hz (he ▸ hx)
  · intro hx
    have hu : x ∈ U := hx
    have he := congrArg (fun g : U.toScheme ⟶ Scheme.ProjectiveLine.projectiveP1 k =>
      g ⟨x, hu⟩) hlocal
    change f x = Scheme.ProjectiveLine.chart k 0 (localAffinePencil X U s ⟨x, hu⟩) at he
    change f x ∈ Set.range (Scheme.ProjectiveLine.chart k 0)
    exact ⟨localAffinePencil X U s ⟨x, hu⟩, he.symm⟩

/-- The original pole function constructs a finite pencil with its exact
original affine-chart inverse image and proves that original complement affine. -/
theorem exists_finite_pencil_with_affine_complement [IsProper X.hom]
    (q : Scheme.ClosedPoint X.left) (z : X.left.functionField)
    (hz : X.left.ord z q.val < 0) (hreg : RegularAway X q z) :
    ∃ f : X.left ⟶ Scheme.ProjectiveLine.projectiveP1 k,
      f ≫ Scheme.ProjectiveLine.structureMap k = X.hom ∧
      X.left.fromSpecStalk (genericPoint X.left) ≫ f = genericPencil X z ∧
      IsFinite f ∧ IsDominant f ∧
      f ⁻¹ᵁ (Scheme.ProjectiveLine.chart k 0).opensRange = complementOpen X.left q ∧
      IsAffineOpen (complementOpen X.left q) := by
  obtain ⟨f, hf, hfg, hfin, hdom⟩ := exists_finite_pencil_of_negative_order X q z hz
  let := hfin
  have hpre := pencil_preimage_affineChart X f hf z hfg q hz hreg
  have hAff := (isAffineOpen_opensRange (Scheme.ProjectiveLine.chart k 0)).preimage f
  exact ⟨f, hf, hfg, hfin, hdom, hpre, hpre ▸ hAff⟩

end Complement

/-- The first polynomial affine chart transported through the fixed native
lifted-coordinate projective-line comparison. -/
def nativePencilChart (k : Type u) [Field k] :
    Spec (.of k[X]) ⟶ AlgebraicGeometry.ProjectiveSpace k (ULift.{u} (Fin 2)) :=
  Scheme.ProjectiveLine.chart k 0 ≫
    (ProjectiveLine.projectiveLineOverIsoNative k).hom.left

instance nativePencilChart_isOpenImmersion (k : Type u) [Field k] :
    IsOpenImmersion (nativePencilChart k) := by
  let e := ProjectiveLine.projectiveLineOverIsoNative k
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  change IsOpenImmersion (Scheme.ProjectiveLine.chart k 0 ≫ e.hom.left)
  infer_instance

/-- The same original rational function gives the literal native P1 map,
with its original scalar and generic triangles and exact affine complement. -/
theorem exists_finite_native_pencil_with_affine_complement
    (X : FScheme k) [IsIntegral X.left] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (q : Scheme.ClosedPoint X.left) (z : X.left.functionField)
    (hz : X.left.ord z q.val < 0) (hreg : RegularAway X q z) :
    ∃ f : X.left ⟶ AlgebraicGeometry.ProjectiveSpace k (ULift.{u} (Fin 2)),
      f ≫ AlgebraicGeometry.ProjectiveSpace.toSpec k (ULift.{u} (Fin 2)) = X.hom ∧
      X.left.fromSpecStalk (genericPoint X.left) ≫ f = genericPencil X z ≫
        (ProjectiveLine.projectiveLineOverIsoNative k).hom.left ∧
      IsFinite f ∧ IsDominant f ∧
      f ⁻¹ᵁ (nativePencilChart k).opensRange = complementOpen X.left q ∧
      IsAffineOpen (complementOpen X.left q) := by
  obtain ⟨f, hf, hfg, hfin, hdom, hpre, hAff⟩ :=
    exists_finite_pencil_with_affine_complement X q z hz hreg
  let e := ProjectiveLine.projectiveLineOverIsoNative k
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let := hfin
  let := hdom
  refine ⟨f ≫ e.hom.left, ?_, ?_, inferInstance, inferInstance, ?_, hAff⟩
  · have he : e.hom.left ≫
        AlgebraicGeometry.ProjectiveSpace.toSpec k (ULift.{u} (Fin 2)) =
        Scheme.ProjectiveLine.structureMap k := e.hom.w
    rw [Category.assoc, he]
    exact hf
  · rw [← Category.assoc, hfg]
  · change (f ≫ e.hom.left) ⁻¹ᵁ
      (Scheme.ProjectiveLine.chart k 0 ≫ e.hom.left).opensRange = _
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.comp_preimage,
      Scheme.Hom.preimage_image_eq]
    exact hpre

end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor
