/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.Sections
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.IdealClass
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorIndependence
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.TrivializedPower
public import Aglib.AlgebraicGeometry.Modules.Invertible.ScalarAutomorphisms
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Length

/-!
# The original point divisor for normalized pole functions

The original point-ideal inclusion has divisor exactly the original
rational point. Its coefficient is computed by the length-one actual
stalk quotient, and its support by the original closed immersion.
It yields an actual positive-point module isomorphism to O([p]), normalized
by the original section one. The normalization is also an equality of actual
structure-module maps, hence holds on all opens. A degree-one calculation
alone does not identify the original divisor.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.FiniteCartierDegree

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

variable {k : Type u} [Field k]

/-- The native rational point with exactly the original two morphisms. -/
def rationalPoint (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) : Scheme.RationalPoint k X.left := ⟨X.hom, p, hp⟩

@[simp] theorem rationalPoint_structureMap (X : FScheme k)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    (rationalPoint X p hp).structureMap = X.hom := rfl

@[simp] theorem rationalPoint_sectionMap (X : FScheme k)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    (rationalPoint X p hp).sectionMap = p := rfl

/-- The original closed point selected by the original rational section. -/
def closedPoint (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) : Scheme.ClosedPoint X.left :=
  ⟨(rationalPoint X p hp).point, (rationalPoint X p hp).point_isClosed⟩

@[simp] theorem closedPoint_val (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) :
    (closedPoint X p hp).val = p (IsLocalRing.closedPoint k) := rfl

/-- The existing closed-point divisor with its original multiplicity. -/
def pointDivisor (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℤ) : Divisor X.left := Finsupp.single (closedPoint X p hp) n

theorem pointDivisor_nsmul (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    n • pointDivisor X p hp 1 = pointDivisor X p hp n := by
  classical
  simp only [pointDivisor, Finsupp.smul_single, nsmul_eq_mul, mul_one]

theorem pointDivisor_one_add (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    pointDivisor X p hp 1 + pointDivisor X p hp n = pointDivisor X p hp ((n + 1 : ℕ) : ℤ) := by
  classical
  simp only [pointDivisor, ← Finsupp.single_add]
  congr 1
  omega

theorem pointDivisor_nonneg (X : FScheme k) (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) : ∀ x, 0 ≤ pointDivisor X p hp n x := by
  classical
  intro x
  by_cases hx : x = closedPoint X p hp
  · simpa only [pointDivisor, hx, Finsupp.single_eq_same] using Int.natCast_nonneg n
  · simp only [pointDivisor, Finsupp.single_eq_of_ne hx, le_refl]

/-- The native integral structure follows from the given smooth connected curve. -/
theorem isIntegral_of_properties (X : FScheme k) (hX : Properties X) : IsIntegral X.left := by
  let := hX.smooth
  let := hX.connected
  let : GeometricallyIntegral X.hom :=
    Scheme.geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected X.hom
  exact GeometricallyIntegral.isIntegral_of_subsingleton X.hom

/-- Every actual closed-point stalk of the given smooth curve is a DVR. -/
theorem isDiscreteValuationRing_stalk (X : FScheme k) (hX : Properties X) [IsIntegral X.left]
    (x : Scheme.ClosedPoint X.left) :
    IsDiscreteValuationRing (X.left.presheaf.stalk x.val) := by
  have h : SmoothOfRelativeDimension 1 (𝟙 X.left ≫ X.hom) := by
    simpa only [Category.id_comp] using hX.smooth
  let := h
  exact Scheme.smoothChart_closedPoint_dvr (𝟙 X.left) X.hom x.val x.property

/-- The original point ideal's divisor, computed by its original inclusion
and a native generic chart. -/
def idealDivisor (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) : Divisor X.left := by
  let : IsIntegral X.left := isIntegral_of_properties X hX
  let : IsNoetherian X.left := curveProperties_isNoetherian hX
  have (x : Scheme.ClosedPoint X.left) :
      IsDiscreteValuationRing (X.left.presheaf.stalk x.val) := isDiscreteValuationRing_stalk X hX x
  let I := idealLineBundle X hX p hp
  let c := Picard.RationalTrivialization.localChart X.left I.val I.property (genericPoint X.left)
  let : Nonempty c.1 := ⟨⟨genericPoint X.left, c.2.property⟩⟩
  exact MapDivisors.mapDivisor X.left I (Scheme.Hom.idealInclusion p) c.1 c.2.val

/-- Local quotient length and original support identify the point divisor
itself, independently of its numerical degree or global ideal sections. -/
theorem idealDivisor_eq_pointDivisor (X : FScheme k) (hX : Properties X)
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    idealDivisor X hX p hp = pointDivisor X p hp 1 := by
  let : IsIntegral X.left := isIntegral_of_properties X hX
  let : IsNoetherian X.left := curveProperties_isNoetherian hX
  have (x : Scheme.ClosedPoint X.left) :
      IsDiscreteValuationRing (X.left.presheaf.stalk x.val) := isDiscreteValuationRing_stalk X hX x
  let I := idealLineBundle X hX p hp
  let c := Picard.RationalTrivialization.localChart X.left I.val I.property (genericPoint X.left)
  let : Nonempty c.1 := ⟨⟨genericPoint X.left, c.2.property⟩⟩
  exact pointMapDivisor_eq_single X.left (rationalPoint X p hp) I.property c.1 c.2.val

/-- Global sections of the actual module-sheaf isomorphism, with original field scalars. -/
def sectionsLinearEquivOfIso (X : FScheme k) {M N : X.left.Modules} (e : M ≅ N) :
    M.val.obj (op ⊤) ≃ₗ[k] N.val.obj (op ⊤) := by
  let F : X.left.Modules ⥤ ModuleCat Γ(X.left, ⊤) :=
    SheafOfModules.evaluation X.left.ringCatSheaf (op ⊤)
  let E := (F.mapIso e).toLinearEquiv
  exact {
    __ := E.toAddEquiv
    map_smul' := fun a x ↦ E.map_smul (Scheme.constants X a) x }

private theorem exists_normalized_point_iso
    (X : FScheme k) (L M : LineBundle X.left)
    (s : (show X.left.Modules from SheafOfModules.unit X.left.ringCatSheaf) ⟶ L.val)
    (hs : s.val.app (op ⊤) (1 : Γ(X.left, ⊤)) ≠ 0)
    (b : M.val.val.obj (op ⊤)) (hb : b ≠ 0)
    (hdim : Module.finrank k (L.val.val.obj (op ⊤)) = 1)
    (E₀ : (show X.left.Modules from L.val) ≅ (show X.left.Modules from M.val)) :
    ∃ E : (show X.left.Modules from L.val) ≅ (show X.left.Modules from M.val),
      E.hom.val.app (op ⊤) (s.val.app (op ⊤) (1 : Γ(X.left, ⊤))) = b := by
  let F := sectionsLinearEquivOfIso X E₀
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim hs (F.symm b)
  have hEq : a • F (s.val.app (op ⊤) (1 : Γ(X.left, ⊤))) = b := by
    simpa only [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply] using congrArg F ha
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at hEq
    exact hb hEq.symm
  let u : Γ(X.left, ⊤)ˣ := Units.map (Scheme.constants X).toMonoidHom (Units.mk0 a ha0)
  let E := E₀ ≪≫ TrivializedPower.scalarIso X.left M.val u
  refine ⟨E, ?_⟩
  change (TrivializedPower.scalarMap X.left M.val (u : Γ(X.left, ⊤))).val.app (op ⊤)
    (E₀.hom.val.app (op ⊤) (s.val.app (op ⊤) (1 : Γ(X.left, ⊤)))) = b
  rw [TrivializedPower.scalarMap_app]
  have ht : (homOfLE le_top : (⊤ : X.left.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [ht, op_id, X.left.presheaf.map_id]
  exact hEq

/-- The first native tensor power is compared by its original right unit. -/
def firstTensorPowerIso (Y : Scheme.{u}) (L : LineBundle Y) :
    (tensorPowerLineBundle Y L 1).val ≅ L.val :=
  tensorSheafIso Y (Iso.refl _) (Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf)) ≪≫
      (SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app _

/-- Native powers of an actual abstract line bundle, from one actual
point-divisor sheaf isomorphism. Keeping the coefficient object abstract
avoids expanding the point ideal inside every recursive comparison. -/
def tensorPowerPointDivisorIso (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    [∀ x : Scheme.ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim Y ≤ 1) (L : LineBundle Y) (x : Scheme.ClosedPoint Y)
    (e : L.val ≅ DivisorClass.divisorSheaf Y (Finsupp.single x 1)) :
    (n : ℕ) → (tensorPowerLineBundle Y L n).val ≅
      DivisorClass.divisorSheaf Y (Finsupp.single x (n : ℤ))
  | 0 => Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf) ≪≫
      DivisorClass.globalTrivialization Y hdim (Finsupp.single x 0) 1 (by
        intro y
        have h : Y.ord (1 : Y.functionField) y.val = 0 := (Divisors.localOrder Y y).map_zero
        simp only [Finsupp.single_zero, Finsupp.zero_apply, Units.val_one, h, zero_add])
  | 1 => firstTensorPowerIso Y L ≪≫ e
  | n + 2 =>
    let eN : (tensorPowerLineBundle Y L (n + 1)).val ≅
        DivisorClass.divisorSheaf Y (Finsupp.single x ((n + 1 : ℕ) : ℤ)) :=
      tensorPowerPointDivisorIso Y hdim L x e (n + 1)
    let eT : tensorSheaf Y L.val (tensorPowerLineBundle Y L (n + 1)).val ≅
        tensorSheaf Y (DivisorClass.divisorSheaf Y (Finsupp.single x 1))
          (DivisorClass.divisorSheaf Y (Finsupp.single x ((n + 1 : ℕ) : ℤ))) :=
      tensorSheafIso Y e eN
    eT ≪≫ DivisorClass.divisorTensorIso Y hdim (Finsupp.single x 1)
        (Finsupp.single x ((n + 1 : ℕ) : ℤ)) ≪≫
      eqToIso (congrArg (DivisorClass.divisorSheaf Y) (by
        rw [← Finsupp.single_add]
        congr 1
        omega))

private theorem module_comp_app (Y : Scheme.{u}) {M N P : Y.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (U : Y.Opens) (m : Γ(M, U)) :
    (f ≫ g).val.app (op U) m = g.val.app (op U) (f.val.app (op U) m) := rfl

private theorem tensorSheafLeftUnit_inv_section (Y : Scheme.{u}) (M : Y.Modules)
    (U : Y.Opens) (m : Γ(M, U)) :
    (tensorSheafLeftUnit Y M).inv.val.app (op U) m =
      moduleTensorSection Y (SheafOfModules.unit Y.ringCatSheaf) M U (1 : Γ(Y, U)) m :=
  leftUnitor_inv_moduleTensorSection (X := Y) M U m

private theorem tensorSheafMap_section (Y : Scheme.{u})
    {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N')
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (tensorSheafMap Y a b).val.app (op U) (moduleTensorSection Y M N U m n) =
      moduleTensorSection Y M' N' U (a.val.app (op U) m) (b.val.app (op U) n) :=
  SheafOfModulesOfCommRing.tensor_map_tensorSection Y.sheaf a b (op U) m n

private theorem tensorSheafIso_section (Y : Scheme.{u})
    {M M' N N' : Y.Modules} (a : M ≅ M') (b : N ≅ N')
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (tensorSheafIso Y a b).hom.val.app (op U) (moduleTensorSection Y M N U m n) =
      moduleTensorSection Y M' N' U (a.hom.val.app (op U) m) (b.hom.val.app (op U) n) :=
  tensorSheafMap_section Y a.hom b.hom U m n

private theorem firstTensorPowerIso_inclusion (Y : Scheme.{u}) (L : LineBundle Y)
    (σ : (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) ⟶
      (show Y.Modules from L.val))
    (U : Y.Opens) (m : (tensorPowerLineBundle Y L 0).val.val.obj (op U)) :
    (firstTensorPowerIso Y L).hom.val.app (op U)
      (((tensorSheafLeftUnit Y (tensorPowerLineBundle Y L 0).val).inv ≫
        tensorSheafMap Y σ (𝟙 (tensorPowerLineBundle Y L 0).val)).val.app (op U) m) =
      (Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf)).hom.val.app (op U) m •
          σ.val.app (op U) (1 : Γ(Y, U)) := by
  let c₀ := Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf)
  change ((SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app L.val).hom.val.app
      (op U) ((tensorSheafIso Y (Iso.refl L.val) c₀).hom.val.app (op U)
        ((tensorSheafMap Y σ (𝟙 (tensorPowerLineBundle Y L 0).val)).val.app (op U)
          ((tensorSheafLeftUnit Y (tensorPowerLineBundle Y L 0).val).inv.val.app (op U) m))) = _
  rw [tensorSheafLeftUnit_inv_section Y (tensorPowerLineBundle Y L 0).val U m,
    tensorSheafMap_section Y σ (𝟙 (tensorPowerLineBundle Y L 0).val) U
      (1 : Γ(Y, U)) m]
  change ((SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app L.val).hom.val.app
      (op U) ((tensorSheafIso Y (Iso.refl L.val) c₀).hom.val.app (op U)
        (moduleTensorSection Y L.val (tensorPowerLineBundle Y L 0).val U
          (σ.val.app (op U) (1 : Γ(Y, U))) m)) = _
  have ht := tensorSheafIso_section Y (Iso.refl L.val) c₀ U
    (σ.val.app (op U) (1 : Γ(Y, U))) m
  exact (congrArg (fun z ↦
    ((SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app L.val).hom.val.app
      (op U) z) ht).trans
    (tensorRightUnitIso_hom_section Y L.val U
      (σ.val.app (op U) (1 : Γ(Y, U))) (c₀.hom.val.app (op U) m))

section FractionalComparison

variable (X : FScheme k) (hX : Properties X)
  [IsIntegral X.left] [IsNoetherian X.left]
  [∀ x : Scheme.ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]

local instance : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩

/-- Literal rational one in the existing pole-bounded fractional module. -/
def fractionalOne (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    DivisorClass.fractionalSections X.left (pointDivisor X p hp n) ⊤ := by
  refine ⟨1, Or.inr ?_⟩
  intro x _
  have h : X.left.ord (1 : X.left.functionField) x.val = 0 :=
    (Divisors.localOrder X.left x).map_zero
  rw [h, zero_add]
  exact pointDivisor_nonneg X p hp n x

@[simp] theorem fractionalOne_val (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    (fractionalOne X p hp n : X.left.functionField) = 1 := rfl

theorem fractionalOne_ne_zero (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) : fractionalOne X p hp n ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg Subtype.val h)

/-- The existing fractional pole module has the original structural field action. -/
instance fractionalPoleSectionsModule (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℤ) :
    Module k (DivisorClass.fractionalSections X.left (pointDivisor X p hp n) ⊤) :=
  Module.compHom _ (Scheme.constants X)

/-- The native divisor-section comparison restricted to the original field action. -/
def divisorSectionsLinearEquiv (p : Spec (.of k) ⟶ X.left)
    (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) :
    (DivisorClass.divisorSheaf X.left (pointDivisor X p hp n)).val.obj (op ⊤) ≃ₗ[k]
      DivisorClass.fractionalSections X.left (pointDivisor X p hp n) ⊤ := by
  let E := DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp n) ⊤
  exact {
    __ := E.toAddEquiv
    map_smul' := fun a s ↦ E.map_smul (Scheme.constants X a) s }

/-- The positive point module admits an actual divisor-sheaf isomorphism
normalized by its original constant-one section. -/
theorem exists_positive_divisorSheafIso
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    ∃ E : (show X.left.Modules from (positiveLineBundle X hX p hp).val) ≅
        (show X.left.Modules from DivisorClass.divisorSheaf X.left (pointDivisor X p hp 1)),
      DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp 1) ⊤
        (E.hom.val.app (op ⊤)
          ((positiveSection X hX p hp).val.app (op ⊤) (1 : Γ(X.left, ⊤)))) =
        fractionalOne X p hp 1 := by
  have hdim : topologicalKrullDim X.left ≤ 1 :=
    (curveProperties_dimension Scheme.smoothFieldDimension hX).le
  let I := idealLineBundle X hX p hp
  let c := Picard.RationalTrivialization.localChart X.left I.val I.property (genericPoint X.left)
  let : Nonempty c.1 := ⟨⟨genericPoint X.left, c.2.property⟩⟩
  let L := positiveLineBundle X hX p hp
  let O := DivisorClass.divisorLineBundle X.left hdim (pointDivisor X p hp 1)
  have hclass : classOf X.left L = classOf X.left O :=
    idealDual_class_eq_point X.left (rationalPoint X p hp) I.property hdim
  obtain ⟨E₀⟩ := (class_eq_iff X.left L O).mp hclass
  let B := DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp 1) ⊤
  let b := B.symm (fractionalOne X p hp 1)
  have hb : b ≠ 0 := by
    intro hb
    have h := congrArg B hb
    rw [B.map_zero] at h
    exact fractionalOne_ne_zero X p hp 1 ((B.apply_symm_apply _).symm.trans h)
  have hs : (positiveSection X hX p hp).val.app (op ⊤) (1 : Γ(X.left, ⊤)) ≠ 0 := by
    intro hs
    apply oneSection_ne_zero X hX p hp
    change (firstPowerIso X hX p hp).inv.val.app (op ⊤)
      ((positiveSection X hX p hp).val.app (op ⊤) (1 : Γ(X.left, ⊤))) = 0
    rw [hs, map_zero]
  have hL : Module.finrank k (L.val.val.obj (op ⊤)) = 1 :=
    (sectionsLinearEquivOfIso X (firstPowerIso X hX p hp)).finrank_eq.symm.trans
      (sections_finrank X hX p hp hg 1 (by omega))
  obtain ⟨E, hE⟩ := exists_normalized_point_iso X L O (positiveSection X hX p hp) hs b hb hL E₀
  exact ⟨E, (congrArg B hE).trans (B.apply_symm_apply _)⟩

/-- A sheaf isomorphism fixed by the original section one, not a choice of
vector-space coordinates. -/
def positiveDivisorIso (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    (show X.left.Modules from (positiveLineBundle X hX p hp).val) ≅
      (show X.left.Modules from DivisorClass.divisorSheaf X.left (pointDivisor X p hp 1)) :=
  (exists_positive_divisorSheafIso X hX p hp hg).choose

theorem positiveDivisorIso_one (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp 1) ⊤
      ((positiveDivisorIso X hX p hp hg).hom.val.app (op ⊤)
        ((positiveSection X hX p hp).val.app (op ⊤) (1 : Γ(X.left, ⊤)))) =
      fractionalOne X p hp 1 :=
  (exists_positive_divisorSheafIso X hX p hp hg).choose_spec

/-- The fractional constant-one map, as an actual structure-module morphism. -/
def fractionalOneMap (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) :
    (show X.left.Modules from SheafOfModules.unit X.left.ringCatSheaf) ⟶
      (show X.left.Modules from DivisorClass.divisorSheaf X.left (pointDivisor X p hp 1)) :=
  (unitHomGlobalSectionsEquiv X.left _).symm
    ((DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp 1) ⊤).symm
      (fractionalOne X p hp 1))

/-- Normalization is equality of the actual sheaf maps on all opens. -/
theorem positiveSection_comp_positiveDivisorIso
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    positiveSection X hX p hp ≫ (positiveDivisorIso X hX p hp hg).hom =
      fractionalOneMap X p hp := by
  apply (unitHomGlobalSectionsEquiv X.left _).injective
  apply (DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp 1) ⊤).injective
  change _ = DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp 1) ⊤
    (unitHomGlobalSectionsEquiv X.left _ (fractionalOneMap X p hp))
  rw [fractionalOneMap, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact positiveDivisorIso_one X hX p hp hg

/-- The normalized first intrinsic pole space is the actual fractional
pole space at the original point, with its original field action. -/
def firstSectionsFractionalEquiv
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    sections X hX p hp 1 ≃ₗ[k]
      DivisorClass.fractionalSections X.left (pointDivisor X p hp 1) ⊤ :=
  (sectionsLinearEquivOfIso X
    (firstPowerIso X hX p hp ≪≫ positiveDivisorIso X hX p hp hg)).trans
      (divisorSectionsLinearEquiv X p hp 1)

theorem firstSectionsFractionalEquiv_one
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    firstSectionsFractionalEquiv X hX p hp hg (oneSection X hX p hp) =
      fractionalOne X p hp 1 := by
  change DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp 1) ⊤
    ((positiveDivisorIso X hX p hp hg).hom.val.app (op ⊤)
      ((firstPowerIso X hX p hp).hom.val.app (op ⊤) (oneSection X hX p hp))) = _
  rw [firstPowerIso_oneSection]
  exact positiveDivisorIso_one X hX p hp hg

/-- Actual tensor powers identify with the original point's divisor
sheaves. The first power uses the original tensor-unit comparison. -/
def poleDivisorIso (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) :
    (show X.left.Modules from (poleLineBundle X hX p hp n).val) ≅
      (show X.left.Modules from DivisorClass.divisorSheaf X.left (pointDivisor X p hp n)) :=
  tensorPowerPointDivisorIso X.left
    (curveProperties_dimension Scheme.smoothFieldDimension hX).le
    (positiveLineBundle X hX p hp) (closedPoint X p hp) (positiveDivisorIso X hX p hp hg) n

theorem poleDivisorIso_one (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    poleDivisorIso X hX p hp hg 1 =
      firstPowerIso X hX p hp ≪≫ positiveDivisorIso X hX p hp hg := rfl

theorem poleDivisorIso_add_two (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) :
    poleDivisorIso X hX p hp hg (n + 2) =
      tensorSheafIso X.left (positiveDivisorIso X hX p hp hg)
        (poleDivisorIso X hX p hp hg (n + 1)) ≪≫
      DivisorClass.divisorTensorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le
        (pointDivisor X p hp 1) (pointDivisor X p hp ((n + 1 : ℕ) : ℤ)) ≪≫
      eqToIso (congrArg (DivisorClass.divisorSheaf X.left)
        (pointDivisor_one_add X p hp (n + 1))) := rfl

/-- Original global sections and existing fractional sections are linearly
equivalent through the actual normalized module-sheaf comparison. -/
def sectionsFractionalEquiv
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) :
    sections X hX p hp n ≃ₗ[k]
      DivisorClass.fractionalSections X.left (pointDivisor X p hp n) ⊤ :=
  (sectionsLinearEquivOfIso X (poleDivisorIso X hX p hp hg n)).trans
    (divisorSectionsLinearEquiv X p hp n)

theorem sectionsFractionalEquiv_val
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (s : sections X hX p hp n) :
    (sectionsFractionalEquiv X hX p hp hg n s : X.left.functionField) =
      Scheme.Modules.RationalFunctions.rationalValue X.left ⊤
        ((poleDivisorIso X hX p hp hg n).hom.val.app (op ⊤) s).val := rfl

theorem sectionsFractionalEquiv_one
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) :
    sectionsFractionalEquiv X hX p hp hg 1 (oneSection X hX p hp) =
      fractionalOne X p hp 1 := by
  apply Subtype.ext
  rw [sectionsFractionalEquiv_val, poleDivisorIso_one]
  change Scheme.Modules.RationalFunctions.rationalValue X.left ⊤
    ((positiveDivisorIso X hX p hp hg).hom.val.app (op ⊤)
      ((firstPowerIso X hX p hp).hom.val.app (op ⊤) (oneSection X hX p hp))).val = 1
  rw [firstPowerIso_oneSection]
  exact congrArg Subtype.val (positiveDivisorIso_one X hX p hp hg)

private theorem divisorSheaf_eqToIso_value {D E : Divisor X.left} (h : D = E)
    (U : X.left.Opens) [Nonempty U]
    (s : (DivisorClass.divisorSheaf X.left D).val.obj (op U)) :
    Scheme.Modules.RationalFunctions.rationalValue X.left U
        ((eqToIso (congrArg (DivisorClass.divisorSheaf X.left) h)).hom.val.app (op U) s).val =
      Scheme.Modules.RationalFunctions.rationalValue X.left U s.val := by
  cases h
  rfl

private theorem divisorTensorIso_tensorSection
    (D E : Divisor X.left) (U : X.left.Opens)
    (s : (DivisorClass.divisorSheaf X.left D).val.obj (op U))
    (t : (DivisorClass.divisorSheaf X.left E).val.obj (op U)) :
    (DivisorClass.divisorTensorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le D E).hom.val.app (op U)
      (moduleTensorSection X.left _ _ U s t) =
        DivisorClass.divisorMultiplySections X.left D E U s t := by
  rw [DivisorClass.divisorTensorIso_hom]
  have hh := (PresheafOfModules.sheafificationHomEquiv
    (R := X.left.ringCatSheaf)
    (P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.left.presheaf)
      (DivisorClass.divisorSheaf X.left D).val (DivisorClass.divisorSheaf X.left E).val)
    (F := DivisorClass.divisorSheaf X.left (D + E))
    (𝟙 X.left.ringCatSheaf.obj)).apply_symm_apply
      (DivisorClass.divisorMultiplicationPresheaf X.left D E)
  exact congrArg (fun g ↦ g.app (op U) (s ⊗ₜ t)) hh

private theorem poleDivisorIso_tensorSection_value
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ)
    (s : (positiveLineBundle X hX p hp).val.val.obj (op ⊤))
    (t : sections X hX p hp (n + 1)) :
    (sectionsFractionalEquiv X hX p hp hg (n + 2)
        (moduleTensorSection X.left (positiveLineBundle X hX p hp).val
          (poleLineBundle X hX p hp (n + 1)).val ⊤ s t) : X.left.functionField) =
      ((DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp 1) ⊤
        ((positiveDivisorIso X hX p hp hg).hom.val.app (op ⊤) s)) : X.left.functionField) *
        (sectionsFractionalEquiv X hX p hp hg (n + 1) t : X.left.functionField) := by
  simp only [sectionsFractionalEquiv_val]
  rw [poleDivisorIso_add_two]
  simp only [Iso.trans_hom, module_comp_app]
  rw [divisorSheaf_eqToIso_value X (pointDivisor_one_add X p hp (n + 1)) ⊤]
  let D := pointDivisor X p hp 1
  let E := pointDivisor X p hp ((n + 1 : ℕ) : ℤ)
  let s' := (positiveDivisorIso X hX p hp hg).hom.val.app (op ⊤) s
  let t' := (poleDivisorIso X hX p hp hg (n + 1)).hom.val.app (op ⊤) t
  have ht := tensorSheafIso_section X.left (positiveDivisorIso X hX p hp hg)
    (poleDivisorIso X hX p hp hg (n + 1)) ⊤ s t
  have hm := divisorTensorIso_tensorSection X hX D E ⊤ s' t'
  calc
    _ = Scheme.Modules.RationalFunctions.rationalValue X.left ⊤
        ((DivisorClass.divisorTensorIso X.left
          (curveProperties_dimension Scheme.smoothFieldDimension hX).le D E).hom.val.app
            (op ⊤) (moduleTensorSection X.left _ _ ⊤ s' t')).val :=
      congrArg (fun z ↦ Scheme.Modules.RationalFunctions.rationalValue X.left ⊤
        ((DivisorClass.divisorTensorIso X.left
          (curveProperties_dimension Scheme.smoothFieldDimension hX).le D E).hom.val.app
            (op ⊤) z).val) ht
    _ = Scheme.Modules.RationalFunctions.rationalValue X.left ⊤
        (DivisorClass.divisorMultiplySections X.left D E ⊤ s' t').val :=
      congrArg (fun z ↦ Scheme.Modules.RationalFunctions.rationalValue X.left ⊤ z.val) hm
    _ = _ := DivisorClass.divisorMultiplySections_value X.left D E ⊤ s' t'

/-- The original n-to-n+1 inclusion preserves the actual rational value
for every positive pole bound. -/
theorem sectionsFractionalEquiv_inclusion_succ_value
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (s : sections X hX p hp (n + 1)) :
    (sectionsFractionalEquiv X hX p hp hg (n + 2)
      (sectionsInclusion X hX p hp (n + 1) s) : X.left.functionField) =
        (sectionsFractionalEquiv X hX p hp hg (n + 1) s : X.left.functionField) := by
  have h : sectionsInclusion X hX p hp (n + 1) s =
      moduleTensorSection X.left (positiveLineBundle X hX p hp).val
        (poleLineBundle X hX p hp (n + 1)).val ⊤
        ((positiveSection X hX p hp).val.app (op ⊤) (1 : Γ(X.left, ⊤))) s := by
    change (tensorSheafMap X.left (positiveSection X hX p hp) (𝟙 _)).val.app (op ⊤)
      ((tensorSheafLeftUnit X.left _).inv.val.app (op ⊤) s) = _
    rw [tensorSheafLeftUnit_inv_section, tensorSheafMap_section]
    rfl
  rw [h, poleDivisorIso_tensorSection_value, positiveDivisorIso_one, fractionalOne_val, one_mul]

/-- The existing fractional module's structural scalar acts through the
original function-field constants map. -/
theorem fractionalSections_smul_val
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _) (n : ℕ) (a : k)
    (s : DivisorClass.fractionalSections X.left (pointDivisor X p hp n) ⊤) :
    ((a • s : DivisorClass.fractionalSections X.left (pointDivisor X p hp n) ⊤) :
      X.left.functionField) = Scheme.functionFieldConstants X.left X.hom a * s.val := rfl

/-- The actual normalized section-to-function-field linear map, retaining
the original structural constants. -/
def sectionsToFunctionField
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) :
    letI := Scheme.functionFieldConstantsAlgebra X.left X.hom
    sections X hX p hp n →ₗ[k] X.left.functionField := by
  letI := Scheme.functionFieldConstantsAlgebra X.left X.hom
  exact {
    toFun := fun s ↦ (sectionsFractionalEquiv X hX p hp hg n s).val
    map_add' := fun s t ↦ by rw [map_add]; rfl
    map_smul' := fun a s ↦ by
      rw [LinearEquiv.map_smul]
      exact fractionalSections_smul_val X p hp n a _ }

theorem sectionsToFunctionField_injective
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) :
    Function.Injective (sectionsToFunctionField X hX p hp hg n) :=
  Subtype.val_injective.comp (sectionsFractionalEquiv X hX p hp hg n).injective

theorem mem_range_sectionsToFunctionField_iff
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (f : X.left.functionField) :
    letI := Scheme.functionFieldConstantsAlgebra X.left X.hom
    f ∈ (sectionsToFunctionField X hX p hp hg n).range ↔
      DivisorClass.IsFractionalSection X.left (pointDivisor X p hp n) ⊤ f := by
  let := Scheme.functionFieldConstantsAlgebra X.left X.hom
  constructor
  · rintro ⟨s, rfl⟩
    exact (sectionsFractionalEquiv X hX p hp hg n s).property
  · intro hf
    exact ⟨(sectionsFractionalEquiv X hX p hp hg n).symm ⟨f, hf⟩,
      congrArg Subtype.val ((sectionsFractionalEquiv X hX p hp hg n).apply_symm_apply _)⟩

private theorem poleDivisorIso_zero_value
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (s : sections X hX p hp 0) :
    (sectionsFractionalEquiv X hX p hp hg 0 s : X.left.functionField) =
      X.left.germToFunctionField ⊤
        ((Limits.coproductUniqueIso
          (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.left.ringCatSheaf)).hom.val.app
            (op ⊤) s) := by
  rw [sectionsFractionalEquiv_val]
  exact (DivisorClass.sectionTrivialization_value X.left
    (curveProperties_dimension Scheme.smoothFieldDimension hX).le
    (pointDivisor X p hp 0) ⊤ 1 _ _).trans (one_mul _)

/-- Even the original zero-to-one inclusion keeps its original rational value. -/
theorem sectionsFractionalEquiv_inclusion_zero_value
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (s : sections X hX p hp 0) :
    (sectionsFractionalEquiv X hX p hp hg 1
      (sectionsInclusion X hX p hp 0 s) : X.left.functionField) =
        (sectionsFractionalEquiv X hX p hp hg 0 s : X.left.functionField) := by
  let c₀ := Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.left.ringCatSheaf)
  let a : Γ(X.left, ⊤) := c₀.hom.val.app (op ⊤) s
  let t := (positiveSection X hX p hp).val.app (op ⊤) (1 : Γ(X.left, ⊤))
  have hfirst : (firstPowerIso X hX p hp).hom.val.app (op ⊤)
      (sectionsInclusion X hX p hp 0 s) = a • t :=
    firstTensorPowerIso_inclusion X.left (positiveLineBundle X hX p hp)
      (positiveSection X hX p hp) ⊤ s
  rw [poleDivisorIso_zero_value, sectionsFractionalEquiv_val, poleDivisorIso_one]
  simp only [Iso.trans_hom, module_comp_app]
  change ((DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp 1) ⊤
    ((positiveDivisorIso X hX p hp hg).hom.val.app (op ⊤)
      ((firstPowerIso X hX p hp).hom.val.app (op ⊤)
        (sectionsInclusion X hX p hp 0 s)))) : X.left.functionField) = _
  rw [hfirst, ((positiveDivisorIso X hX p hp hg).hom.val.app (op ⊤)).hom.map_smul a t,
    (DivisorClass.explicitSheafSectionsEquiv X.left (pointDivisor X p hp 1) ⊤).map_smul,
    positiveDivisorIso_one]
  change X.left.germToFunctionField ⊤ a * 1 = X.left.germToFunctionField ⊤ a
  exact mul_one _

/-- Every original n-to-n+1 pole inclusion preserves its actual rational value. -/
theorem sectionsFractionalEquiv_inclusion_value
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (n : ℕ) (s : sections X hX p hp n) :
    (sectionsFractionalEquiv X hX p hp hg (n + 1)
      (sectionsInclusion X hX p hp n s) : X.left.functionField) =
        (sectionsFractionalEquiv X hX p hp hg n s : X.left.functionField) := by
  cases n with
  | zero => exact sectionsFractionalEquiv_inclusion_zero_value X hX p hp hg s
  | succ n => exact sectionsFractionalEquiv_inclusion_succ_value X hX p hp hg n s


end FractionalComparison

end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor
