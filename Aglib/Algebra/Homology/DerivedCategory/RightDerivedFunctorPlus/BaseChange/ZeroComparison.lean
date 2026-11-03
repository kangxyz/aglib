/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroNormalization
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology.Coherence
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.Complex
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonSquares

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.UnitComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.NatTrans

/-! # Native single-unit and zeroth exchange transport -/
@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Functor
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

section SingleUnit
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] (F : A ⥤ B) [F.Additive]

/-- Only an abbreviation for the original single map followed by the actual unit. -/
def rightDerivedSingleUnit (M : A) :
    (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj M) ⟶
      F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M) :=
  DerivedCategory.Plus.Q.map
    (show (CochainComplex.singleFunctorPlus B 0).obj (F.obj M) ⟶
        F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj M) from
      ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)) ≫
      F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus A 0).obj M)

private theorem single_homology_comparison (M : B) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app M =
      (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).hom.app
        ((CochainComplex.singleFunctorPlus B 0).obj M) ≫
      (singleObjHomologySelfIso (.up ℤ) 0 M).hom := by
  dsimp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.Plus.homologyFunctorFactors,
    DerivedCategory.singleFunctorsPostcompQIso, DerivedCategory.Plus.QCompιIso,
    ObjectProperty.liftCompιIso]
  let Z := (single B (.up ℤ) 0).obj M
  let V := DerivedCategory.Q.obj Z
  let H := DerivedCategory.homologyFunctor B 0
  let h := (DerivedCategory.homologyFunctorFactors B 0).hom.app Z
  let e := (singleObjHomologySelfIso (.up ℤ) 0 M).hom
  change H.map (𝟙 V) ≫ 𝟙 (H.obj V) ≫ h ≫ e =
    (𝟙 (H.obj V) ≫ H.map (𝟙 V) ≫ 𝟙 (H.obj V) ≫ h) ≫ e
  simp only [Functor.map_id, Category.id_comp]

/-- Homology normalization of the literal single-unit morphism. -/
theorem rightDerivedSingleUnit_homology (M : A) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app (F.obj M) ≫
      (DerivedCategory.Plus.homologyFunctor B 0).map (F.rightDerivedSingleUnit M) =
    F.toRightDerivedZero.app M ≫ (F.rightDerivedSingleHomologyIso 0).hom.app M := by
  let K := (CochainComplex.singleFunctorPlus A 0).obj M
  let T := (CochainComplex.singleFunctorPlus B 0).obj (F.obj M)
  let S := F.mapCochainComplexPlus.obj K
  let σ : T ⟶ S := ObjectProperty.homMk
    ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  let P₀ := (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).app T
  let P₁ := (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).app S
  let H := DerivedCategory.Plus.homologyFunctor B 0
  have hd : (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app (F.obj M) =
      (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫ P₀.inv := by
    apply (cancel_mono ((DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app
      (F.obj M))).mp
    rw [Iso.inv_hom_id_app, single_homology_comparison]
    simp only [Category.assoc]
    change 𝟙 _ = (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      P₀.inv ≫ P₀.hom ≫ (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).hom
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  have hp : P₀.inv ≫ H.map (DerivedCategory.Plus.Q.map σ) =
      homologyMap ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) 0 ≫ P₁.inv := by
    apply (cancel_mono P₁.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h := (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).hom.naturality σ
    change H.map (DerivedCategory.Plus.Q.map σ) ≫ P₁.hom =
      P₀.hom ≫ homologyMap ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) 0 at h
    rw [h]
    simp only [Iso.inv_hom_id_assoc]
  rw [rightDerivedSingleUnit, Functor.map_comp, hd]
  change ((singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫ P₀.inv) ≫
    H.map (DerivedCategory.Plus.Q.map σ) ≫ H.map (F.rightDerivedFunctorPlusUnit.app K) = _
  rw [Category.assoc, ← Category.assoc P₀.inv, hp]
  simpa only [K, S, P₁, H, Iso.app_inv, Category.assoc] using
    (F.rightDerivedSingleHomologyIso_unit_zero M).symm

/-- Left exactness is used only to identify R0 with the original functor. -/
theorem rightDerivedSingleUnit_homology_zero [PreservesFiniteLimits F] (M : A) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app (F.obj M) ≫
      (DerivedCategory.Plus.homologyFunctor B 0).map (F.rightDerivedSingleUnit M) =
    F.rightDerivedSingleHomologyZeroIso.inv.app M := by
  rw [rightDerivedSingleUnit_homology, rightDerivedSingleHomologyZeroIso_inv,
    NatTrans.comp_app]

end SingleUnit

section Exchange
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  [EnoughInjectives D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits R₁] [PreservesFiniteLimits R₂]
  [G.PreservesHomology] [H.PreservesHomology]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂)
  (β : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
    H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)

/-- The literal degreewise transformation, including native composition maps. -/
def exchangeOnComplexes : R₁.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ⟶
    H.mapCochainComplexPlus ⋙ R₂.mapCochainComplexPlus :=
  (mapCochainComplexPlusCompIso R₁ G).inv ≫ α.mapCochainComplexPlus ≫
    (mapCochainComplexPlusCompIso H R₂).hom

omit [HasDerivedCategory A] [EnoughInjectives A]
  [HasDerivedCategory B] [EnoughInjectives B] [HasDerivedCategory C]
  [HasDerivedCategory D] [EnoughInjectives D]
  [PreservesFiniteLimits R₁] [PreservesFiniteLimits R₂]
  [G.PreservesHomology] [H.PreservesHomology] in
/-- Native single maps commute with the actual termwise exchange. -/
private theorem exchangeOnComplexes_single (M : B) :
    G.mapCochainComplexPlus.map
      (show (CochainComplex.singleFunctorPlus A 0).obj (R₁.obj M) ⟶
          R₁.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus B 0).obj M) from
        ObjectProperty.homMk ((singleMapHomologicalComplex R₁ (.up ℤ) 0).inv.app M)) ≫
      (exchangeOnComplexes R₁ R₂ G H α).app ((CochainComplex.singleFunctorPlus B 0).obj M) ≫
      R₂.mapCochainComplexPlus.map
        (show H.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus B 0).obj M) ⟶
            (CochainComplex.singleFunctorPlus D 0).obj (H.obj M) from
          ObjectProperty.homMk ((singleMapHomologicalComplex H (.up ℤ) 0).hom.app M)) =
    (show G.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj (R₁.obj M)) ⟶
        (CochainComplex.singleFunctorPlus C 0).obj (G.obj (R₁.obj M)) from
      ObjectProperty.homMk ((singleMapHomologicalComplex G (.up ℤ) 0).hom.app (R₁.obj M))) ≫
      (CochainComplex.singleFunctorPlus C 0).map (α.app M) ≫
      (show (CochainComplex.singleFunctorPlus C 0).obj (R₂.obj (H.obj M)) ⟶
          R₂.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus D 0).obj (H.obj M)) from
        ObjectProperty.homMk
          ((singleMapHomologicalComplex R₂ (.up ℤ) 0).inv.app (H.obj M))) := by
  apply ObjectProperty.hom_ext
  ext i
  by_cases hi : i = 0
  · subst i
    simp [exchangeOnComplexes, mapCochainComplexPlusCompIso,
      singleMapHomologicalComplex_hom_app_self, singleMapHomologicalComplex_inv_app_self,
      singleObjXSelf, singleObjXIsoOfEq, CochainComplex.singleFunctorPlus,
      CochainComplex.singleFunctor, NatTrans.mapCochainComplexPlus_app_f,
      ObjectProperty.lift, HomologicalComplex.single]
  · exact (G.map_isZero (isZero_single_obj_X (.up ℤ) 0 (R₁.obj M) i hi)).eq_of_src _ _

omit [PreservesFiniteLimits R₁] [PreservesFiniteLimits R₂] in
/-- The original complex-unit square implies the required single-unit square.
Only the exact horizontal functors' units are cancelled. -/
theorem singleUnit_square_of_complexUnit (M : B)
    (hunit : ∀ K : CochainComplex.Plus B,
      G.rightDerivedFunctorPlus.map (R₁.rightDerivedFunctorPlusUnit.app K) ≫
        β.app (DerivedCategory.Plus.Q.obj K) ≫
        R₂.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K) =
      G.rightDerivedFunctorPlusExactComparison.hom.app (R₁.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.Q.map ((exchangeOnComplexes R₁ R₂ G H α).app K) ≫
        R₂.rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K)) :
    G.rightDerivedFunctorPlus.map (R₁.rightDerivedSingleUnit M) ≫
        β.app ((DerivedCategory.Plus.singleFunctor B 0).obj M) ≫
        R₂.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M) =
      (G.rightDerivedFunctorPlusSingleIso 0).hom.app (R₁.obj M) ≫
        (DerivedCategory.Plus.singleFunctor C 0).map (α.app M) ≫
        R₂.rightDerivedSingleUnit (H.obj M) := by
  let K := (CochainComplex.singleFunctorPlus B 0).obj M
  let KR := (CochainComplex.singleFunctorPlus A 0).obj (R₁.obj M)
  let KH := (CochainComplex.singleFunctorPlus D 0).obj (H.obj M)
  let τ : KR ⟶ R₁.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((singleMapHomologicalComplex R₁ (.up ℤ) 0).inv.app M)
  let σ : H.mapCochainComplexPlus.obj K ⟶ KH :=
    ObjectProperty.homMk ((singleMapHomologicalComplex H (.up ℤ) 0).hom.app M)
  let Q : CochainComplex.Plus C ⥤ DerivedCategory.Plus C := DerivedCategory.Plus.Q
  have hH : (H.rightDerivedFunctorPlusSingleIso 0).hom.app M =
      H.rightDerivedFunctorPlusExactComparison.hom.app K ≫ DerivedCategory.Plus.Q.map σ := by
    let : IsIso H.rightDerivedFunctorPlusUnit :=
      H.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    apply (cancel_epi (H.rightDerivedFunctorPlusUnit.app K)).mp
    rw [H.rightDerivedFunctorPlusSingleIso_unit]
    have hi := H.rightDerivedFunctorPlusExactComparison.inv_hom_id_app K
    change H.rightDerivedFunctorPlusUnit.app K ≫
      H.rightDerivedFunctorPlusExactComparison.hom.app K = 𝟙 _ at hi
    rw [← Category.assoc, hi, Category.id_comp]
  let : IsIso G.rightDerivedFunctorPlusUnit :=
    G.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  apply (cancel_epi (G.rightDerivedFunctorPlusUnit.app KR)).mp
  rw [rightDerivedSingleUnit, G.rightDerivedFunctorPlus.map_comp, hH,
    R₂.rightDerivedFunctorPlus.map_comp]
  simp only [Category.assoc]
  have hG := G.rightDerivedFunctorPlusUnit.naturality τ
  change Q.map (G.mapCochainComplexPlus.map τ) ≫
      G.rightDerivedFunctorPlusUnit.app (R₁.mapCochainComplexPlus.obj K) =
    G.rightDerivedFunctorPlusUnit.app KR ≫
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map τ) at hG
  rw [← Category.assoc (G.rightDerivedFunctorPlusUnit.app KR), ← hG]
  simp only [Category.assoc]
  erw [reassoc_of% hunit K]
  have hi := G.rightDerivedFunctorPlusExactComparison.inv_hom_id_app
    (R₁.mapCochainComplexPlus.obj K)
  change G.rightDerivedFunctorPlusUnit.app (R₁.mapCochainComplexPlus.obj K) ≫
    G.rightDerivedFunctorPlusExactComparison.hom.app
      (R₁.mapCochainComplexPlus.obj K) = 𝟙 _ at hi
  rw [← Category.assoc (G.rightDerivedFunctorPlusUnit.app _), hi, Category.id_comp]
  have hR := R₂.rightDerivedFunctorPlusUnit.naturality σ
  simp only [Functor.comp_map] at hR
  erw [← hR]
  erw [reassoc_of% G.rightDerivedFunctorPlusSingleIso_unit 0 (R₁.obj M)]
  simp only [rightDerivedSingleUnit]
  have hc := congrArg Q.map (exchangeOnComplexes_single R₁ R₂ G H α M)
  simp only [Functor.map_comp] at hc
  have hc' := congrArg (fun z => z ≫ R₂.rightDerivedFunctorPlusUnit.app KH) hc
  simp only [Category.assoc] at hc'
  exact hc'

/-- The exact five native factors defining the degree-zero transported exchange. -/
def higherExchangeZero (M : B) : G.obj ((R₁.rightDerived 0).obj M) ⟶
    (R₂.rightDerived 0).obj (H.obj M) :=
  G.map ((R₁.rightDerivedSingleHomologyIso 0).hom.app M) ≫
    (G.rightDerivedFunctorPlusHomologyIso 0).inv.app
      (R₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M)) ≫
    (DerivedCategory.Plus.homologyFunctor C 0).map
      (β.app ((DerivedCategory.Plus.singleFunctor B 0).obj M)) ≫
    (DerivedCategory.Plus.homologyFunctor C 0).map
      (R₂.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
    (R₂.rightDerivedSingleHomologyIso 0).inv.app (H.obj M)

/-- Conditional single-unit form of the q0 comparison. The premise must be derived
from the literal complex-unit square, not assumed for a newly chosen exchange. -/
theorem higherExchangeZero_normalization_of_singleUnit (M : B)
    (h : G.rightDerivedFunctorPlus.map (R₁.rightDerivedSingleUnit M) ≫
        β.app ((DerivedCategory.Plus.singleFunctor B 0).obj M) ≫
        R₂.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M) =
      (G.rightDerivedFunctorPlusSingleIso 0).hom.app (R₁.obj M) ≫
        (DerivedCategory.Plus.singleFunctor C 0).map (α.app M) ≫
        R₂.rightDerivedSingleUnit (H.obj M)) :
    G.map (R₁.rightDerivedZeroIsoSelf.hom.app M) ≫ α.app M =
      higherExchangeZero R₁ R₂ G H β M ≫ R₂.rightDerivedZeroIsoSelf.hom.app (H.obj M) := by
  let s := (DerivedCategory.Plus.singleFunctor B 0).obj M
  let k := (DerivedCategory.Plus.singleFunctor A 0).obj (R₁.obj M)
  let HC := DerivedCategory.Plus.homologyFunctor C 0
  let HA := DerivedCategory.Plus.homologyFunctor A 0
  let dA := (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app (R₁.obj M)
  let dC := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app (G.obj (R₁.obj M))
  let dC' := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app (R₂.obj (H.obj M))
  let E := G.rightDerivedFunctorPlusHomologyIso 0
  let r₁ := R₁.rightDerivedSingleHomologyZeroIso.app M
  let r₂ := R₂.rightDerivedSingleHomologyZeroIso.app (H.obj M)
  let b := HC.map (β.app s)
  let t := HC.map (R₂.rightDerivedFunctorPlus.map
    ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M))
  have hG : G.map dA.inv ≫ E.inv.app k ≫
      HC.map ((G.rightDerivedFunctorPlusSingleIso 0).hom.app (R₁.obj M)) = dC.inv := by
    apply (cancel_mono dC.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id]
    have hcoh := G.rightDerivedFunctorPlusSingleIso_homology 0 (R₁.obj M)
    change HC.map ((G.rightDerivedFunctorPlusSingleIso 0).hom.app (R₁.obj M)) ≫ dC.hom =
      E.hom.app k ≫ G.map dA.hom at hcoh
    erw [hcoh]
    simp only [Iso.inv_hom_id_app_assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id]
  have hn := E.inv.naturality (R₁.rightDerivedSingleUnit M)
  change G.map (HA.map (R₁.rightDerivedSingleUnit M)) ≫
      E.inv.app (R₁.rightDerivedFunctorPlus.obj s) =
    E.inv.app k ≫ HC.map (G.rightDerivedFunctorPlus.map (R₁.rightDerivedSingleUnit M)) at hn
  have hs : G.map r₁.inv ≫ E.inv.app (R₁.rightDerivedFunctorPlus.obj s) =
      G.map dA.inv ≫ E.inv.app k ≫
        HC.map (G.rightDerivedFunctorPlus.map (R₁.rightDerivedSingleUnit M)) := by
    have hu : dA.inv ≫ HA.map (R₁.rightDerivedSingleUnit M) = r₁.inv :=
      R₁.rightDerivedSingleUnit_homology_zero M
    erw [← hu, G.map_comp, Category.assoc, hn]
  have hh := congrArg HC.map h
  simp only [Functor.map_comp] at hh
  have hd := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.naturality (α.app M)
  change HC.map ((DerivedCategory.Plus.singleFunctor C 0).map (α.app M)) ≫ dC'.hom =
    dC.hom ≫ α.app M at hd
  have hd' : dC.inv ≫ HC.map ((DerivedCategory.Plus.singleFunctor C 0).map (α.app M)) =
      α.app M ≫ dC'.inv := by
    apply (cancel_mono dC'.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [hd]
    simp only [Iso.inv_hom_id_assoc]
  have hz : G.map r₁.inv ≫ E.inv.app (R₁.rightDerivedFunctorPlus.obj s) ≫ b ≫ t =
      α.app M ≫ r₂.inv := by
    rw [← Category.assoc (G.map r₁.inv), hs]
    simp only [Category.assoc]
    rw [hh]
    erw [reassoc_of% hG, reassoc_of% hd']
    have hu : dC'.inv ≫ HC.map (R₂.rightDerivedSingleUnit (H.obj M)) = r₂.inv :=
      R₂.rightDerivedSingleUnit_homology_zero (H.obj M)
    erw [hu]
  have hz' : G.map r₁.hom ≫ α.app M =
      E.inv.app (R₁.rightDerivedFunctorPlus.obj s) ≫ b ≫ t ≫ r₂.hom := by
    apply (cancel_epi (G.map r₁.inv)).mp
    simp only [← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp]
    have hz₂ := congrArg (fun z => z ≫ r₂.hom) hz
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hz₂.symm
  have hf₁ := congrArg (fun z => G.map z)
    (congrArg (fun z => z.app M) (R₁.rightDerivedSingleHomologyZeroIso_hom_comp))
  have hf₂ := congrArg (fun z => z.app (H.obj M))
    (R₂.rightDerivedSingleHomologyZeroIso_hom_comp)
  simp only [NatTrans.comp_app, G.map_comp] at hf₁ hf₂
  change G.map ((R₁.rightDerivedSingleHomologyIso 0).hom.app M) ≫ G.map r₁.hom =
    G.map (R₁.rightDerivedZeroIsoSelf.hom.app M) at hf₁
  change (R₂.rightDerivedSingleHomologyIso 0).hom.app (H.obj M) ≫ r₂.hom =
    R₂.rightDerivedZeroIsoSelf.hom.app (H.obj M) at hf₂
  have hr₂ : r₂.hom = (R₂.rightDerivedSingleHomologyIso 0).inv.app (H.obj M) ≫
      R₂.rightDerivedZeroIsoSelf.hom.app (H.obj M) := by
    apply (cancel_epi ((R₂.rightDerivedSingleHomologyIso 0).hom.app (H.obj M))).mp
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hf₂
  rw [← hf₁, Category.assoc, hz', hr₂]
  simp only [higherExchangeZero, E, s, b, t, HC, Category.assoc]

/-- The five-factor transport of the actual derived exchange recovers the
original ordinary transformation in degree zero, under the original R0 isos. -/
theorem higherExchangeZero_normalization (M : B)
    (hunit : ∀ K : CochainComplex.Plus B,
      G.rightDerivedFunctorPlus.map (R₁.rightDerivedFunctorPlusUnit.app K) ≫
        β.app (DerivedCategory.Plus.Q.obj K) ≫
        R₂.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K) =
      G.rightDerivedFunctorPlusExactComparison.hom.app (R₁.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.Q.map ((exchangeOnComplexes R₁ R₂ G H α).app K) ≫
        R₂.rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K)) :
    G.map (R₁.rightDerivedZeroIsoSelf.hom.app M) ≫ α.app M =
      higherExchangeZero R₁ R₂ G H β M ≫ R₂.rightDerivedZeroIsoSelf.hom.app (H.obj M) :=
  higherExchangeZero_normalization_of_singleUnit R₁ R₂ G H α β M
    (singleUnit_square_of_complexUnit R₁ R₂ G H α β M hunit)

/-- The literal ordinary-versus-derived zero comparison, with the actual
transported morphism kept as a parameter for concrete specialization. -/
def HigherExchangeZeroEquation (M : B)
    (b : G.obj ((R₁.rightDerived 0).obj M) ⟶ (R₂.rightDerived 0).obj (H.obj M)) : Prop :=
  G.map (R₁.rightDerivedZeroIsoSelf.hom.app M) ≫ α.app M =
    b ≫ R₂.rightDerivedZeroIsoSelf.hom.app (H.obj M)

/-- Substitution of an explicitly identified actual transport map takes place
in the generic category, rather than constructing a large concrete rewrite motive. -/
theorem higherExchangeZero_normalization_of_eq (M : B)
    (b : G.obj ((R₁.rightDerived 0).obj M) ⟶ (R₂.rightDerived 0).obj (H.obj M))
    (hb : higherExchangeZero R₁ R₂ G H β M = b)
    (hunit : ∀ K : CochainComplex.Plus B,
      G.rightDerivedFunctorPlus.map (R₁.rightDerivedFunctorPlusUnit.app K) ≫
        β.app (DerivedCategory.Plus.Q.obj K) ≫
        R₂.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K) =
      G.rightDerivedFunctorPlusExactComparison.hom.app (R₁.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.Q.map ((exchangeOnComplexes R₁ R₂ G H α).app K) ≫
        R₂.rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K)) :
    HigherExchangeZeroEquation R₁ R₂ G H α M b := by
  subst b
  exact higherExchangeZero_normalization R₁ R₂ G H α β M hunit

end Exchange
end CategoryTheory.Functor


namespace CategoryTheory

open TwoSquare

universe uA vA wA uB vB wB uC vC wC uD vD wD
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  [EnoughInjectives D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
  {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  [G.Additive] [H.Additive] [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
  [G.PreservesHomology] [H.PreservesHomology]
  [L₁.PreservesHomology] [L₂.PreservesHomology]
  [PreservesFiniteLimits R₁] [PreservesFiniteLimits R₂]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  (α : TwoSquare G L₁ L₂ H)
  (αD : TwoSquare G.rightDerivedFunctorPlus L₁.rightDerivedFunctorPlus
    L₂.rightDerivedFunctorPlus H.rightDerivedFunctorPlus)

/-- Both canonical input predicates are unfolded only in the generic category.
The concrete consumer passes its original unit and five-factor component theorems
without constructing any expanded sheaf-category rewrite motive. -/
theorem higherExchangeZero_normalization_of_mate_transport
    (s : R₁.rightDerived 0 ⋙ G ⟶ DerivedCategory.Plus.singleFunctor B 0 ⋙
      (R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor C 0)
    (t : DerivedCategory.Plus.singleFunctor B 0 ⋙
      (H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor C 0 ⟶ H ⋙ R₂.rightDerived 0)
    (M : B)
    (hunit : ∀ K, DerivedMateUnitEquation adj₁ adj₂ α αD K)
    (htransport : WhiskeredTransportEquation s
      (mateEquiv adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus αD).natTrans
      t M
      (G.map ((R₁.rightDerivedSingleHomologyIso 0).hom.app M))
      ((G.rightDerivedFunctorPlusHomologyIso 0).inv.app
        (R₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M)))
      ((DerivedCategory.Plus.homologyFunctor C 0).map
        (R₂.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M)))
      ((R₂.rightDerivedSingleHomologyIso 0).inv.app (H.obj M))) :
    Functor.HigherExchangeZeroEquation R₁ R₂ G H (mateEquiv adj₁ adj₂ α).natTrans M
      ((s ≫ Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor B 0)
        (Functor.whiskerRight
          (mateEquiv adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus αD).natTrans
          (DerivedCategory.Plus.homologyFunctor C 0)) ≫ t).app M) := by
  apply Functor.higherExchangeZero_normalization_of_eq R₁ R₂ G H
    (mateEquiv adj₁ adj₂ α).natTrans
    (mateEquiv adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus αD).natTrans
    M _
  · exact htransport.symm
  · intro K
    exact hunit K

end CategoryTheory
