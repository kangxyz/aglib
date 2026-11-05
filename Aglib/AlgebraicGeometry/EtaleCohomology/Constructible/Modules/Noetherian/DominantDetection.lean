/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Noetherian.ZeroLocus
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleEvaluation

/-! # Dominant detection for native finite-type local systems

Closed zero loci detect sections after dominant pullback. Applying this on
original etale tests detects arbitrary arrows into the original local system.
The proof retains the actual inverse images and original chart evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

variable (R : Type r) [Ring R]

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Dominant pullback detects zero of arbitrary underlying arrows into a
finite-type native local system, without finite additive carriers. -/
theorem underlying_map_eq_zero_of_isFiniteTypeLocallyConstant_of_isDominant
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    (G : ModuleSheaf R X) (hG : IsFiniteTypeLocallyConstant G)
    {F : AbelianSheaf.{u, u + 1} X} (a : F ⟶ (moduleUnderlying R X).obj G)
    (ha : (inverseImage f).map a = 0) : a = 0 := by
  apply (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext U
  let j : U.unop.left ⟶ X := U.unop.hom
  let p := pullback.fst j f
  let q := pullback.snd j f
  have : IsDominant p := by
    constructor
    change Dense (Set.range (pullback.fst j f))
    rw [Scheme.Pullback.range_fst]
    exact f.denseRange.preimage j.isOpenMap
  let H := (inverseImage j).obj ((moduleUnderlying R X).obj G)
  let E := (moduleInverseImage R j).obj G
  let e := (moduleInverseImageUnderlyingIso R j).app G
  have hc (s : (globalSections U.unop.left).obj H) :
      IsClosed (sectionZeroOpen H s : Set U.unop.left) := by
    have h := isClosed_sectionZeroOpen_of_isFiniteTypeLocallyConstant R E
      (isFiniteTypeLocallyConstant_pullback j hG)
      ((globalSections U.unop.left).map e.inv s)
    exact (sectionZeroOpen_mapIso e.symm s) ▸ h
  have hinj := globalSectionsPullback_injective_of_closedZeroLoci p H hc
  let d := (inverseImage j).map a
  let c : inverseImage j ⋙ inverseImage p ≅
      inverseImage f ⋙ inverseImage q :=
    (inverseImageComp j p).symm ≪≫
      eqToIso (congrArg inverseImage (pullback.condition (f := j) (g := f))) ≪≫
      inverseImageComp f q
  have hd : (inverseImage p).map d = 0 := by
    apply (cancel_mono (c.hom.app ((moduleUnderlying R X).obj G))).mp
    have h := c.hom.naturality a
    change (inverseImage p).map d ≫ _ =
      c.hom.app F ≫ (inverseImage q).map ((inverseImage f).map a) at h
    rw [ha, Functor.map_zero, comp_zero] at h
    simpa only [zero_comp] using h
  have hΓ : (globalSections U.unop.left).map d = 0 := by
    apply AddCommGrpCat.hom_ext
    ext s
    apply hinj
    have h := ConcreteCategory.congr_hom (globalSectionsPullback_naturality p d) s
    rw [hd, Functor.map_zero, comp_zero] at h
    simpa only [ConcreteCategory.comp_apply, AddCommGrpCat.zero_apply,
      map_zero] using h
  have h := Continuity.pullbackSectionsEtaleEvaluationIso_naturality a U.unop
  rw [hΓ, zero_comp] at h
  change a.hom.app (op U.unop) = 0
  apply (cancel_epi (Continuity.pullbackSectionsEtaleEvaluationIso F U.unop).hom).mp
  simpa only [comp_zero] using h.symm

/-- The original native dominant pullback detects equality of arbitrary maps
into a finite-type locally constant module coefficient. -/
theorem inverseImage_map_injective_of_isFiniteTypeLocallyConstant_of_isDominant
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    (G : ModuleSheaf R X) (hG : IsFiniteTypeLocallyConstant G)
    (F : ModuleSheaf R X) :
    Function.Injective (fun a : F ⟶ G => (moduleInverseImage R f).map a) := by
  intro a b hab
  apply (moduleUnderlying R X).map_injective
  apply sub_eq_zero.mp
  apply underlying_map_eq_zero_of_isFiniteTypeLocallyConstant_of_isDominant R f G hG
  rw [Functor.map_sub, sub_eq_zero]
  let e := moduleInverseImageUnderlyingIso R f
  apply (cancel_epi (e.hom.app F)).mp
  change e.hom.app F ≫ (moduleUnderlying R X ⋙ inverseImage f).map a =
    e.hom.app F ≫ (moduleUnderlying R X ⋙ inverseImage f).map b
  rw [← e.hom.naturality, ← e.hom.naturality]
  change (moduleUnderlying R Y).map ((moduleInverseImage R f).map a) ≫ _ =
    (moduleUnderlying R Y).map ((moduleInverseImage R f).map b) ≫ _
  exact congrArg (fun k => (moduleUnderlying R Y).map k ≫ e.hom.app G) hab

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
