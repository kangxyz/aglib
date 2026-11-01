/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.InternalExtComparison
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Source
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity

/-!
# Original source and evaluation maps for internal Ext

The source maps retain the original internal Hom, tensor adjunction and lifted
unit. Evaluation is the original counit in Hom-first order. No flatness,
projectivity of the unit, or exactness of tensoring by a coefficient is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open SheafOfModulesOfCommRing (tensorProduct tensorMap tensorLeftUnitIso tensorRightUnitIso)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe c h r eM eA

namespace SheafOfModules.InternalHom

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h r} RingCat.{max c h r})]
  (R : Sheaf J CommRingCat.{max c h r})
  [HasSheafify J AddCommGrpCat.{max c h r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h r}]

/-- Source naturality of the whole global-Hom comparison at the selected lifted unit. -/
theorem liftedUnitCoyonedaIso_precompose {M M' : SheafOfModulesOfCommRing R}
    (a : M' ⟶ M) :
    Functor.whiskerRight (precomposeNatTrans.{c, h, r} R a)
        (preadditiveCoyoneda.obj (op (SheafOfModules.liftedUnit.{c, h, max c h r, max c h r}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))) ≫
        (liftedUnitCoyonedaIso.{c, h, r} R M').hom =
      (liftedUnitCoyonedaIso.{c, h, r} R M).hom ≫ preadditiveCoyoneda.map a.op := by
  ext N f
  change unitHomAddEquiv.{c, h, r} R M' N
      ((SheafOfModules.liftedUnitIso _).inv ≫ (f ≫ map R a (𝟙 N))) =
    a ≫ unitHomAddEquiv.{c, h, r} R M N ((SheafOfModules.liftedUnitIso _).inv ≫ f)
  rw [← Category.assoc]
  exact unitHomAddEquiv_precompose.{c, h, r} R a
    ((SheafOfModules.liftedUnitIso _).inv ≫ f)

/-- The original counit commutes with both original coefficient maps. -/
theorem evaluationSheaf_naturality {M M' N N' : SheafOfModulesOfCommRing R}
    (a : M' ⟶ M) (b : N ⟶ N') :
    tensorMap R (map R a b) (𝟙 M') ≫ evaluationSheaf.{c, h, r} R M' N' =
      tensorMap R (𝟙 (sheaf R M N)) a ≫ evaluationSheaf.{c, h, r} R M N ≫ b := by
  rw [← uncurry_eq_tensorMap_evaluation.{c, h, r}]
  have hm : map R a b = map R a (𝟙 N) ≫ map R (𝟙 M') b := by
    rw [map_comp]
    simp only [Category.id_comp]
  rw [hm, uncurry_map.{c, h, r}]
  have hs := uncurry_precompose.{c, h, r} R a (𝟙 (sheaf R M N))
  simp only [Category.id_comp] at hs
  rw [hs]
  rfl

/-- Evaluating a map out of the original unit gives precisely the original global-Hom arrow. -/
theorem unitHomAddEquiv_evaluation (M N : SheafOfModulesOfCommRing R)
    (f : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      sheaf R M N) :
    tensorMap R f (𝟙 M) ≫ evaluationSheaf.{c, h, r} R M N =
      (tensorLeftUnitIso R).hom.app M ≫ unitHomAddEquiv.{c, h, r} R M N f := by
  rw [unitHomAddEquiv_apply, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact (uncurry_eq_tensorMap_evaluation.{c, h, r} R _ M N f).symm

/-- The same actual evaluation on pure original sections, without cohomological transport. -/
theorem evaluationSheaf_map_tmul {M N P : SheafOfModulesOfCommRing R}
    (f : P ⟶ sheaf R M N) (U : Cᵒᵖ) (x : P.val.obj U) (m : M.val.obj U) :
    (tensorMap R f (𝟙 M) ≫ evaluationSheaf.{c, h, r} R M N).val.app U
        ((SheafOfModulesOfCommRing.tensorUnitMap R P M).app U (x ⊗ₜ m)) =
      (f.val.app U x).val.app (op (Over.mk (𝟙 U.unop))) m := by
  rw [← uncurry_eq_tensorMap_evaluation.{c, h, r} R P M N f]
  exact uncurry_tmul.{c, h, r} R P M N f U x m

/-- Internal Hom from the original unit is the identity by the original right-unitor
and tensor-Hom adjunction. This is internal exactness, not global projectivity. -/
def unitSourceHomIso :
    homFunctor.{c, h, r} R
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      𝟭 (SheafOfModulesOfCommRing R) :=
  Adjunction.rightAdjointUniq (tensorHomAdjunction.{c, h, r} R _)
    ((Adjunction.id).ofNatIsoLeft (tensorRightUnitIso R).symm)

/-- The unit-source comparison retains the original whole evaluation counit. -/
theorem unitSourceHomIso_evaluation (N : SheafOfModulesOfCommRing R) :
    tensorMap R ((unitSourceHomIso.{c, h, r} R).hom.app N)
        (𝟙 (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ≫
        (tensorRightUnitIso R).hom.app N =
      evaluationSheaf.{c, h, r} R _ N := by
  exact Adjunction.rightAdjointUniq_hom_app_counit
    (tensorHomAdjunction.{c, h, r} R _)
    ((Adjunction.id).ofNatIsoLeft (tensorRightUnitIso R).symm) N

/-- The lifted unit uses the fixed actual ULift isomorphism before the same unit-source map. -/
def liftedUnitSourceHomIso :
    homFunctor.{c, h, r} R
      (SheafOfModules.liftedUnit.{c, h, max c h r, max c h r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      𝟭 (SheafOfModulesOfCommRing R) :=
  (bifunctor.{c, h, r} R).mapIso
      (SheafOfModules.liftedUnitIso ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).symm.op
    ≪≫ unitSourceHomIso.{c, h, r} R

end SheafOfModules.InternalHom

namespace CategoryTheory.Functor

open HomologicalComplex

universe u v u' w w'

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D] [HasExt.{w'} D]
  (L : A ⥤ D) [L.Additive] (P : D)

attribute [local instance] HasDerivedCategory.standard

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical reverse map is computed on one supplied original resolution.
Only the represented derived unit on its actual internal-Hom image is inverted. -/
theorem internalExtReverse_resolution
    (hI : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} P (L.obj I) (n + 1)))
    {N : A} (I : InjectiveResolution N) :
    let _ := isIso_representedRightDerivedUnit_map_of_injective L P hI I.cochainComplexPlus
      (fun n => inferInstanceAs (Injective (I.cochainComplex.X n)))
    (leftExactDerivedReverse L P hI).app N ≫
        (I.rightDerivedFunctorPlusIso (L ⋙ preadditiveCoyoneda.obj (op P))).inv =
      (preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            ((show (CochainComplex.singleFunctorPlus D 0).obj (L.obj N) ⟶
                L.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj N)
              from ObjectProperty.homMk
                ((singleMapHomologicalComplex L (.up ℤ) 0).inv.app N)) ≫
              L.mapCochainComplexPlus.map I.ιPlus)) ≫
        CategoryTheory.inv ((preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlusUnit.app
          (L.mapCochainComplexPlus.obj I.cochainComplexPlus)) := by
  let G := preadditiveCoyoneda.obj (op P)
  let K := I.cochainComplexPlus
  let f : (DerivedCategory.Plus.singleFunctor A 0).obj N ⟶ DerivedCategory.Plus.Q.obj K :=
    DerivedCategory.Plus.Q.map I.ιPlus
  let E := I.rightDerivedFunctorPlusIso L
  let B := I.rightDerivedFunctorPlusIso (L ⋙ G)
  let T := rightDerivedFunctorPlusCompComparison L G
  let z := G.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K)
  let a : (CochainComplex.singleFunctorPlus D 0).obj (L.obj N) ⟶
      L.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj N) :=
    ObjectProperty.homMk ((singleMapHomologicalComplex L (.up ℤ) 0).inv.app N)
  let b := a ≫ L.mapCochainComplexPlus.map I.ιPlus
  let : IsIso z := isIso_representedRightDerivedUnit_map_of_injective L P hI K
    (fun n => inferInstanceAs (Injective (I.cochainComplex.X n)))
  let : IsIso T := isIso_rightDerivedFunctorPlusCompComparison_of_acyclic L G
    (representedDerivedImage_isZero_of_ext_subsingleton L P hI)
  have hT : B.hom ≫ T.app ((DerivedCategory.Plus.singleFunctor A 0).obj N) =
      z ≫ G.rightDerivedFunctorPlus.map E.hom := by
    apply (cancel_mono (G.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlus.map f))).mp
    have hn := T.naturality f
    change (L ⋙ G).rightDerivedFunctorPlus.map f ≫ T.app (DerivedCategory.Plus.Q.obj K) =
      T.app ((DerivedCategory.Plus.singleFunctor A 0).obj N) ≫
        G.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlus.map f) at hn
    rw [Category.assoc, ← hn, ← Category.assoc]
    rw [I.rightDerivedFunctorPlusIso_hom_comp (L ⋙ G)]
    rw [rightDerivedFunctorPlusCompComparison_app]
    change z ≫ G.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlusUnit.app K) = _
    rw [Category.assoc, ← G.rightDerivedFunctorPlus.map_comp]
    rw [I.rightDerivedFunctorPlusIso_hom_comp L]
  have hu : DerivedCategory.Plus.Q.map b ≫ E.hom = L.rightDerivedSingleUnit N := by
    dsimp only [b]
    rw [Functor.map_comp, Category.assoc, I.rightDerivedFunctorPlusIso_unit L]
    rfl
  change (leftExactDerivedReverse L P hI).app N ≫ B.inv =
    G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map b) ≫ CategoryTheory.inv z
  apply (cancel_mono (B.hom ≫ T.app ((DerivedCategory.Plus.singleFunctor A 0).obj N))).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hT]
  simp only [IsIso.inv_hom_id_assoc]
  rw [← G.rightDerivedFunctorPlus.map_comp, hu]
  exact leftExactDerivedReverse_app_comp_comparison L P hI N

end CategoryTheory.Functor

namespace CategoryTheory.InjectiveResolution

open HomologicalComplex CochainComplex.HomComplex

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A] [HasExt.{w} A]
  {N : A} (I : InjectiveResolution N)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extMk_originalHomology (F : A) (q : ℕ)
    (f : F ⟶ I.cocomplex.X q) (hf : f ≫ I.cocomplex.d q (q + 1) = 0) :
    (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (op F)) q).hom
        (I.extRightDerivedAddEquiv F q (I.extMk f (q + 1) rfl hf)) =
      let K := ((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex
      K.homologyπ (q : ℤ) ((K.sc (q : ℤ)).abCyclesIso.inv
        ⟨f ≫ (I.cochainComplexXIso q q rfl).inv, by
          change (f ≫ _) ≫ I.cochainComplex.d (q : ℤ) ((ComplexShape.up ℤ).next q) = 0
          rw [CochainComplex.next ℤ (q : ℤ),
            I.cochainComplex_d q (q + 1) q (q + 1) rfl (by omega)]
          simpa only [Category.assoc, Iso.inv_hom_id_assoc, zero_comp] using
            congrArg (fun z => z ≫ (I.cochainComplexXIso (q + 1) (q + 1) rfl).inv) hf⟩) := by
  let a := f ≫ (I.cochainComplexXIso q q rfl).inv
  have ha : a ≫ I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0 := by
    dsimp only [a]
    rw [I.cochainComplex_d q (q + 1) q (q + 1) rfl (by omega)]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, zero_comp] using
      congrArg (fun z => z ≫ (I.cochainComplexXIso (q + 1) (q + 1) rfl).inv) hf
  have hx : I.extMk f (q + 1) rfl hf = I.extEquivCohomologyClass.symm
      (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl ha)) := by
    apply I.extEquivCohomologyClass.injective
    rw [Equiv.apply_symm_apply, I.extEquivCohomologyClass_extMk]
    rfl
  rw [hx, I.extRightDerivedAddEquiv_cocycle F q a ha]
  exact ConcreteCategory.congr_hom
    (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (op F)) q).inv_hom_id _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original Ext source precomposition on one fixed target resolution is the original
source map of its actual Hom complex. The target resolution does not vary with F. -/
theorem ext_originalHomology_precompose {F F' : A} (a : F' ⟶ F)
    (q : ℕ) (x : Ext.{w} F N q) :
    (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (op F')) q).hom
        (I.extRightDerivedAddEquiv F' q ((Ext.mk₀ a).comp x (zero_add q))) =
      homologyMap ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op)
        (.up ℤ)).app I.cochainComplex) (q : ℤ)
        ((I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (op F)) q).hom
          (I.extRightDerivedAddEquiv F q x)) := by
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective x (q + 1) rfl
  rw [I.mk₀_comp_extMk, I.extMk_originalHomology, I.extMk_originalHomology]
  let K := ((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex (.up ℤ)).obj
    I.cochainComplex
  let K' := ((preadditiveCoyoneda.obj (op F')).mapHomologicalComplex (.up ℤ)).obj
    I.cochainComplex
  let t := (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℤ)).app
    I.cochainComplex
  change K'.homologyπ (q : ℤ) _ = homologyMap t (q : ℤ) (K.homologyπ (q : ℤ) _)
  rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (K'.iCycles (q : ℤ))).mp inferInstance
  rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply]
  erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles,
    HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
  change (a ≫ f) ≫ (I.cochainComplexXIso q q rfl).inv =
    a ≫ (f ≫ (I.cochainComplexXIso q q rfl).inv)
  exact Category.assoc _ _ _

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.Functor

open HomologicalComplex

universe u v u' w'

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D] [HasExt.{w'} D]
  (L : A ⥤ D) [L.Additive] (P : D)

attribute [local instance] HasDerivedCategory.standard

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Normalization of the original reverse on the single supplied target resolution,
before original Ext or ordinary-cohomology carriers are evaluated. -/
theorem internalExtHomReverse_resolution {F : A}
    (e : L ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op F))
    (hI : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} P (L.obj I) (n + 1)))
    {N : A} (I : InjectiveResolution N) (q : ℕ) :
    (rightDerivedHomReverse L P e hI q).app N ≫
        (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (op F)) q).hom =
      ((preadditiveCoyoneda.obj (op P)).rightDerivedSingleHomologyIso q).hom.app (L.obj N) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (q : ℤ)).map
          ((leftExactDerivedReverse L P hI).app N ≫
            (I.rightDerivedFunctorPlusIso (L ⋙ preadditiveCoyoneda.obj (op P))).inv) ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).hom.app
          ((L ⋙ preadditiveCoyoneda.obj (op P)).mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
        homologyMap ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I.cochainComplex)
          (q : ℤ) := by
  let G := preadditiveCoyoneda.obj (op P)
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat (q : ℤ)
  let B := I.rightDerivedFunctorPlusIso (L ⋙ G)
  let E := I.isoRightDerivedObjCochain (L ⋙ G) q
  let S := (L ⋙ G).rightDerivedSingleHomologyIso q
  let T := (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).app
    ((L ⋙ G).mapCochainComplexPlus.obj I.cochainComplexPlus)
  have hS : S.inv.app N ≫ E.hom = H.map B.inv ≫ T.hom := by
    apply (cancel_epi (S.hom.app N)).mp
    rw [Iso.hom_inv_id_app_assoc]
    dsimp only [S]
    rw [rightDerivedSingleHomologyIso_hom_app (L ⋙ G) I q]
    simp only [InjectiveResolution.isoRightDerivedSingleHomology_hom, Category.assoc]
    rw [← H.map_comp_assoc, B.hom_inv_id, H.map_id]
    change E.hom = E.hom ≫ T.inv ≫ T.hom
    rw [Iso.inv_hom_id, Category.comp_id]
  have he := I.isoRightDerivedObjCochain_hom_natTrans e.hom q
  change (rightDerivedNatIsoOfAdditive e q).hom.app N ≫
      (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (op F)) q).hom =
    E.hom ≫ homologyMap ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I.cochainComplex)
      (q : ℤ) at he
  simp only [rightDerivedHomReverse, NatTrans.comp_app, Category.assoc]
  rw [he]
  simp only [rightDerivedRepresentedReverse, Category.assoc]
  rw [reassoc_of% hS, ← H.map_comp_assoc]
  rfl

end CategoryTheory.Functor

namespace CategoryTheory.Functor

open HomologicalComplex

universe u v u' w'

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D] [HasExt.{w'} D]
  (L : A ⥤ D) [L.Additive] (P : D)

attribute [local instance] HasDerivedCategory.standard

private def internalExtResolutionAugmentation {N : A} (I : InjectiveResolution N) :
    (CochainComplex.singleFunctorPlus D 0).obj (L.obj N) ⟶
      L.mapCochainComplexPlus.obj I.cochainComplexPlus :=
  (show (CochainComplex.singleFunctorPlus D 0).obj (L.obj N) ⟶
      L.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj N) from
    ObjectProperty.homMk ((singleMapHomologicalComplex L (.up ℤ) 0).inv.app N)) ≫
      L.mapCochainComplexPlus.map I.ιPlus

omit [EnoughInjectives A] [EnoughInjectives D] [HasExt.{w'} D] in
private theorem internalExtResolutionAugmentation_naturality
    {L' : A ⥤ D} [L'.Additive] (α : L ⟶ L') {N : A} (I : InjectiveResolution N) :
    (CochainComplex.singleFunctorPlus D 0).map (α.app N) ≫
        internalExtResolutionAugmentation L' I =
      internalExtResolutionAugmentation L I ≫
        (NatTrans.mapCochainComplexPlus α).app I.cochainComplexPlus := by
  let S := (CochainComplex.singleFunctorPlus A 0).obj N
  let a : (CochainComplex.singleFunctorPlus D 0).obj (L.obj N) ⟶
      L.mapCochainComplexPlus.obj S :=
    ObjectProperty.homMk ((singleMapHomologicalComplex L (.up ℤ) 0).inv.app N)
  let a' : (CochainComplex.singleFunctorPlus D 0).obj (L'.obj N) ⟶
      L'.mapCochainComplexPlus.obj S :=
    ObjectProperty.homMk ((singleMapHomologicalComplex L' (.up ℤ) 0).inv.app N)
  have hs : a ≫ (NatTrans.mapCochainComplexPlus α).app S =
      (CochainComplex.singleFunctorPlus D 0).map (α.app N) ≫ a' := by
    apply ObjectProperty.hom_ext
    change (singleMapHomologicalComplex L (.up ℤ) 0).inv.app N ≫
        (NatTrans.mapHomologicalComplex α (.up ℤ)).app
          ((CochainComplex.singleFunctor A 0).obj N) = _
    rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj,
      Iso.inv_hom_id_app_assoc]
    rfl
  change _ ≫ (a' ≫ L'.mapCochainComplexPlus.map I.ιPlus) =
    (a ≫ L.mapCochainComplexPlus.map I.ιPlus) ≫ _
  rw [← Category.assoc, ← hs, Category.assoc, Category.assoc,
    (NatTrans.mapCochainComplexPlus α).naturality I.ιPlus]

private def internalExtResolutionEvaluation {F : A}
    (e : L ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op F))
    (hI : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} P (L.obj I) (n + 1)))
    {N : A} (I : InjectiveResolution N) :
    (preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor D 0).obj (L.obj N)) ⟶
      DerivedCategory.Plus.Q.obj
        ((preadditiveCoyoneda.obj (op F)).mapCochainComplexPlus.obj I.cochainComplexPlus) := by
  letI := isIso_representedRightDerivedUnit_map_of_injective L P hI I.cochainComplexPlus
    (fun n => inferInstanceAs (Injective (I.cochainComplex.X n)))
  exact (preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (internalExtResolutionAugmentation L I)) ≫
    CategoryTheory.inv ((preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlusUnit.app
      (L.mapCochainComplexPlus.obj I.cochainComplexPlus)) ≫
    DerivedCategory.Plus.Q.map ((NatTrans.mapCochainComplexPlus e.hom).app I.cochainComplexPlus)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem internalExtResolutionEvaluation_naturality
    {L' : A ⥤ D} [L'.Additive] {F F' : A}
    (e : L ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op F))
    (e' : L' ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op F'))
    (hI : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} P (L.obj I) (n + 1)))
    (hI' : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} P (L'.obj I) (n + 1)))
    (α : L ⟶ L') (a : F' ⟶ F)
    (he : whiskerRight α (preadditiveCoyoneda.obj (op P)) ≫ e'.hom =
      e.hom ≫ preadditiveCoyoneda.map a.op)
    {N : A} (I : InjectiveResolution N) :
    (preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor D 0).map (α.app N)) ≫
        internalExtResolutionEvaluation L' P e' hI' I =
      internalExtResolutionEvaluation L P e hI I ≫
        DerivedCategory.Plus.Q.map
          ((NatTrans.mapCochainComplexPlus (preadditiveCoyoneda.map a.op)).app
            I.cochainComplexPlus) := by
  let G := preadditiveCoyoneda.obj (op P)
  let K := I.cochainComplexPlus
  let v := (NatTrans.mapCochainComplexPlus α).app K
  let z := G.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K)
  let z' := G.rightDerivedFunctorPlusUnit.app (L'.mapCochainComplexPlus.obj K)
  let : IsIso z := isIso_representedRightDerivedUnit_map_of_injective L P hI K
    (fun n => inferInstanceAs (Injective (I.cochainComplex.X n)))
  let : IsIso z' := isIso_representedRightDerivedUnit_map_of_injective L' P hI' K
    (fun n => inferInstanceAs (Injective (I.cochainComplex.X n)))
  have hz := G.rightDerivedFunctorPlusUnit.naturality v
  change DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map v) ≫ z' =
    z ≫ G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map v) at hz
  have hzi : G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map v) ≫
      CategoryTheory.inv z' =
    CategoryTheory.inv z ≫ DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map v) := by
    apply (cancel_epi z).mp
    rw [← Category.assoc, ← hz]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id, Category.comp_id]
  have hk : G.mapCochainComplexPlus.map v ≫
        (NatTrans.mapCochainComplexPlus e'.hom).app K =
      (NatTrans.mapCochainComplexPlus e.hom).app K ≫
        (NatTrans.mapCochainComplexPlus (preadditiveCoyoneda.map a.op)).app K := by
    apply ObjectProperty.hom_ext
    ext n : 1
    exact congrArg (fun t => t.app (I.cochainComplex.X n)) he
  change G.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus D 0).map (α.app N))) ≫
      (G.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (internalExtResolutionAugmentation L' I)) ≫
        CategoryTheory.inv z' ≫
        DerivedCategory.Plus.Q.map ((NatTrans.mapCochainComplexPlus e'.hom).app K)) =
    (G.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (internalExtResolutionAugmentation L I)) ≫
        CategoryTheory.inv z ≫
        DerivedCategory.Plus.Q.map ((NatTrans.mapCochainComplexPlus e.hom).app K)) ≫ _
  rw [← Category.assoc, ← G.rightDerivedFunctorPlus.map_comp,
    ← DerivedCategory.Plus.Q.map_comp,
    internalExtResolutionAugmentation_naturality, DerivedCategory.Plus.Q.map_comp,
    G.rightDerivedFunctorPlus.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hzi]
  have hq := congrArg (fun f => DerivedCategory.Plus.Q.map f) hk
  simp only [CategoryTheory.Functor.map_comp] at hq
  exact congrArg (fun f => G.rightDerivedFunctorPlus.map
    (DerivedCategory.Plus.Q.map (internalExtResolutionAugmentation L I)) ≫
      CategoryTheory.inv z ≫ f) hq

end CategoryTheory.Functor

namespace CategoryTheory.Functor

open HomologicalComplex

universe u v u' w w'

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  {D : Type u'} [Category.{v} D] [Abelian D] [EnoughInjectives D] [HasExt.{w'} D]
  (L : A ⥤ D) [L.Additive] (P : D)

attribute [local instance] HasDerivedCategory.standard

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem internalExtHomReverse_resolutionEvaluation {F : A}
    (e : L ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op F))
    (hI : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} P (L.obj I) (n + 1)))
    {N : A} (I : InjectiveResolution N) (q : ℕ) :
    (rightDerivedHomReverse L P e hI q).app N ≫
        (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (op F)) q).hom =
      ((preadditiveCoyoneda.obj (op P)).rightDerivedSingleHomologyIso q).hom.app (L.obj N) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (q : ℤ)).map
          (internalExtResolutionEvaluation L P e hI I) ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).hom.app
          ((preadditiveCoyoneda.obj (op F)).mapCochainComplexPlus.obj I.cochainComplexPlus) := by
  let G := preadditiveCoyoneda.obj (op P)
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat (q : ℤ)
  let K := I.cochainComplexPlus
  let t := (NatTrans.mapCochainComplexPlus e.hom).app K
  have ht := (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat)
    (q : ℤ)).hom.naturality t
  change H.map (DerivedCategory.Plus.Q.map t) ≫
      (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).hom.app
        ((preadditiveCoyoneda.obj (op F)).mapCochainComplexPlus.obj K) =
    (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).hom.app
        ((L ⋙ G).mapCochainComplexPlus.obj K) ≫
      homologyMap ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I.cochainComplex)
        (q : ℤ) at ht
  let z := G.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K)
  let : IsIso z := isIso_representedRightDerivedUnit_map_of_injective L P hI K
    (fun n => inferInstanceAs (Injective (I.cochainComplex.X n)))
  have hraw : (leftExactDerivedReverse L P hI).app N ≫
      (I.rightDerivedFunctorPlusIso (L ⋙ G)).inv =
    G.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (internalExtResolutionAugmentation L I)) ≫
      CategoryTheory.inv z := internalExtReverse_resolution L P hI I
  rw [internalExtHomReverse_resolution L P e hI I q, hraw]
  rw [← ht, ← H.map_comp_assoc]
  simp only [internalExtResolutionEvaluation, Category.assoc]
  rfl

variable [HasExt.{w} A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extReverse_originalResolutionEvaluation {F : A}
    (e : L ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op F))
    (hI : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} P (L.obj I) (n + 1)))
    (N : A) (q : ℕ) (x : Ext.{w'} P (L.obj N) q) :
    let I := injectiveResolution N
    (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (op F)) q).hom
        (I.extRightDerivedAddEquiv F q (extReverseOfLeftExact L P e hI N q x)) =
      (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).hom.app
        ((preadditiveCoyoneda.obj (op F)).mapCochainComplexPlus.obj I.cochainComplexPlus)
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat (q : ℤ)).map
          (internalExtResolutionEvaluation L P e hI I)
          (((preadditiveCoyoneda.obj (op P)).rightDerivedSingleHomologyIso q).hom.app (L.obj N)
            (extRightDerivedRepresentedAddEquiv P (L.obj N) q x))) := by
  dsimp only
  simp only [extReverseOfLeftExact, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    extRightDerivedRepresentedAddEquiv, AddEquiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom
    (internalExtHomReverse_resolutionEvaluation L P e hI (injectiveResolution N) q)
    (extRightDerivedRepresentedAddEquiv P (L.obj N) q x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extReverse_sourceFunctors {L' : A ⥤ D} [L'.Additive] {F F' : A}
    (e : L ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op F))
    (e' : L' ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op F'))
    (hI : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} P (L.obj I) (n + 1)))
    (hI' : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} P (L'.obj I) (n + 1)))
    (α : L ⟶ L') (a : F' ⟶ F)
    (he : whiskerRight α (preadditiveCoyoneda.obj (op P)) ≫ e'.hom =
      e.hom ≫ preadditiveCoyoneda.map a.op)
    (N : A) (q : ℕ) (x : Ext.{w'} P (L.obj N) q) :
    extReverseOfLeftExact L' P e' hI' N q (x.comp (Ext.mk₀ (α.app N)) (add_zero q)) =
      (Ext.mk₀ a).comp (extReverseOfLeftExact L P e hI N q x) (zero_add q) := by
  let I := injectiveResolution N
  let G := preadditiveCoyoneda.obj (op P)
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat (q : ℤ)
  let S := G.rightDerivedSingleHomologyIso q
  let C := I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (op F')) q
  apply ((I.extRightDerivedAddEquiv F' q).trans C.addCommGroupIsoToAddEquiv).injective
  change C.hom (I.extRightDerivedAddEquiv F' q _) = C.hom (I.extRightDerivedAddEquiv F' q _)
  rw [I.ext_originalHomology_precompose a q]
  rw [extReverse_originalResolutionEvaluation L' P e' hI' N q,
    extReverse_originalResolutionEvaluation L P e hI N q]
  have hin : S.hom.app (L'.obj N)
        (extRightDerivedRepresentedAddEquiv P (L'.obj N) q
          (x.comp (Ext.mk₀ (α.app N)) (add_zero q))) =
      H.map (G.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor D 0).map (α.app N)))
        (S.hom.app (L.obj N)
      (extRightDerivedRepresentedAddEquiv P (L.obj N) q x)) := by
    rw [extRightDerivedRepresentedAddEquiv_naturality]
    exact ConcreteCategory.congr_hom (S.hom.naturality (α.app N))
      (extRightDerivedRepresentedAddEquiv P (L.obj N) q x)
  rw [hin]
  have hout := (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat)
    (q : ℤ)).hom.naturality
      ((NatTrans.mapCochainComplexPlus (preadditiveCoyoneda.map a.op)).app I.cochainComplexPlus)
  change H.map (DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (preadditiveCoyoneda.map a.op)).app
          I.cochainComplexPlus)) ≫
      (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).hom.app
        ((preadditiveCoyoneda.obj (op F')).mapCochainComplexPlus.obj I.cochainComplexPlus) =
    (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).hom.app
        ((preadditiveCoyoneda.obj (op F)).mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
      homologyMap ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℤ)).app
        I.cochainComplex) (q : ℤ) at hout
  have hm : H.map (G.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor D 0).map (α.app N))) ≫
        H.map (internalExtResolutionEvaluation L' P e' hI' I) ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).hom.app
          ((preadditiveCoyoneda.obj (op F')).mapCochainComplexPlus.obj I.cochainComplexPlus) =
      H.map (internalExtResolutionEvaluation L P e hI I) ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).hom.app
          ((preadditiveCoyoneda.obj (op F)).mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
        homologyMap ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℤ)).app
          I.cochainComplex) (q : ℤ) := by
    rw [← H.map_comp_assoc,
      internalExtResolutionEvaluation_naturality L P e e' hI hI' α a he I,
      H.map_comp_assoc, hout]
  exact ConcreteCategory.congr_hom hm
    (S.hom.app (L.obj N)
      (extRightDerivedRepresentedAddEquiv P (L.obj N) q x))

end CategoryTheory.Functor

namespace CategoryTheory.Functor

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A] [HasExt.{w} A]
  (L : A ⥤ A) [L.Additive] (P : A)

attribute [local instance] HasDerivedCategory.standard

/-- The original reverse respects a whole endofunctor/source square
at its original Ext realization. -/
theorem extReverseOfLeftExact_naturality_functor {L' : A ⥤ A} [L'.Additive] {F F' : A}
    (e : L ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op F))
    (e' : L' ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op F'))
    (hI : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w} P (L.obj I) (n + 1)))
    (hI' : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w} P (L'.obj I) (n + 1)))
    (α : L ⟶ L') (a : F' ⟶ F)
    (he : whiskerRight α (preadditiveCoyoneda.obj (op P)) ≫ e'.hom =
      e.hom ≫ preadditiveCoyoneda.map a.op)
    (N : A) (q : ℕ) :
    (extReverseOfLeftExact L' P e' hI' N q).comp
        ((Ext.mk₀ (α.app N)).postcomp P (add_zero q)) =
      ((Ext.mk₀ a).precomp N (zero_add q)).comp (extReverseOfLeftExact L P e hI N q) := by
  apply AddMonoidHom.ext
  intro x
  dsimp only [AddMonoidHom.comp_apply]
  have hPost : ((Ext.mk₀ (α.app N)).postcomp P (add_zero q)) x =
      x.comp (Ext.mk₀ (α.app N)) (add_zero q) := by
    simpa only [Ext.postcomp, AddMonoidHom.flip_apply] using
      (Ext.bilinearComp_apply_apply P (L.obj N) (L'.obj N) q 0 q (add_zero q)
        x (Ext.mk₀ (α.app N)))
  have hPre (y : Ext.{w} F N q) : ((Ext.mk₀ a).precomp N (zero_add q)) y =
      (Ext.mk₀ a).comp y (zero_add q) :=
    Ext.bilinearComp_apply_apply F' F N 0 q q (zero_add q) (Ext.mk₀ a) y
  exact (congrArg (fun z => extReverseOfLeftExact L' P e' hI' N q z) hPost).trans
    ((extReverse_sourceFunctors.{u, v, u, w, w} L P e e' hI hI' α a he N q x).trans
      (hPre (extReverseOfLeftExact L P e hI N q x)).symm)

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf.InternalExt

/-- Whole source squares pass through the original module-unit cohomology comparisons. -/
theorem cohomologyExtReverseAfterComparison_source
    {A A' B B' H H' : Type*}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    [AddCommGroup H] [AddCommGroup H']
    (E : A ≃+ H) (E' : A' ≃+ H') (r : A →+ B) (r' : A' →+ B')
    (rho : H →+ B) (rho' : H' →+ B')
    (hρ : rho = cohomologyExtReverseAfterComparison E r)
    (hρ' : rho' = cohomologyExtReverseAfterComparison E' r')
    (f : A →+ A') (g : H →+ H') (u : B →+ B')
    (hr : r'.comp f = u.comp r) (hE : ∀ x, E' (f x) = g (E x)) :
    rho'.comp g = u.comp rho := by
  rw [hρ, hρ']
  ext y
  obtain ⟨x, rfl⟩ := E.surjective y
  change r' (E'.symm (g (E x))) = u (r (E.symm (E x)))
  rw [← hE, E'.symm_apply_apply, E.symm_apply_apply]
  exact congrArg (fun f : A →+ B' => f x) hr

open SheafOfModules.InternalHom

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  (R : Sheaf J CommRingCat.{max c h}) [HasSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max c h})]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasExt.{eM} (SheafOfModulesOfCommRing R)]
  [HasExt.{eA} (Sheaf J AddCommGrpCat.{max c h})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max c h})]
  {T : C} (hT : IsTerminal T)

local instance : EnoughInjectives (SheafOfModulesOfCommRing R) :=
  SheafOfModules.enoughInjectivesLarge.{c, h, 0}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- The entire original source square at its literal derived-Hom carrier. It uses
one resolution of N for all sources, and has no target-acyclicity premise. -/
theorem moduleExtReverse_precompose {M M' : SheafOfModulesOfCommRing R}
    (a : M' ⟶ M) (N : SheafOfModulesOfCommRing R) (q : ℕ) :
    (fun {P : Prop} (_h : P) => P)
      (Functor.extReverseOfLeftExact_naturality_functor.{_, _, eM}
        (homFunctor.{c, h, 0} R M)
        (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (liftedUnitCoyonedaIso.{c, h, 0} R M) (liftedUnitCoyonedaIso.{c, h, 0} R M')
        (homFunctor_injective_ext_subsingleton R hT M)
        (homFunctor_injective_ext_subsingleton R hT M')
        (precomposeNatTrans.{c, h, 0} R a) a
        (liftedUnitCoyonedaIso_precompose.{c, h, 0} R a) N q) :=
  Functor.extReverseOfLeftExact_naturality_functor.{_, _, eM} (homFunctor.{c, h, 0} R M)
    (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (liftedUnitCoyonedaIso.{c, h, 0} R M) (liftedUnitCoyonedaIso.{c, h, 0} R M')
    (homFunctor_injective_ext_subsingleton R hT M)
    (homFunctor_injective_ext_subsingleton R hT M')
    (precomposeNatTrans.{c, h, 0} R a) a
    (liftedUnitCoyonedaIso_precompose.{c, h, 0} R a) N q

/-- Whole source naturality of the canonical ordinary-H map, on the actual original
module-unit cohomology comparisons. Both Ext worlds stay independent. -/
theorem cohomologyExtReverse_precompose {M M' : SheafOfModulesOfCommRing R}
    (a : M' ⟶ M) (N : SheafOfModulesOfCommRing R) (q : ℕ) :
    (fun {P : Prop} (_h : P) => P)
      (cohomologyExtReverseAfterComparison_source
        (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R M N) q)
        (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R M' N) q)
        (moduleExtReverse R hT M N q) (moduleExtReverse R hT M' N q)
        (cohomologyExtReverse R hT M N q) (cohomologyExtReverse R hT M' N q) rfl rfl
        ((Ext.mk₀ (map R a (𝟙 N))).postcomp
          (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (add_zero q))
        (Sheaf.H.map ((SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat
          RingCat)).obj R)).map (map R a (𝟙 N))) q)
        ((Ext.mk₀ a).precomp N (zero_add q))
        (moduleExtReverse_precompose R hT a N q)
        (ModuleCoefficients.cohomologyMap_naturality hT ((sheafCompose J (forget₂ CommRingCat
          RingCat)).obj R) (map R a (𝟙 N)) q)) :=
  cohomologyExtReverseAfterComparison_source
    (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R M N) q)
    (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R M' N) q)
    (moduleExtReverse R hT M N q) (moduleExtReverse R hT M' N q)
    (cohomologyExtReverse R hT M N q) (cohomologyExtReverse R hT M' N q) rfl rfl
    ((Ext.mk₀ (map R a (𝟙 N))).postcomp
      (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (add_zero q))
    (Sheaf.H.map ((SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      R)).map (map R a (𝟙 N))) q)
    ((Ext.mk₀ a).precomp N (zero_add q))
    (moduleExtReverse_precompose R hT a N q)
    (ModuleCoefficients.cohomologyMap_naturality hT ((sheafCompose J (forget₂ CommRingCat
      RingCat)).obj R) (map R a (𝟙 N)) q)

end CategoryTheory.Sheaf.InternalExt

namespace SheafOfModules.InternalHom

open CategoryTheory.MonoidalCategory

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h r} RingCat.{max c h r})]
  (R : Sheaf J CommRingCat.{max c h r})
  [HasSheafify J AddCommGrpCat.{max c h r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h r}]

private theorem tensorUnit_unitors :
    (tensorLeftUnitIso R).hom.app
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) =
      (tensorRightUnitIso R).hom.app
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := by
  rw [SheafOfModulesOfCommRing.tensorLeftUnitIso_hom_app,
    SheafOfModulesOfCommRing.tensorRightUnitIso_hom_app]
  congr 2
  exact unitors_equal

/-- The unit-source isomorphism has the actual evaluation as its right-unit counit. -/
theorem unitSourceHomIso_counit (N : SheafOfModulesOfCommRing R) :
    (tensorRightUnitIso R).hom.app (sheaf R
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N) ≫
        (unitSourceHomIso.{c, h, r} R).hom.app N =
      evaluationSheaf.{c, h, r} R
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N := by
  have h := (tensorRightUnitIso R).hom.naturality ((unitSourceHomIso.{c, h, r} R).hom.app N)
  exact h.symm.trans (unitSourceHomIso_evaluation.{c, h, r} R N)

/-- On maps from the actual unit, global Hom is postcomposition by the actual
unit-source isomorphism. This fixes its normalization, rather than only its isomorphism class. -/
theorem unitSourceHomIso_globalHom (N : SheafOfModulesOfCommRing R)
    (h : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      sheaf R (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N) :
    unitHomAddEquiv.{c, h, r} R _ N h = h ≫ (unitSourceHomIso.{c, h, r} R).hom.app N := by
  let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  have hn := (tensorRightUnitIso R).hom.naturality h
  change tensorMap R h (𝟙 U) ≫ (tensorRightUnitIso R).hom.app (sheaf R U N) =
    (tensorRightUnitIso R).hom.app U ≫ h at hn
  have hev : (tensorRightUnitIso R).hom.app (sheaf R U N) ≫
      (unitSourceHomIso.{c, h, r} R).hom.app N = evaluationSheaf.{c, h, r} R U N :=
    unitSourceHomIso_counit.{c, h, r} R N
  have hu : (tensorLeftUnitIso R).inv.app U ≫ (tensorRightUnitIso R).hom.app U = 𝟙 U := by
    calc
      _ = (tensorLeftUnitIso R).inv.app U ≫ (tensorLeftUnitIso R).hom.app U :=
        congrArg (fun f => (tensorLeftUnitIso R).inv.app U ≫ f) (tensorUnit_unitors R).symm
      _ = 𝟙 U := (tensorLeftUnitIso R).inv_hom_id_app U
  calc
    unitHomAddEquiv.{c, h, r} R U N h =
        (tensorLeftUnitIso R).inv.app U ≫ uncurry.{c, h, r} R U U N h :=
      unitHomAddEquiv_apply.{c, h, r} R U N h
    _ = (tensorLeftUnitIso R).inv.app U ≫ tensorMap R h (𝟙 U) ≫
        evaluationSheaf.{c, h, r} R U N := by rw [uncurry_eq_tensorMap_evaluation]
    _ = (tensorLeftUnitIso R).inv.app U ≫
        (tensorMap R h (𝟙 U) ≫ (tensorRightUnitIso R).hom.app (sheaf R U N)) ≫
        (unitSourceHomIso.{c, h, r} R).hom.app N := by
      simp only [Category.assoc]
      exact congrArg (fun f : tensorProduct R (sheaf R U N) U ⟶ N =>
        (tensorLeftUnitIso R).inv.app U ≫ tensorMap R h (𝟙 U) ≫ f) hev.symm
    _ = (tensorLeftUnitIso R).inv.app U ≫
        ((tensorRightUnitIso R).hom.app U ≫ h) ≫
        (unitSourceHomIso.{c, h, r} R).hom.app N := by rw [hn]
    _ = ((tensorLeftUnitIso R).inv.app U ≫ (tensorRightUnitIso R).hom.app U) ≫
        h ≫ (unitSourceHomIso.{c, h, r} R).hom.app N := by simp only [Category.assoc]
    _ = h ≫ (unitSourceHomIso.{c, h, r} R).hom.app N := by
      rw [hu]
      exact Category.id_comp (h ≫ (unitSourceHomIso.{c, h, r} R).hom.app N)


/-- The selected lifted-unit global Hom comparison is the coefficient action of
the same actual internal-Hom/unit isomorphism. -/
theorem liftedUnitSourceHomIso_globalHom (N : SheafOfModulesOfCommRing R)
    (h : SheafOfModules.liftedUnit.{c, h, max c h r, max c h r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      sheaf R (SheafOfModules.liftedUnit.{c, h, max c h r, max c h r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N) :
    (liftedUnitCoyonedaIso.{c, h, r} R _).hom.app N h =
      h ≫ (liftedUnitSourceHomIso.{c, h, r} R).hom.app N := by
  let e := SheafOfModules.liftedUnitIso ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  apply (cancel_epi e.inv).mp
  change e.inv ≫ unitHomAddEquiv.{c, h, r} R _ N (e.inv ≫ h) =
    e.inv ≫ h ≫ (map R e.inv (𝟙 N) ≫ (unitSourceHomIso.{c, h, r} R).hom.app N)
  rw [← unitHomAddEquiv_precompose.{c, h, r} R e.inv (e.inv ≫ h),
    unitSourceHomIso_globalHom.{c, h, r} R N]
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

/-- The whole selected global-Hom isomorphism is the original coefficient-unit action. -/
theorem liftedUnitSourceHomIso_coyoneda :
    (liftedUnitCoyonedaIso.{c, h, r} R
      (SheafOfModules.liftedUnit.{c, h, max c h r, max c h r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).hom =
      (Functor.isoWhiskerRight (liftedUnitSourceHomIso.{c, h, r} R)
        (preadditiveCoyoneda.obj (op (SheafOfModules.liftedUnit.{c, h, max c h r, max c h r}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))))).hom ≫
        (Functor.leftUnitor (preadditiveCoyoneda.obj
          (op (SheafOfModules.liftedUnit.{c, h, max c h r, max c h r}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))))).hom := by
  ext N h
  exact liftedUnitSourceHomIso_globalHom.{c, h, r} R N h

end SheafOfModules.InternalHom

namespace CategoryTheory.Functor

open HomologicalComplex

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A] [HasExt.{w} A]

attribute [local instance] HasDerivedCategory.standard

omit [EnoughInjectives A] in
private theorem identity_injective_ext_subsingleton (P I : A) [Injective I] (q : ℕ) :
    Subsingleton (Ext.{w} P I (q + 1)) := by
  refine ⟨fun x y => ?_⟩
  exact (Ext.eq_zero_of_injective x).trans (Ext.eq_zero_of_injective y).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem internalExtResolutionEvaluation_id (P : A) {N : A}
    (I : InjectiveResolution N) :
    internalExtResolutionEvaluation (𝟭 A) P
        (Functor.leftUnitor (preadditiveCoyoneda.obj (op P)))
        (identity_injective_ext_subsingleton P) I =
      (I.rightDerivedFunctorPlusIso (preadditiveCoyoneda.obj (op P))).inv := by
  let G := preadditiveCoyoneda.obj (op P)
  let K := I.cochainComplexPlus
  let J := Functor.mapCochainComplexPlusIdIso A
  let B := I.rightDerivedFunctorPlusIso G
  let z := G.rightDerivedFunctorPlusUnit.app K
  let z' := G.rightDerivedFunctorPlusUnit.app ((𝟭 A).mapCochainComplexPlus.obj K)
  let : IsIso z := G.isIso_rightDerivedFunctorPlusUnit_of_injective K
    (fun n => inferInstanceAs (Injective (I.cochainComplex.X n)))
  let : IsIso z' := isIso_representedRightDerivedUnit_map_of_injective (𝟭 A) P
    (identity_injective_ext_subsingleton P) K
    (fun n => inferInstanceAs (Injective (I.cochainComplex.X n)))
  have hs : (show (CochainComplex.singleFunctorPlus A 0).obj N ⟶
        (𝟭 A).mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj N) from
      ObjectProperty.homMk ((singleMapHomologicalComplex (𝟭 A) (.up ℤ) 0).inv.app N)) =
      J.inv.app ((CochainComplex.singleFunctorPlus A 0).obj N) := by
    apply ObjectProperty.hom_ext
    rw [singleMapHomologicalComplex_id_inv_app]
    ext n
    rfl
  have ha : internalExtResolutionAugmentation (𝟭 A) I ≫ J.hom.app K = I.ιPlus := by
    change (_ ≫ (𝟭 A).mapCochainComplexPlus.map I.ιPlus) ≫ J.hom.app K = _
    rw [Category.assoc, J.hom.naturality I.ιPlus, hs,
      ← Category.assoc, Iso.inv_hom_id_app]
    change (𝟙 _) ≫ I.ιPlus = I.ιPlus
    exact Category.id_comp I.ιPlus
  have he : (NatTrans.mapCochainComplexPlus (Functor.leftUnitor G).hom).app K =
      G.mapCochainComplexPlus.map (J.hom.app K) := by
    apply ObjectProperty.hom_ext
    ext n : 1
    simp [J, Functor.mapCochainComplexPlusIdIso, NatTrans.mapCochainComplexPlus_app_f]
  have hz := G.rightDerivedFunctorPlusUnit.naturality (J.hom.app K)
  change DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map (J.hom.app K)) ≫ z =
    z' ≫ G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (J.hom.app K)) at hz
  have hb : B.inv ≫ z = G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus) := by
    apply (cancel_epi B.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact (I.rightDerivedFunctorPlusIso_hom_comp G).symm
  apply (cancel_mono z).mp
  rw [hb]
  change (G.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (internalExtResolutionAugmentation (𝟭 A) I)) ≫
      CategoryTheory.inv z' ≫
      DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (Functor.leftUnitor G).hom).app K)) ≫ z = _
  simp only [Category.assoc]
  rw [he, hz]
  simp only [IsIso.inv_hom_id_assoc]
  rw [← G.rightDerivedFunctorPlus.map_comp, ← DerivedCategory.Plus.Q.map_comp, ha]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extReverse_identity (P N : A) (q : ℕ) (x : Ext.{w} P N q) :
    extReverseOfLeftExact (𝟭 A) P (Functor.leftUnitor (preadditiveCoyoneda.obj (op P)))
      (identity_injective_ext_subsingleton P) N q x = x := by
  let I := injectiveResolution N
  let G := preadditiveCoyoneda.obj (op P)
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat (q : ℤ)
  let B := I.rightDerivedFunctorPlusIso G
  let E := I.isoRightDerivedObjCochain G q
  let S := G.rightDerivedSingleHomologyIso q
  let T := (DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat) (q : ℤ)).app
    (G.mapCochainComplexPlus.obj I.cochainComplexPlus)
  apply ((I.extRightDerivedAddEquiv P q).trans E.addCommGroupIsoToAddEquiv).injective
  change E.hom (I.extRightDerivedAddEquiv P q _) = E.hom (I.extRightDerivedAddEquiv P q x)
  rw [extReverse_originalResolutionEvaluation (𝟭 A) P _ _ N q x,
    internalExtResolutionEvaluation_id P I]
  have h : S.hom.app N ≫ H.map B.inv ≫ T.hom = E.hom := by
    rw [rightDerivedSingleHomologyIso_hom_app G I q]
    simp only [InjectiveResolution.isoRightDerivedSingleHomology_hom, Category.assoc]
    rw [← H.map_comp_assoc, B.hom_inv_id, H.map_id]
    change E.hom ≫ T.inv ≫ 𝟙 _ ≫ T.hom = E.hom
    simp only [Category.id_comp]
    rw [T.inv_hom_id]
    exact Category.comp_id E.hom
  exact ConcreteCategory.congr_hom h (extRightDerivedRepresentedAddEquiv P N q x)

/-- A specified actual unit isomorphism normalizes the whole reverse in every degree. -/
theorem extReverseOfLeftExact_unitIso (L : A ⥤ A) [L.Additive] (P : A)
    (η : L ≅ 𝟭 A)
    (e : L ⋙ preadditiveCoyoneda.obj (op P) ≅ preadditiveCoyoneda.obj (op P))
    (he : whiskerRight η.hom (preadditiveCoyoneda.obj (op P)) ≫
      (Functor.leftUnitor (preadditiveCoyoneda.obj (op P))).hom = e.hom)
    (hI : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w} P (L.obj I) (n + 1)))
    (N : A) (q : ℕ) :
    extReverseOfLeftExact L P e hI N q =
      (Ext.mk₀ (η.hom.app N)).postcomp P (add_zero q) := by
  apply AddMonoidHom.ext
  intro x
  have he' : whiskerRight η.hom (preadditiveCoyoneda.obj (op P)) ≫
      (Functor.leftUnitor (preadditiveCoyoneda.obj (op P))).hom =
    e.hom ≫ preadditiveCoyoneda.map (𝟙 P).op := by
    simpa only [CategoryTheory.op_id, CategoryTheory.Functor.map_id, Category.comp_id] using he
  have h := extReverse_sourceFunctors L P e
    (Functor.leftUnitor (preadditiveCoyoneda.obj (op P))) hI
    (identity_injective_ext_subsingleton P) η.hom (𝟙 P) he' N q x
  rw [extReverse_identity, Ext.mk₀_id_comp] at h
  exact h.symm

end CategoryTheory.Functor
namespace CategoryTheory.Sheaf.InternalExt

open SheafOfModules.InternalHom

/-- The whole unit-source law retains the original module-unit cohomology comparison. -/
theorem cohomologyExtReverseAfterComparison_unit
    {A B H H' : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup H] [AddCommGroup H']
    (E : A ≃+ H) (E' : B ≃+ H') (r : A →+ B) (rho : H →+ B)
    (hρ : rho = cohomologyExtReverseAfterComparison E r)
    (f : A →+ B) (hr : r = f) (g : H →+ H')
    (hE : ∀ x, E' (f x) = g (E x)) : E'.toAddMonoidHom.comp rho = g := by
  rw [hρ, hr]
  ext y
  obtain ⟨x, rfl⟩ := E.surjective y
  change E' (f (E.symm (E x))) = g (E x)
  rw [E.symm_apply_apply]
  exact hE x

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  (R : Sheaf J CommRingCat.{max c h}) [HasSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max c h})]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasExt.{eM} (SheafOfModulesOfCommRing R)]
  [HasExt.{eA} (Sheaf J AddCommGrpCat.{max c h})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max c h})]
  {T : C} (hT : IsTerminal T)

local instance : EnoughInjectives (SheafOfModulesOfCommRing R) :=
  SheafOfModules.enoughInjectivesLarge.{c, h, 0}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- All-degree unit-source normalization is actual coefficient postcomposition by
internal Hom(unit,N) ≅ N. No global projectivity or target acyclicity is assumed. -/
theorem moduleExtReverse_unit (N : SheafOfModulesOfCommRing R) (q : ℕ) :
    (fun {P : Prop} (_h : P) => P)
      (Functor.extReverseOfLeftExact_unitIso (homFunctor.{c, h, 0} R
        (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
        (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (liftedUnitSourceHomIso.{c, h, 0} R)
        (liftedUnitCoyonedaIso.{c, h, 0} R (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
        (liftedUnitSourceHomIso_coyoneda.{c, h, 0} R).symm
        (homFunctor_injective_ext_subsingleton R hT (SheafOfModules.liftedUnit.{c, h, max c h,
          max c h}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) N q) :=
  Functor.extReverseOfLeftExact_unitIso (homFunctor.{c, h, 0} R
    (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (liftedUnitSourceHomIso.{c, h, 0} R)
    (liftedUnitCoyonedaIso.{c, h, 0} R (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (liftedUnitSourceHomIso_coyoneda.{c, h, 0} R).symm
    (homFunctor_injective_ext_subsingleton R hT (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) N q

/-- The full ordinary-H/unit-source square uses the original module-unit Ext/H
comparison and the original underlying map of the actual internal unit isomorphism. -/
theorem cohomologyExtReverse_unit (N : SheafOfModulesOfCommRing R) (q : ℕ) :
    (fun {P : Prop} (_h : P) => P)
      (cohomologyExtReverseAfterComparison_unit
        (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R
            (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N) q)
        (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT ((sheafCompose J (forget₂
          CommRingCat RingCat)).obj R) N q)
        (moduleExtReverse R hT (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N q)
        (cohomologyExtReverse R hT (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N q) rfl
        ((Ext.mk₀ ((liftedUnitSourceHomIso.{c, h, 0} R).hom.app N)).postcomp
          (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (add_zero q))
        (moduleExtReverse_unit R hT N q)
        (Sheaf.H.map ((SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat
          RingCat)).obj R)).map
          ((liftedUnitSourceHomIso.{c, h, 0} R).hom.app N)) q)
        (ModuleCoefficients.cohomologyMap_naturality hT ((sheafCompose J (forget₂ CommRingCat
          RingCat)).obj R)
          ((liftedUnitSourceHomIso.{c, h, 0} R).hom.app N) q)) :=
  cohomologyExtReverseAfterComparison_unit
    (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R
        (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N) q)
    (ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars hT ((sheafCompose J (forget₂
      CommRingCat RingCat)).obj R) N q)
    (moduleExtReverse R hT (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N q)
    (cohomologyExtReverse R hT (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N q) rfl
    ((Ext.mk₀ ((liftedUnitSourceHomIso.{c, h, 0} R).hom.app N)).postcomp
      (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (add_zero q))
    (moduleExtReverse_unit R hT N q)
    (Sheaf.H.map ((SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      R)).map
      ((liftedUnitSourceHomIso.{c, h, 0} R).hom.app N)) q)
    (ModuleCoefficients.cohomologyMap_naturality hT ((sheafCompose J (forget₂ CommRingCat
      RingCat)).obj R)
      ((liftedUnitSourceHomIso.{c, h, 0} R).hom.app N) q)

end CategoryTheory.Sheaf.InternalExt
