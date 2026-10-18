/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Coefficients

/-!
# The original inverse normal line under coefficient transport

The affine coefficient frame is natural in an actual coefficient morphism
with compatible original sections frames. The same ordered inverse normal
section therefore transports through the actual pullback of that morphism.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u w
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A)
  {L N : (Spec A).Modules} [L.IsQuasicoherent] [N.IsQuasicoherent]
  (f : L ⟶ N) (eL : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  (eN : moduleSpecΓFunctor.obj N ≅ ModuleCat.of A A)
  (he : eL.inv ≫ moduleSpecΓFunctor.map f = eN.inv)

include he in
/-- The actual pulled-back coefficient frame retains its original counit naturality. -/
theorem regularListCoefficientFrameIso_naturality :
    (pullback (Spec.map (regularListQuotientMap s))).map f ≫
        (closedImmersionRegularListCoefficientFrameIso s eN).hom =
      (closedImmersionRegularListCoefficientFrameIso s eL).hom := by
  let q := regularListQuotientMap s
  let P := pullback (Spec.map q)
  let F := ModuleCat.extendScalars q.hom
  let B := regularListQuotientRing s
  let T := tilde.functor B
  let u := (tildeSelf (R := B)).hom
  let cL := asIso L.fromTildeΓ
  let cN := asIso N.fromTildeΓ
  let ε := ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A A) ≪≫
    (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
  have he' : moduleSpecΓFunctor.map f ≫ eN.hom = eL.hom := by
    apply (cancel_epi eL.inv).mp
    rw [← Category.assoc, he, Iso.inv_hom_id, Iso.inv_hom_id]
  have hc := fromTildeΓNatTrans.naturality f
  change (tilde.functor A).map (moduleSpecΓFunctor.map f) ≫ cN.hom = cL.hom ≫ f at hc
  have hf : f ≫ cN.inv =
      cL.inv ≫ (tilde.functor A).map (moduleSpecΓFunctor.map f) := by
    have hi := congrArg (fun z => cL.inv ≫ z ≫ cN.inv) hc
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using hi.symm
  have hp := (tildePullbackIso q).hom.naturality (moduleSpecΓFunctor.map f)
  change P.map ((tilde.functor A).map (moduleSpecΓFunctor.map f)) ≫
      (tildePullbackIso q).hom.app (moduleSpecΓFunctor.obj N) =
    (tildePullbackIso q).hom.app (moduleSpecΓFunctor.obj L) ≫
      T.map (F.map (moduleSpecΓFunctor.map f)) at hp
  change P.map f ≫ P.map cN.inv ≫
      (tildePullbackIso q).hom.app (moduleSpecΓFunctor.obj N) ≫
      T.map (F.map eN.hom ≫ ε.hom) ≫ u =
    P.map cL.inv ≫
      (tildePullbackIso q).hom.app (moduleSpecΓFunctor.obj L) ≫
      T.map (F.map eL.hom ≫ ε.hom) ≫ u
  have hF := congrArg F.map he'
  simp only [Functor.map_comp] at hF
  have hT := congrArg (fun z => T.map (z ≫ ε.hom) ≫ u) hF
  have h₀ := congrArg (fun z => P.map z ≫
    (tildePullbackIso q).hom.app (moduleSpecΓFunctor.obj N) ≫
      T.map (F.map eN.hom ≫ ε.hom) ≫ u) hf
  have h₁ := congrArg (fun z => P.map cL.inv ≫ z ≫
    T.map (F.map eN.hom ≫ ε.hom) ≫ u) hp
  have h₂ := congrArg (fun z => P.map cL.inv ≫
    (tildePullbackIso q).hom.app (moduleSpecΓFunctor.obj L) ≫ z) hT
  calc
    _ = P.map cL.inv ≫ P.map ((tilde.functor A).map (moduleSpecΓFunctor.map f)) ≫
        (tildePullbackIso q).hom.app (moduleSpecΓFunctor.obj N) ≫
          T.map (F.map eN.hom ≫ ε.hom) ≫ u := by
      simpa only [Functor.map_comp, Category.assoc] using h₀
    _ = P.map cL.inv ≫ (tildePullbackIso q).hom.app (moduleSpecΓFunctor.obj L) ≫
        T.map (F.map (moduleSpecΓFunctor.map f)) ≫ T.map (F.map eN.hom ≫ ε.hom) ≫ u := by
      simpa only [Category.assoc] using h₁
    _ = _ := by
      simpa only [Functor.map_comp, Category.assoc] using h₂

include he in
/-- The original inverse coefficient-frame sections transport through the actual pullback. -/
theorem regularListCoefficientSection_naturality (r : regularListQuotientRing s)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    ((pullback (Spec.map (regularListQuotientMap s))).map f).val.app (op U)
        (closedImmersionRegularListCoefficientSection s eL r U) =
      closedImmersionRegularListCoefficientSection s eN r U := by
  have hc := regularListCoefficientFrameIso_naturality s f eL eN he
  have hi : (closedImmersionRegularListCoefficientFrameIso s eL).inv ≫
      (pullback (Spec.map (regularListQuotientMap s))).map f =
    (closedImmersionRegularListCoefficientFrameIso s eN).inv := by
    apply (cancel_mono (closedImmersionRegularListCoefficientFrameIso s eN).hom).mp
    rw [Category.assoc, hc, Iso.inv_hom_id, Iso.inv_hom_id]
  rw [closedImmersionRegularListCoefficientSection_eq,
    closedImmersionRegularListCoefficientSection_eq]
  exact congrArg (fun z => z.val.app (op U)
    (tilde.toOpen (ModuleCat.of (regularListQuotientRing s) (regularListQuotientRing s)) U r)) hi

variable {R : CommRingCat.{u}} (α : R ⟶ A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)

include he in
/-- The same actual inverse normal map is natural in the original coefficient sheaf. -/
theorem regularListInverseNormalLineIso_coefficient :
    (closedImmersionRegularListInverseNormalLineIso α s hs eL).hom ≫
        (moduleTensorLeftFunctor (Spec (regularListQuotientRing s))
          (dualLineBundle _ (closedImmersionRegularListNormalLineBundle α s hs)).val).map
            ((pullback (Spec.map (regularListQuotientMap s))).map f) =
      (closedImmersionRegularListInverseNormalLineIso α s hs eN).hom := by
  let Z := Spec (regularListQuotientRing s)
  let D := (dualLineBundle Z (closedImmersionRegularListNormalLineBundle α s hs)).val
  let P := pullback (Spec.map (regularListQuotientMap s))
  let T := moduleTensorLeftFunctor Z D
  apply (SheafOfModules.unitHomEquiv _).injective
  apply PresheafOfModules.sections_ext
  intro U
  let V := U.unop
  let ell := closedImmersionRegularListNormalDualSection α s hs V
  have hL := closedImmersionRegularListInverseNormalLineIso_section α s hs eL
    (1 : regularListQuotientRing s) V
  have hN := closedImmersionRegularListInverseNormalLineIso_section α s hs eN
    (1 : regularListQuotientRing s) V
  have hmap := moduleTensorLeftFunctor_map_section D (P.map f) V ell
    (closedImmersionRegularListCoefficientSection s eL (1 : regularListQuotientRing s) V)
  have hcoeff := regularListCoefficientSection_naturality s f eL eN he
    (1 : regularListQuotientRing s) V
  change (T.map (P.map f)).val.app (op V)
      ((closedImmersionRegularListInverseNormalLineIso α s hs eL).hom.val.app (op V)
        (1 : Z.ringCatSheaf.obj.obj (op V))) =
    (closedImmersionRegularListInverseNormalLineIso α s hs eN).hom.val.app (op V)
      (1 : Z.ringCatSheaf.obj.obj (op V))
  have hOne := tilde_toOpen_self_one (R := regularListQuotientRing s) V
  have h := (congrArg ((T.map (P.map f)).val.app (op V)) hL).trans
    (hmap.trans ((congrArg (moduleTensorSection Z D (P.obj N) V ell) hcoeff).trans hN.symm))
  exact (congrArg (fun z => (T.map (P.map f)).val.app (op V)
    ((closedImmersionRegularListInverseNormalLineIso α s hs eL).hom.val.app (op V) z))
      hOne).symm.trans (h.trans (congrArg
        ((closedImmersionRegularListInverseNormalLineIso α s hs eN).hom.val.app (op V)) hOne))

private theorem canonicalContraction_coefficient {Z : Scheme.{u}} (C : LineBundle Z)
    (eC : C.val ≅ SheafOfModules.unit Z.ringCatSheaf)
    (eD : (dualLineBundle Z C).val ≅ SheafOfModules.unit Z.ringCatSheaf)
    {Q M N : Z.Modules} (Δ : tensorSheaf Z C.val Q ≅ M) (κ : M ≅ N) :
    (moduleTensorLeftFunctor Z (dualLineBundle Z C).val).map κ.hom ≫
        (normalDeterminantContractionIso C eC eD (Δ ≪≫ κ)).hom =
      (normalDeterminantContractionIso C eC eD Δ).hom := by
  let T := moduleTensorLeftFunctor Z (dualLineBundle Z C).val
  change T.map κ.hom ≫ T.map (κ.inv ≫ Δ.inv) ≫
      ((normalDeterminantTensorAssociator C eC eD).app Q).hom ≫
      (((SheafOfModulesOfCommRing.tensorFunctor Z.sheaf).mapIso
        (dualEvaluationIso Z C)).app Q).hom ≫
      ((SheafOfModulesOfCommRing.tensorLeftUnitIso Z.sheaf).app Q).hom =
    T.map Δ.inv ≫ ((normalDeterminantTensorAssociator C eC eD).app Q).hom ≫
      (((SheafOfModulesOfCommRing.tensorFunctor Z.sheaf).mapIso
        (dualEvaluationIso Z C)).app Q).hom ≫
      ((SheafOfModulesOfCommRing.tensorLeftUnitIso Z.sheaf).app Q).hom
  rw [← T.map_comp_assoc, Iso.hom_inv_id_assoc]

variable [HasExt.{w} (ModuleCat.{u} A)]
  {I : InjectiveResolution L} {J : InjectiveResolution N}
  (E : L ≅ N) (φ : InjectiveResolution.Hom I J E.hom)
  (hE : eL.inv ≫ moduleSpecΓFunctor.map E.hom = eN.inv)
  {Q : (Spec (regularListQuotientRing s)).Modules}
  (Δ : tensorSheaf (Spec (regularListQuotientRing s))
    (closedImmersionRegularListNormalLineBundle α s hs).val Q ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj L)

include hE in
/-- The actual contracted canonical model arrow transports through the original coefficient
isomorphism and its actual resolution lift, with the same normal-first Delta. -/
theorem regularListCanonicalModelTopHomologyIso_coefficient :
    HomologicalComplex.homologyMap
        (((closedImmersionRightAdjoint
          (Spec.map (regularListQuotientMap s))).mapHomologicalComplex (.up ℤ)).map φ.hom')
        (s.length : ℤ) ≫
      (regularListCanonicalModelTopHomologyIso s hs eN α J
        (Δ ≪≫ (pullback (Spec.map (regularListQuotientMap s))).mapIso E)).hom =
    (regularListCanonicalModelTopHomologyIso s hs eL α I Δ).hom := by
  let C := closedImmersionRegularListNormalLineBundle α s hs
  let eC := closedImmersionRegularListNormalFrameIso α s hs
  let eD := closedImmersionRegularListNormalDualFrameIso α s hs
  let κ := (pullback (Spec.map (regularListQuotientMap s))).mapIso E
  let enL := closedImmersionRegularListInverseNormalLineIso α s hs eL
  let enN := closedImmersionRegularListInverseNormalLineIso α s hs eN
  let cL := normalDeterminantContractionIso C eC eD Δ
  let cN := normalDeterminantContractionIso C eC eD (Δ ≪≫ κ)
  have hN := regularListInverseNormalLineIso_coefficient s E.hom eL eN hE α hs
  have hC := canonicalContraction_coefficient C eC eD Δ κ
  have hn : enN.hom ≫ cN.hom = enL.hom ≫ cL.hom := by
    change enL.hom ≫
      (moduleTensorLeftFunctor (Spec (regularListQuotientRing s))
        (dualLineBundle _ C).val).map κ.hom = enN.hom at hN
    rw [← hN, Category.assoc, hC]
  have ht := regularListModelTopHomologyIso_coefficient s hs φ eL eN hE
  have h₀ := congrArg (fun z => z ≫ enN.hom ≫ cN.hom) ht
  have h₁ := congrArg (fun z =>
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs I eL).hom ≫ z) hn
  simpa only [regularListCanonicalModelTopHomologyIso, Iso.trans_hom, Category.assoc] using
    h₀.trans h₁

end AlgebraicGeometry.Scheme.Modules
