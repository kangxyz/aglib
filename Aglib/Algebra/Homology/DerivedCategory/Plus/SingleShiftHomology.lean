/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Shift.ShiftSequence

/-! # Canonical degree-one homology of a shifted single

The original single, homology, and quotient shift conventions give the same
degree-one value for a shifted morphism and its inverse shift adjunct.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem complexSingleShiftBase (U : C) :
    let S0 := (CochainComplex.singleFunctor C 0).obj U
    let S1 := (CochainComplex.singleFunctor C 1).obj U
    let η : S0⟦(-1 : ℤ)⟧ ≅ S1 :=
      ((CochainComplex.singleFunctors C).shiftIso (-1) 1 0 (by omega)).app U
    let adj : shiftFunctor (CochainComplex C ℤ) (-1 : ℤ) ⊣
        shiftFunctor (CochainComplex C ℤ) (1 : ℤ) :=
      by exact (shiftEquiv' (CochainComplex C ℤ) (-1) 1 (by omega)).toAdjunction
    let z0 : ShiftedHom S0 S1 (1 : ℤ) := (adj.homEquiv S0 S1) η.hom
    (singleObjHomologySelfIso (.up ℤ) 1 U).inv =
      (singleObjHomologySelfIso (.up ℤ) 0 U).inv ≫
        (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap z0 0 1 (by omega) := by
  intro S0 S1 η adj z0
  have hunit : (adj.unit.app S0).f 0 = 𝟙 (S0.X 0) := by
    change ((shiftFunctorCompIsoId (CochainComplex C ℤ) (-1) 1 (by omega)).inv.app S0).f 0 = _
    simp [shiftFunctorCompIsoId, CochainComplex.shiftFunctorAdd'_hom_app_f',
      CochainComplex.shiftFunctorZero_inv_app_f, HomologicalComplex.XIsoOfEq]
  have hcomponent : (singleObjXSelf (.up ℤ) 0 U).inv ≫ z0.f 0 ≫
      (singleObjXSelf (.up ℤ) 1 U).hom = 𝟙 U := by
    simp only [z0, η, Adjunction.homEquiv_apply, Category.assoc,
      CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctor_obj_X', Int.reduceAdd,
      HomologicalComplex.comp_f]
    rw [hunit]
    simp only [singleObjXSelf, singleObjXIsoOfEq, single, Int.reduceNeg, Functor.comp_obj,
      CochainComplex.shiftFunctor_obj_X', Int.reduceAdd, NatIso.ofComponents.app,
      Hom.isoOfComponents_hom_f, eqToIso_refl, Iso.refl_hom]
    simp only [Iso.refl_inv]
    change 𝟙 U ≫ 𝟙 U ≫ 𝟙 U ≫ 𝟙 U = 𝟙 U
    simp only [Category.id_comp]
  let F0 := HomologicalComplex.shortComplexFunctor C (.up ℤ) 0
  let F1 := HomologicalComplex.shortComplexFunctor C (.up ℤ) 1
  let ψ : F0.obj S0 ⟶ F1.obj S1 :=
    F0.map z0 ≫ (CochainComplex.shiftShortComplexFunctorIso C 1 0 1 (by omega)).hom.app S1
  have hshift : ((CochainComplex.shiftShortComplexFunctorIso C 1 0 1 (by omega)).hom.app S1).τ₂ =
      𝟙 ((S1⟦(1 : ℤ)⟧).X 0) := by
    simp [CochainComplex.shiftShortComplexFunctorIso,
      CochainComplex.shiftShortComplexFunctor', CochainComplex.shiftEval,
      HomologicalComplex.XIsoOfEq]
  have hψmid : (singleObjXSelf (.up ℤ) 0 U).inv ≫ ψ.τ₂ ≫
      (singleObjXSelf (.up ℤ) 1 U).hom = 𝟙 U := by
    change (singleObjXSelf (.up ℤ) 0 U).inv ≫
      (z0.f 0 ≫ ((CochainComplex.shiftShortComplexFunctorIso C 1 0 1 (by omega)).hom.app S1).τ₂) ≫
        (singleObjXSelf (.up ℤ) 1 U).hom = 𝟙 U
    rw [hshift]
    simpa only [Category.comp_id] using hcomponent
  have hmap : (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap
      z0 0 1 (by omega) = ShortComplex.homologyMap ψ := by
    let H := HomologicalComplex.homologyFunctor C (.up ℤ) 0
    have hm0 : (H.shift (0 : ℤ)).map z0 = ShortComplex.homologyMap (F0.map z0) := rfl
    have hs : (H.shiftIso (1 : ℤ) 0 1 (by omega)).hom.app S1 =
        ShortComplex.homologyMap
          ((CochainComplex.shiftShortComplexFunctorIso C 1 0 1 (by omega)).hom.app S1) :=
      CochainComplex.ShiftSequence.shiftIso_hom_app (C := C) 1 0 1 (by omega) S1
    rw [Functor.shiftMap, hm0, hs]
    exact (ShortComplex.homologyMap_comp _ _).symm
  let e0 := singleObjHomologySelfIso (.up ℤ) 0 U
  let e1 := singleObjHomologySelfIso (.up ℤ) 1 U
  have hmid : ψ.τ₂ ≫ (singleObjXSelf (.up ℤ) 1 U).hom =
      (singleObjXSelf (.up ℤ) 0 U).hom := by
    apply (cancel_epi (singleObjXSelf (.up ℤ) 0 U).inv).mp
    simpa only [Category.assoc] using hψmid.trans
      (singleObjXSelf (.up ℤ) 0 U).inv_hom_id.symm
  have hcore : ShortComplex.homologyMap ψ ≫ e1.hom = e0.hom := by
    have : IsIso (S0.homologyπ 0) := S0.isIso_homologyπ _ 0 rfl rfl
    apply (cancel_epi (S0.homologyπ 0)).mp
    change (F0.obj S0).homologyπ ≫ ShortComplex.homologyMap ψ ≫ e1.hom =
      S0.homologyπ 0 ≫ e0.hom
    rw [ShortComplex.homologyπ_naturality_assoc ψ]
    rw [homologyπ_singleObjHomologySelfIso_hom]
    change ShortComplex.cyclesMap ψ ≫ S1.homologyπ 1 ≫ e1.hom =
      (singleObjCyclesSelfIso (.up ℤ) 0 U).hom
    rw [homologyπ_singleObjHomologySelfIso_hom]
    rw [singleObjCyclesSelfIso_hom, singleObjCyclesSelfIso_hom]
    change ShortComplex.cyclesMap ψ ≫ (F1.obj S1).iCycles ≫
        (singleObjXSelf (.up ℤ) 1 U).hom =
      (F0.obj S0).iCycles ≫ (singleObjXSelf (.up ℤ) 0 U).hom
    rw [ShortComplex.cyclesMap_i_assoc]
    rw [hmid]
  rw [hmap]
  calc
    e1.inv = e0.inv ≫ e0.hom ≫ e1.inv := by simp
    _ = e0.inv ≫ (ShortComplex.homologyMap ψ ≫ e1.hom) ≫ e1.inv := by rw [hcore]
    _ = e0.inv ≫ ShortComplex.homologyMap ψ := by simp [Category.assoc]
end

open CategoryTheory CategoryTheory.Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem derivedSingleShiftBase (U : C) :
    let S0 := (DerivedCategory.singleFunctor C 0).obj U
    let S1 := (DerivedCategory.singleFunctor C 1).obj U
    let η := ((DerivedCategory.singleFunctors C).shiftIso (-1) 1 0 (by omega)).app U
    let adj := (shiftEquiv' (DerivedCategory C) (-1) 1 (by omega)).toAdjunction
    let z0 : ShiftedHom S0 S1 (1 : ℤ) := (adj.homEquiv S0 S1) η.hom
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 1).inv.app U =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app U ≫
        (DerivedCategory.homologyFunctor C 0).shiftMap z0 0 1 (by omega) := by
  intro S0 S1 η adj z0
  let V0 := (CochainComplex.singleFunctor C 0).obj U
  let V1 := (CochainComplex.singleFunctor C 1).obj U
  let ε := ((CochainComplex.singleFunctors C).shiftIso (-1) 1 0 (by omega)).app U
  let cadj := (shiftEquiv' (CochainComplex C ℤ) (-1) 1 (by omega)).toAdjunction
  let v0 : ShiftedHom V0 V1 (1 : ℤ) := (cadj.homEquiv V0 V1) ε.hom
  have ho0 : DerivedCategory.Q.obj V0 = S0 := by rfl
  have ho1 : DerivedCategory.Q.obj V1 = S1 := by rfl
  have hη : η.hom = (DerivedCategory.Q.commShiftIso (-1)).inv.app V0 ≫
      DerivedCategory.Q.map ε.hom := by
    change (((CochainComplex.singleFunctors C).postcomp DerivedCategory.Q).shiftIso
      (-1) 1 0 (by omega)).hom.app U = _
    exact SingleFunctors.postcomp_shiftIso_hom_app
      (CochainComplex.singleFunctors C) DerivedCategory.Q (-1) 1 0 (by omega) U
  have hu : DerivedCategory.Q.map (cadj.unit.app V0) =
      adj.unit.app S0 ≫
        ((DerivedCategory.Q.commShiftIso (-1)).inv.app V0)⟦(1 : ℤ)⟧' ≫
          (DerivedCategory.Q.commShiftIso 1).inv.app (V0⟦(-1 : ℤ)⟧) := by
    change DerivedCategory.Q.map
      ((shiftFunctorCompIsoId (CochainComplex C ℤ) (-1) 1 (by omega)).inv.app V0) = _
    exact Functor.map_shiftFunctorCompIsoId_inv_app
      DerivedCategory.Q V0 (-1) 1 (by omega)
  have hz : v0.map DerivedCategory.Q = z0 := by
    change DerivedCategory.Q.map
        (cadj.unit.app V0 ≫ (shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map ε.hom) ≫
        (DerivedCategory.Q.commShiftIso 1).hom.app V1 =
      adj.unit.app S0 ≫ (shiftFunctor (DerivedCategory C) (1 : ℤ)).map η.hom
    rw [Functor.map_comp, hu]
    simp only [Category.assoc]
    rw [DerivedCategory.Q.commShiftIso_hom_naturality ε.hom (1 : ℤ)]
    erw [Iso.inv_hom_id_app_assoc]
    simp only [hη, Functor.map_comp]
  have hc := complexSingleShiftBase (C := C) U
  dsimp only at hc
  have he0 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app U =
      (singleObjHomologySelfIso (.up ℤ) 0 U).inv ≫
        (DerivedCategory.homologyFunctorFactors C 0).inv.app V0 := by
    simp [DerivedCategory.singleFunctorCompHomologyFunctorIso]
    rfl
  have he1 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C 1).inv.app U =
      (singleObjHomologySelfIso (.up ℤ) 1 U).inv ≫
        (DerivedCategory.homologyFunctorFactors C 1).inv.app V1 := by
    simp [DerivedCategory.singleFunctorCompHomologyFunctorIso]
    rfl
  have hshift := DerivedCategory.shiftMap_homologyFunctor_map_Q v0 0 1 (by omega)
  have hc' : (singleObjHomologySelfIso (.up ℤ) 1 U).inv =
      (singleObjHomologySelfIso (.up ℤ) 0 U).inv ≫
        (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap v0 0 1 (by omega) := by
    exact hc
  have hshift' : (DerivedCategory.homologyFunctor C 0).shiftMap z0 0 1 (by omega) =
      (DerivedCategory.homologyFunctorFactors C 0).hom.app V0 ≫
        (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap v0 0 1 (by omega) ≫
          (DerivedCategory.homologyFunctorFactors C 1).inv.app V1 := by
    rw [← hz]
    exact hshift
  rw [he0, he1, hshift']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ (DerivedCategory.homologyFunctorFactors C 1).inv.app V1) hc'
end

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem shiftedSingleHomologyOne_of_base (U : C)
    (hbase : let S0 := (singleFunctor C 0).obj U
      let S1 := (singleFunctor C 1).obj U
      let η := ((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app U
      let adj := (shiftEquiv' (Plus C) (-1) 1 (by omega)).toAdjunction
      let z0 : ShiftedHom S0 S1 (1 : ℤ) := (adj.homEquiv S0 S1) η.hom
      (singleFunctorCompHomologyFunctorIso (C := C) 1).inv.app U =
        (singleFunctorCompHomologyFunctorIso (C := C) 0).inv.app U ≫
          (homologyFunctor C 0).shiftMap z0 0 1 (by omega))
    (K : Plus C)
    (z : ShiftedHom ((singleFunctor C 0).obj U) K (1 : ℤ)) :
    let η := ((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app U
    let x := η.inv ≫
      (((shiftEquiv' (Plus C) (-1) 1 (by omega)).toAdjunction.homEquiv
        ((singleFunctor C 0).obj U) K).symm z)
    (singleFunctorCompHomologyFunctorIso (C := C) 1).inv.app U ≫
        (homologyFunctor C 1).map x =
      (singleFunctorCompHomologyFunctorIso (C := C) 0).inv.app U ≫
        (homologyFunctor C 0).shiftMap z 0 1 (by omega) := by
  intro η x
  let S0 := (singleFunctor C 0).obj U
  let S1 := (singleFunctor C 1).obj U
  let adj := (shiftEquiv' (Plus C) (-1) 1 (by omega)).toAdjunction
  let z0 : ShiftedHom S0 S1 (1 : ℤ) := (adj.homEquiv S0 S1) η.hom
  dsimp only at hbase
  let j := (adj.homEquiv S0 K).symm z
  have hx : η.hom ≫ x = j := by
    dsimp only [x, j, η, adj, S0]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hz : z = z0 ≫ x⟦(1 : ℤ)⟧' := by
    calc
      z = (adj.homEquiv S0 K) j := ((adj.homEquiv S0 K).apply_symm_apply z).symm
      _ = (adj.homEquiv S0 K) (η.hom ≫ x) := by rw [hx]
      _ = z0 ≫ x⟦(1 : ℤ)⟧' := adj.homEquiv_naturality_right η.hom x
  rw [hz, (homologyFunctor C 0).shiftMap_comp z0 x 0 1 (by omega)]
  rw [← Category.assoc]
  rw [← hbase]
  rfl

end DerivedCategory.Plus
end

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DerivedCategory.Plus

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem homology_shiftMap_full
    {K L : Plus C} {q : ℤ} (t : ShiftedHom K L q) :
    (homologyFunctor C 0).shiftMap t (0 : ℤ) q (by omega) =
      (DerivedCategory.homologyFunctor C 0).shiftMap
        (t.map Plus.ι) (0 : ℤ) q (by omega) := by
  let H := DerivedCategory.homologyFunctor C 0
  let ι : Plus C ⥤ DerivedCategory C := Plus.ι
  let c : (L⟦q⟧).obj ⟶ L.obj⟦q⟧ := (ι.commShiftIso q).hom.app L
  let e : H.obj (L.obj⟦q⟧) ≅
      (DerivedCategory.homologyFunctor C q).obj L.obj :=
    (H.shiftIso q (0 : ℤ) q (by omega)).app L.obj
  change H.map t.hom ≫ (𝟙 _ ≫ H.map c ≫ 𝟙 _ ≫ e.hom) =
    H.map (t.hom ≫ c) ≫ e.hom
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]

private theorem plusSingleShiftBase (U : C) :
    let S0 := (singleFunctor C 0).obj U
    let S1 := (singleFunctor C 1).obj U
    let η := ((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app U
    let adj := (shiftEquiv' (Plus C) (-1) 1 (by omega)).toAdjunction
    let z0 : ShiftedHom S0 S1 (1 : ℤ) := (adj.homEquiv S0 S1) η.hom
    (singleFunctorCompHomologyFunctorIso (C := C) 1).inv.app U =
      (singleFunctorCompHomologyFunctorIso (C := C) 0).inv.app U ≫
        (homologyFunctor C 0).shiftMap z0 0 1 (by omega) := by
  intro S0 S1 η adj z0
  let ι : Plus C ⥤ DerivedCategory C := Plus.ι
  let D0 := (DerivedCategory.singleFunctor C 0).obj U
  let D1 := (DerivedCategory.singleFunctor C 1).obj U
  let θ := ((DerivedCategory.singleFunctors C).shiftIso (-1) 1 0 (by omega)).app U
  let dadj := (shiftEquiv' (DerivedCategory C) (-1) 1 (by omega)).toAdjunction
  let d0 : ShiftedHom D0 D1 (1 : ℤ) := (dadj.homEquiv D0 D1) θ.hom
  have ho0 : ι.obj S0 = D0 := by rfl
  have ho1 : ι.obj S1 = D1 := by rfl
  have hη : ι.map η.hom = (ι.commShiftIso (-1)).hom.app S0 ≫ θ.hom := by
    simp [η, singleFunctors, SingleFunctors.lift, SingleFunctors.lift.shiftIso]
    rfl
  have hu : ι.map (adj.unit.app S0) =
      dadj.unit.app D0 ≫
        ((ι.commShiftIso (-1)).inv.app S0)⟦(1 : ℤ)⟧' ≫
          (ι.commShiftIso 1).inv.app (S0⟦(-1 : ℤ)⟧) := by
    change ι.map ((shiftFunctorCompIsoId (Plus C) (-1) 1 (by omega)).inv.app S0) = _
    exact Functor.map_shiftFunctorCompIsoId_inv_app ι S0 (-1) 1 (by omega)
  have hz : z0.map ι = d0 := by
    change ι.map (adj.unit.app S0 ≫ (shiftFunctor (Plus C) (1 : ℤ)).map η.hom) ≫
        (ι.commShiftIso 1).hom.app S1 =
      dadj.unit.app D0 ≫ (shiftFunctor (DerivedCategory C) (1 : ℤ)).map θ.hom
    rw [Functor.map_comp, hu]
    simp only [Category.assoc]
    rw [ι.commShiftIso_hom_naturality η.hom (1 : ℤ)]
    erw [Iso.inv_hom_id_app_assoc]
    simp only [hη, Functor.map_comp]
    simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  have hshift := homology_shiftMap_full z0
  rw [hz] at hshift
  have hd := derivedSingleShiftBase (C := C) U
  dsimp only at hd
  rw [hshift]
  exact hd

/-- The original degree-zero shifted map agrees with the original degree-one
homology value of its inverse shift adjunct under the canonical singles. -/
theorem shiftedSingleHomologyOne (U : C) (K : Plus C)
    (z : ShiftedHom ((singleFunctor C 0).obj U) K (1 : ℤ)) :
    let η := ((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app U
    let x := η.inv ≫
      (((shiftEquiv' (Plus C) (-1) 1 (by omega)).toAdjunction.homEquiv
        ((singleFunctor C 0).obj U) K).symm z)
    (singleFunctorCompHomologyFunctorIso (C := C) 1).inv.app U ≫
        (homologyFunctor C 1).map x =
      (singleFunctorCompHomologyFunctorIso (C := C) 0).inv.app U ≫
        (homologyFunctor C 0).shiftMap z 0 1 (by omega) := by
  exact shiftedSingleHomologyOne_of_base U (plusSingleShiftBase U) K z

end DerivedCategory.Plus
end

end
