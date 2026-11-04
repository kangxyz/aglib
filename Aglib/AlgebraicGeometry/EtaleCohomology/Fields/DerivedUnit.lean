/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.GlobalSectionsUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtalePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Maps from the original field unit to derived module sheaves

Over a separably closed field the original sections functor is exact. The
original field unit therefore represents homology in the native derived
category, with comparison given by the homology map on the actual arrow.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u v w

private theorem single_homology_eq {C : Type u} [Category.{v} C] [Abelian C]
    {P : C} {K : CochainComplex C ℤ} {i : ℤ}
    (f : (CochainComplex.singleFunctor C i).obj P ⟶ K) :
    (singleObjHomologySelfIso (.up ℤ) i P).inv ≫ homologyMap f i =
      (singleObjCyclesSelfIso (.up ℤ) i P).inv ≫ cyclesMap f i ≫ K.homologyπ i := by
  rw [← homologyπ_naturality, singleObjCyclesSelfIso_inv_homologyπ_assoc]

private theorem single_cycles_eq {C : Type u} [Category.{v} C] [Abelian C]
    {P : C} {K : CochainComplex C ℤ} {i : ℤ}
    (f : (CochainComplex.singleFunctor C i).obj P ⟶ K) :
    (singleObjCyclesSelfIso (.up ℤ) i P).inv ≫ cyclesMap f i ≫ K.iCycles i =
      (singleObjXSelf (.up ℤ) i P).inv ≫ f.f i := by
  rw [cyclesMap_i, singleObjCyclesSelfIso_inv_iCycles_assoc]

private theorem projectiveSingle_homology_bijective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : C) [Projective P] (i : ℤ) (K : DerivedCategory C) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor C i).obj P ⟶ K =>
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).inv.app P) ≫
        (DerivedCategory.homologyFunctor C i).map f) := by
  let H := DerivedCategory.homologyFunctor C i
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let L := Q.objPreimage K
  let e : Q.obj L ≅ K := Q.objObjPreimageIso K
  let hL : H.obj K ≅ L.homology i := (H.mapIso e).symm ≪≫
    (DerivedCategory.homologyFunctorFactors C i).app L
  let S := (CochainComplex.singleFunctor C i).obj P
  let eS : (DerivedCategory.singleFunctor C i).obj P ≅ Q.obj S :=
    (DerivedCategory.singleFunctorIsoCompQ C i).app P
  let φ : ((DerivedCategory.singleFunctor C i).obj P ⟶ K) →+ (P ⟶ H.obj K) :=
    { toFun := fun f => (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).inv.app P ≫
        H.map f
      map_zero' := by simp
      map_add' := fun _ _ => by simp }
  have hmap (f : S ⟶ L) :
      φ (eS.hom ≫ Q.map f ≫ e.hom) ≫ hL.hom =
        (singleObjHomologySelfIso (.up ℤ) i P).inv ≫ homologyMap f i := by
    let β := DerivedCategory.homologyFunctorFactors C i
    let bh (J : CochainComplex C ℤ) : H.obj (Q.obj J) ⟶ J.homology i := β.hom.app J
    let bi (J : CochainComplex C ℤ) : J.homology i ⟶ H.obj (Q.obj J) := β.inv.app J
    let a : P ⟶ S.homology i := (singleObjHomologySelfIso (.up ℤ) i P).inv
    have hnat : H.map (Q.map f) ≫ bh L = bh S ≫ homologyMap f i := β.hom.naturality f
    have hs : (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).inv.app P ≫
        H.map eS.hom ≫ bh S = a := by
      calc
        _ = (a ≫ bi S) ≫ (𝟙 (H.obj (Q.obj S))) ≫ bh S := by
          simp only [Functor.id_obj, Functor.comp_obj,
            DerivedCategory.singleFunctorCompHomologyFunctorIso, SingleFunctors.evaluation_obj,
            SingleFunctors.postcomp_functor, DerivedCategory.singleFunctorsPostcompQIso,
            Functor.mapIso_refl, Functor.isoWhiskerRight_refl, Iso.refl_trans, Iso.trans_inv,
            Functor.isoWhiskerLeft_inv, Category.assoc, NatTrans.comp_app,
            homologyFunctorSingleIso_inv_app, DerivedCategory.Q_obj_single_obj,
            Functor.whiskerLeft_app, Functor.associator_inv_app, Category.comp_id,
            DerivedCategory.singleFunctorIsoCompQ, Iso.app_hom, Iso.refl_hom, NatTrans.id_app,
            S, H, Q, eS, bh, β, a, bi]
          exact congrArg (fun z : H.obj (Q.obj S) ⟶ H.obj (Q.obj S) =>
            (a ≫ bi S) ≫ z ≫ bh S) (H.map_id (Q.obj S))
        _ = a := by
          rw [Category.id_comp]
          exact (Category.assoc _ _ _).trans
            ((congrArg (fun z : S.homology i ⟶ S.homology i => a ≫ z)
              (β.inv_hom_id_app S)).trans (Category.comp_id a))
    have he : H.map e.hom ≫ H.map e.inv ≫ bh L = bh L :=
      (H.mapIso e).hom_inv_id_assoc _
    change (_ ≫ H.map (eS.hom ≫ Q.map f ≫ e.hom)) ≫
      H.map e.inv ≫ bh L = _
    simp only [Functor.map_comp, Category.assoc]
    rw [he, hnat]
    simpa only [Category.assoc] using
      congrArg (fun a : P ⟶ S.homology i => a ≫ homologyMap f i) hs
  have hrep (f : (DerivedCategory.singleFunctor C i).obj P ⟶ K) :
      ∃ g : S ⟶ L, eS.hom ≫ Q.map g ≫ e.hom = f := by
    let a : Q.obj S ⟶ Q.obj L := eS.inv ≫ f ≫ e.inv
    obtain ⟨T, _, π, hπ, g, ha⟩ := DerivedCategory.right_fac_of_isStrictlyLE a i
    let : IsIso (Q.map π) := hπ
    let : QuasiIso π := (DerivedCategory.isIso_Q_map_iff_quasiIso C π).mp hπ
    let : IsSplitEpi π := CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective π
    have hi : inv (Q.map π) = Q.map (section_ π) := by
      rw [← cancel_mono (Q.map π), IsIso.inv_hom_id, ← Q.map_comp,
        IsSplitEpi.id, Q.map_id]
    refine ⟨section_ π ≫ g, ?_⟩
    rw [Functor.map_comp, ← hi, ← ha]
    simp [a]
  change Function.Bijective φ
  have hzero (f : (DerivedCategory.singleFunctor C i).obj P ⟶ K) (hf : φ f = 0) : f = 0 := by
    obtain ⟨g, rfl⟩ := hrep f
    let z := (singleObjCyclesSelfIso (.up ℤ) i P).inv ≫ cyclesMap g i
    have hz : z ≫ L.homologyπ i = 0 := by
      simpa only [z, Category.assoc, single_homology_eq g, hf, zero_comp] using (hmap g).symm
    let T := ShortComplex.mk (L.toCycles (i - 1) i) (L.homologyπ i)
      (L.toCycles_comp_homologyπ (i - 1) i)
    have hT : T.Exact := T.exact_of_g_is_cokernel (L.homologyIsCokernel (i - 1) i (by simp))
    let t : P ⟶ L.X (i - 1) := hT.liftFromProjective z hz
    have ht : t ≫ L.toCycles (i - 1) i = z := hT.liftFromProjective_comp z hz
    let s (j k : ℤ) (_ : (ComplexShape.up ℤ).Rel k j) : S.X j ⟶ L.X k :=
      if hj : j = i then
        if hk : k = i - 1 then
          eqToHom (congrArg S.X hj) ≫ (singleObjXSelf (.up ℤ) i P).hom ≫ t ≫
            eqToHom (congrArg L.X hk.symm)
        else 0
      else 0
    have hg : g = Homotopy.nullHomotopicMap' s := by
      apply HomologicalComplex.from_single_hom_ext
      rw [Homotopy.nullHomotopicMap'_f (k₂ := i - 1) (k₀ := i + 1) (by simp) (by simp),
        HomologicalComplex.single_obj_d, zero_comp, zero_add]
      simp only [s, ↓reduceDIte, eqToHom_refl, Category.id_comp, Category.comp_id]
      rw [← L.toCycles_i (i := i - 1) (j := i), Category.assoc, ← Category.assoc t, ht]
      change g.f i = (singleObjXSelf (.up ℤ) i P).hom ≫ z ≫ L.iCycles i
      have hc : z ≫ L.iCycles i = (singleObjXSelf (.up ℤ) i P).inv ≫ g.f i :=
        (Category.assoc _ _ _).trans (single_cycles_eq g)
      rw [hc, Iso.hom_inv_id_assoc]
    rw [hg, DerivedCategory.Q_map_eq_of_homotopy C (Homotopy.nullHomotopy' s)]
    simp
  refine ⟨?_, ?_⟩
  · intro f g h
    apply sub_eq_zero.mp (hzero (f - g) ?_)
    rw [map_sub, h, sub_self]
  · intro y
    let y' := y ≫ hL.hom
    let z := Projective.factorThru y' (L.homologyπ i)
    let f : S ⟶ L := mkHomFromSingle (z ≫ L.iCycles i) (fun j _ => by simp)
    refine ⟨eS.hom ≫ Q.map f ≫ e.hom, (cancel_mono hL.hom).mp ?_⟩
    rw [hmap f, single_homology_eq f, ← Category.assoc]
    have hf : (singleObjCyclesSelfIso (.up ℤ) i P).inv ≫ cyclesMap f i = z := by
      apply (cancel_mono (L.iCycles i)).mp
      rw [Category.assoc, single_cycles_eq f]
      dsimp only [f]
      rw [mkHomFromSingle_f, Iso.inv_hom_id_assoc]
    rw [hf, Projective.factorThru_comp]

section Field

attribute [local instance] hasSheafifyLarge

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] (Λ : Type (u + 1)) [CommRing Λ]

/-- The original field unit represents the actual terminal module sections. -/
def moduleFieldUnitSectionsEquiv (F : ModuleSheaf (Spec (.of Ω)) Λ) :
    (moduleUnit (Spec (.of Ω)) Λ ⟶ F) ≃ (moduleGlobalSections (Spec (.of Ω)) Λ).obj F :=
  (Iso.homCongr (moduleUnitConstantIso (Spec (.of Ω)) Λ).symm
      (Iso.refl F)).trans
    (((moduleGlobalSectionsAdjunction (Spec (.of Ω)) Λ).homEquiv (ModuleCat.of Λ Λ) F).trans
      (ModuleCat.homLinearEquiv (S := Λ).trans (LinearMap.ringLmapEquivSelf Λ Λ _)).toEquiv)

/-- The original unit is projective because terminal sections are exact at a separably closed
field. -/
theorem moduleFieldUnit_projective : Projective (moduleUnit (Spec (.of Ω)) Λ) := by
  let G := moduleGlobalSections (Spec (.of Ω)) Λ
  let : PreservesFiniteColimits G := moduleFieldGlobalSections_preservesFiniteColimits Ω Λ
  let : G.PreservesEpimorphisms := inferInstance
  exact Projective.of_iso (moduleUnitConstantIso (Spec (.of Ω)) Λ)
    ((moduleGlobalSectionsAdjunction (Spec (.of Ω)) Λ).map_projective (ModuleCat.of Λ Λ)
      inferInstance)

variable [HasDerivedCategory.{w} (ModuleSheaf (Spec (.of Ω)) Λ)]

/-- Apply the actual homology functor to a map from the original field unit and evaluate its
value by the original constant-module adjunction. -/
def moduleFieldDerivedUnitHomologyMap (i : ℤ)
    (K : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ))
    (f : (DerivedCategory.Plus.singleFunctor (ModuleSheaf (Spec (.of Ω)) Λ) i).obj
      (moduleUnit (Spec (.of Ω)) Λ) ⟶ K) :
    (moduleGlobalSections (Spec (.of Ω)) Λ).obj
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Spec (.of Ω)) Λ) i).obj K) := by
  let C := ModuleSheaf (Spec (.of Ω)) Λ
  let U : C := moduleUnit (Spec (.of Ω)) Λ
  let H := DerivedCategory.Plus.homologyFunctor C i
  let e : H.obj ((DerivedCategory.Plus.singleFunctor C i).obj U) ≅ U :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).app U
  exact moduleFieldUnitSectionsEquiv Ω Λ (H.obj K) (e.inv ≫ H.map f)

/-- Actual field-unit homology evaluation is bijective in every degree. -/
theorem moduleFieldDerivedUnitHomologyMap_bijective (i : ℤ)
    (K : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ)) :
    Function.Bijective (moduleFieldDerivedUnitHomologyMap Ω Λ i K) := by
  let C := ModuleSheaf (Spec (.of Ω)) Λ
  let U : C := moduleUnit (Spec (.of Ω)) Λ
  let : Projective U := moduleFieldUnit_projective Ω Λ
  let e := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι (C := C))).homEquiv
      (X := (DerivedCategory.Plus.singleFunctor C i).obj U) (Y := K)
  have h := projectiveSingle_homology_bijective U i (DerivedCategory.Plus.ι.obj K)
  exact (moduleFieldUnitSectionsEquiv Ω Λ _).bijective.comp (h.comp e.bijective)

/-- Maps from the original field unit in degree `i` represent degree `i` homology on the
original native bounded-below module category. -/
def moduleFieldDerivedUnitHomologyEquiv (i : ℤ)
    (K : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ)) :
    ((DerivedCategory.Plus.singleFunctor (ModuleSheaf (Spec (.of Ω)) Λ) i).obj
        (moduleUnit (Spec (.of Ω)) Λ) ⟶ K) ≃
      (moduleGlobalSections (Spec (.of Ω)) Λ).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Spec (.of Ω)) Λ) i).obj K) :=
  Equiv.ofBijective _ (moduleFieldDerivedUnitHomologyMap_bijective Ω Λ i K)

/-- The equivalence retains the actual homology evaluation map. -/
theorem moduleFieldDerivedUnitHomologyEquiv_apply (i : ℤ)
    (K : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ))
    (f : (DerivedCategory.Plus.singleFunctor (ModuleSheaf (Spec (.of Ω)) Λ) i).obj
      (moduleUnit (Spec (.of Ω)) Λ) ⟶ K) :
    moduleFieldDerivedUnitHomologyEquiv Ω Λ i K f =
      moduleFieldDerivedUnitHomologyMap Ω Λ i K f :=
  rfl

end Field

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
