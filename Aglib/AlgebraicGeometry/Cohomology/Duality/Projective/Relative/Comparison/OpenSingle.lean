/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.OpenAdjunction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.CochainComplexPlus.Shift

/-!
# The original affine-open restriction map at native singles

Transport the original cochain restriction/counit bijection through the
installed single-complex and integer-shift comparisons. The resulting map
retains the exact-single comparison and the original ordinary counit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

local instance openRestrictionUnit_isIso :
    IsIso (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusUnit :=
  (Scheme.Modules.restrictFunctor j).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology

private theorem openSingleFunctorPlus_map {M N : U.Modules} (n : ℤ) (s : M ⟶ N) :
    (DerivedCategory.Plus.singleFunctor U.Modules n).map s =
      DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus U.Modules n).map s) := by
  apply DerivedCategory.Plus.ι.map_injective
  rfl

/-- The original derived restriction map, the installed exact-single comparison,
and the original restriction counit, with the native shifted-Hom map. -/
def openSingleDerivedHomRestriction (L : U.Modules)
    (K : CochainComplex.Plus Y.Modules) (n k : ℤ)
    (a : ShiftedHom (DerivedCategory.Plus.Q.obj K)
      ((DerivedCategory.Plus.singleFunctor Y.Modules n).obj
        ((Scheme.Modules.pushforward j).obj L)) k) :
    ShiftedHom ((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj K))
      ((DerivedCategory.Plus.singleFunctor U.Modules n).obj L) k :=
  a.map (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus ≫
    (((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusSingleIso n).hom.app
        ((Scheme.Modules.pushforward j).obj L) ≫
      (DerivedCategory.Plus.singleFunctor U.Modules n).map
        ((Scheme.Modules.restrictAdjunction j).counit.app L))⟦k⟧'

private def openCochainCounitNat :
    (Scheme.Modules.pushforward j).mapCochainComplexPlus ⋙
      (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus ⟶
        𝟭 (CochainComplex.Plus U.Modules) :=
  NatTrans.mapCochainComplexPlus (Scheme.Modules.restrictAdjunction j).counit

private def openCochainIdentityIso :
    (𝟭 U.Modules).mapCochainComplexPlus ≅ 𝟭 (CochainComplex.Plus U.Modules) :=
  NatIso.ofComponents
    (fun S => (CochainComplex.plus U.Modules).isoMk
      ((Functor.mapHomologicalComplexIdIso U.Modules (.up ℤ)).app S.obj))
    (by
      intro S T r
      apply ObjectProperty.hom_ext
      exact (Functor.mapHomologicalComplexIdIso U.Modules (.up ℤ)).hom.naturality r.hom)

private instance openCochainIdentityIso_commShift :
    (openCochainIdentityIso (U := U)).hom.CommShift ℤ := by
  refine NatTrans.CommShift.of_comp_faithful (CochainComplex.Plus.ι U.Modules) (h := ?_)
  have he : Functor.whiskerRight (openCochainIdentityIso (U := U)).hom
      (CochainComplex.Plus.ι U.Modules) =
      (𝟭 U.Modules).mapCochainComplexPlusCompι.hom ≫
        Functor.whiskerLeft (CochainComplex.Plus.ι U.Modules)
          (Functor.mapHomologicalComplexIdIso U.Modules (.up ℤ)).hom ≫
        (Functor.rightUnitor (CochainComplex.Plus.ι U.Modules)).hom ≫
        (Functor.leftUnitor (CochainComplex.Plus.ι U.Modules)).inv := by
    apply NatTrans.ext
    funext S
    apply HomologicalComplex.Hom.ext
    funext i
    simp [openCochainIdentityIso, Functor.mapHomologicalComplexIdIso]
  rw [he]
  infer_instance

private instance openCochainCounitNat_commShift :
    (openCochainCounitNat j).CommShift ℤ := by
  have he : openCochainCounitNat j =
      (Functor.mapCochainComplexPlusCompIso (Scheme.Modules.pushforward j)
        (Scheme.Modules.restrictFunctor j)).inv ≫
      NatTrans.mapCochainComplexPlus (Scheme.Modules.restrictAdjunction j).counit ≫
      (openCochainIdentityIso (U := U)).hom := by
    apply NatTrans.ext
    funext S
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.Hom.ext
    funext i
    simp [openCochainCounitNat, Functor.mapCochainComplexPlusCompIso,
      openCochainIdentityIso, Functor.mapHomologicalComplexIdIso]
  rw [he]
  infer_instance

private theorem openCochainCounitNat_app (S : CochainComplex.Plus U.Modules) :
    (openCochainCounitNat j).app S = openCochainCounitPlus j S := rfl

private def openRestrictionCounitNat :
    (Scheme.Modules.pushforward j).mapCochainComplexPlus ⋙
      (DerivedCategory.Plus.Q ⋙ (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus) ⟶
        DerivedCategory.Plus.Q := by
  let F := Scheme.Modules.restrictFunctor j
  let G := Scheme.Modules.pushforward j
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact inv (Functor.whiskerLeft G.mapCochainComplexPlus F.rightDerivedFunctorPlusUnit) ≫
    (Functor.associator G.mapCochainComplexPlus F.mapCochainComplexPlus
      DerivedCategory.Plus.Q).inv ≫
    Functor.whiskerRight (openCochainCounitNat j) DerivedCategory.Plus.Q ≫
    (Functor.leftUnitor DerivedCategory.Plus.Q).hom

private instance openRestrictionCounitNat_commShift :
    (openRestrictionCounitNat j).CommShift ℤ := by
  let F := Scheme.Modules.restrictFunctor j
  let G := Scheme.Modules.pushforward j
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let : (inv (Functor.whiskerLeft G.mapCochainComplexPlus
      F.rightDerivedFunctorPlusUnit)).CommShift ℤ :=
    NatTrans.CommShift.of_isIso _ _
  dsimp only [openRestrictionCounitNat]
  infer_instance

private theorem openRestrictionCounitNat_app (S : CochainComplex.Plus U.Modules) :
    (openRestrictionCounitNat j).app S =
      inv ((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward j).mapCochainComplexPlus.obj S)) ≫
      DerivedCategory.Plus.Q.map (openCochainCounitPlus j S) := by
  simp only [openRestrictionCounitNat, NatTrans.comp_app, NatIso.isIso_inv_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.id_comp,
    openCochainCounitNat_app]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

private theorem openDerivedRestrictionCounit_bijective_of_iso
    (K : CochainComplex.Plus Y.Modules) {S T : CochainComplex.Plus U.Modules}
    (e : S ≅ T) (hT : Function.Bijective (openDerivedRestrictionCounit j K T)) :
    Function.Bijective (openDerivedRestrictionCounit j K S) := by
  let E₁ := Iso.homCongr (Iso.refl (DerivedCategory.Plus.Q.obj K))
    (((Scheme.Modules.pushforward j).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).mapIso e)
  let E₂ := Iso.homCongr
    (Iso.refl (DerivedCategory.Plus.Q.obj
      ((Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj K)))
    (DerivedCategory.Plus.Q.mapIso e)
  have heq : E₂ ∘ openDerivedRestrictionCounit j K S =
      openDerivedRestrictionCounit j K T ∘ E₁ := by
    funext a
    change 𝟙 _ ≫ openDerivedRestrictionCounit j K S a ≫ DerivedCategory.Plus.Q.map e.hom =
      openDerivedRestrictionCounit j K T (𝟙 _ ≫ a ≫ DerivedCategory.Plus.Q.map
        ((Scheme.Modules.pushforward j).mapCochainComplexPlus.map e.hom))
    simp only [Category.id_comp]
    exact openDerivedRestrictionCounit_naturality j K e.hom a
  have hb := hT.comp E₁.bijective
  rw [← heq] at hb
  exact (Equiv.comp_bijective (openDerivedRestrictionCounit j K S) E₂).mp hb

private def openSingleCochainShiftIso (L : U.Modules) (n k : ℤ) :
    (((CochainComplex.singleFunctorPlus U.Modules n).obj L)⟦k⟧) ≅
      (((CochainComplex.singleFunctorPlus U.Modules 0).obj L)⟦k - n⟧) :=
  (CochainComplex.plus U.Modules).isoMk
    (((CochainComplex.Plus.ι U.Modules).commShiftIso k).app
        ((CochainComplex.singleFunctorPlus U.Modules n).obj L) ≪≫
      ((CochainComplex.singleFunctors U.Modules).shiftIso k (n - k) n (by omega)).app L ≪≫
      (((CochainComplex.singleFunctors U.Modules).shiftIso (k - n) (n - k) 0
        (by omega)).app L).symm ≪≫
      (((CochainComplex.Plus.ι U.Modules).commShiftIso (k - n)).app
        ((CochainComplex.singleFunctorPlus U.Modules 0).obj L)).symm)

private theorem affineOpenDerivedRestrictionCounit_single_bijective [IsAffineHom j]
    (L : U.Modules) [L.IsQuasicoherent] (K : CochainComplex.Plus Y.Modules) (n k : ℤ) :
    Function.Bijective (openDerivedRestrictionCounit j K
      (((CochainComplex.singleFunctorPlus U.Modules n).obj L)⟦k⟧)) :=
  openDerivedRestrictionCounit_bijective_of_iso j K (openSingleCochainShiftIso L n k)
    (affineOpenDerivedRestrictionCounit_bijective j L K (k - n))

private def openSinglePushforwardCochainIso (L : U.Modules) (n : ℤ) :
    (Scheme.Modules.pushforward j).mapCochainComplexPlus.obj
        ((CochainComplex.singleFunctorPlus U.Modules n).obj L) ≅
      (CochainComplex.singleFunctorPlus Y.Modules n).obj
        ((Scheme.Modules.pushforward j).obj L) :=
  (CochainComplex.plus Y.Modules).isoMk
    ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pushforward j)
      (.up ℤ) n).app L)

private theorem openSingleCochainCounit (L : U.Modules) (n : ℤ) :
    openCochainCounitPlus j ((CochainComplex.singleFunctorPlus U.Modules n).obj L) =
      (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.map
          (openSinglePushforwardCochainIso j L n).hom ≫
        (show (Scheme.Modules.restrictFunctor j).mapCochainComplexPlus.obj
              ((CochainComplex.singleFunctorPlus Y.Modules n).obj
                ((Scheme.Modules.pushforward j).obj L)) ⟶
            (CochainComplex.singleFunctorPlus U.Modules n).obj
              ((Scheme.Modules.restrictFunctor j).obj ((Scheme.Modules.pushforward j).obj L)) from
          ObjectProperty.homMk
            ((HomologicalComplex.singleMapHomologicalComplex
              (Scheme.Modules.restrictFunctor j) (.up ℤ) n).hom.app
                ((Scheme.Modules.pushforward j).obj L))) ≫
        (CochainComplex.singleFunctorPlus U.Modules n).map
          ((Scheme.Modules.restrictAdjunction j).counit.app L) := by
  apply ObjectProperty.hom_ext
  change (NatTrans.mapHomologicalComplex (Scheme.Modules.restrictAdjunction j).counit
      (.up ℤ)).app ((HomologicalComplex.single U.Modules (.up ℤ) n).obj L) =
    ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pushforward j)
          (.up ℤ) n).hom.app L) ≫
      (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.restrictFunctor j)
        (.up ℤ) n).hom.app ((Scheme.Modules.pushforward j).obj L) ≫
      (HomologicalComplex.single U.Modules (.up ℤ) n).map
        ((Scheme.Modules.restrictAdjunction j).counit.app L)
  rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj,
    HomologicalComplex.singleMapHomologicalComplex_comp_hom_app,
    HomologicalComplex.singleMapHomologicalComplex_id_inv_app]
  apply HomologicalComplex.Hom.ext
  funext i
  simp [Functor.mapHomologicalComplexCompIso, Functor.mapHomologicalComplexIdIso]

private theorem openRestrictionCounitNat_single (L : U.Modules) (n : ℤ) :
    (openRestrictionCounitNat j).app ((CochainComplex.singleFunctorPlus U.Modules n).obj L) =
      (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (openSinglePushforwardCochainIso j L n).hom) ≫
        ((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusSingleIso n).hom.app
          ((Scheme.Modules.pushforward j).obj L) ≫
        (DerivedCategory.Plus.singleFunctor U.Modules n).map
          ((Scheme.Modules.restrictAdjunction j).counit.app L) := by
  let F := Scheme.Modules.restrictFunctor j
  let G := Scheme.Modules.pushforward j
  let S := (CochainComplex.singleFunctorPlus U.Modules n).obj L
  let b := (openSinglePushforwardCochainIso j L n).hom
  have hn := F.rightDerivedFunctorPlusUnit.naturality b
  change DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map b) ≫
      F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus Y.Modules n).obj
        (G.obj L)) = F.rightDerivedFunctorPlusUnit.app (G.mapCochainComplexPlus.obj S) ≫
          F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map b) at hn
  apply (cancel_epi (F.rightDerivedFunctorPlusUnit.app (G.mapCochainComplexPlus.obj S))).mp
  rw [openRestrictionCounitNat_app, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [F.rightDerivedFunctorPlusSingleIso_unit_assoc]
  rw [openSingleFunctorPlus_map]
  have hc := congrArg (DerivedCategory.Plus.Q (C := U.Modules)).map (openSingleCochainCounit j L n)
  simpa only [Functor.map_comp, Category.assoc] using hc

private theorem openRestrictionCounitNat_shift (S : CochainComplex.Plus U.Modules) (k : ℤ) :
    (openRestrictionCounitNat j).app (S⟦k⟧) ≫
        ((DerivedCategory.Plus.Q (C := U.Modules)).commShiftIso k).hom.app S =
      (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus.map
          ((((Scheme.Modules.pushforward j).mapCochainComplexPlus ⋙
            DerivedCategory.Plus.Q).commShiftIso k).hom.app S) ≫
        ((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus.commShiftIso k).hom.app
          (DerivedCategory.Plus.Q.obj
            ((Scheme.Modules.pushforward j).mapCochainComplexPlus.obj S)) ≫
        ((openRestrictionCounitNat j).app S)⟦k⟧' := by
  simpa only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.map_comp,
    Category.assoc] using
    (NatTrans.shift_app_comm (openRestrictionCounitNat j) k S).symm

private def openSinglePushforwardDerivedShiftIso (L : U.Modules) (n k : ℤ) :
    DerivedCategory.Plus.Q.obj ((Scheme.Modules.pushforward j).mapCochainComplexPlus.obj
        (((CochainComplex.singleFunctorPlus U.Modules n).obj L)⟦k⟧)) ≅
      (((DerivedCategory.Plus.singleFunctor Y.Modules n).obj
        ((Scheme.Modules.pushforward j).obj L))⟦k⟧) :=
  (((Scheme.Modules.pushforward j).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q).commShiftIso k).app
      ((CochainComplex.singleFunctorPlus U.Modules n).obj L) ≪≫
    (shiftFunctor (DerivedCategory.Plus Y.Modules) k).mapIso
      (DerivedCategory.Plus.Q.mapIso (openSinglePushforwardCochainIso j L n))

private theorem openSingleDerivedHomRestriction_transport
    (L : U.Modules) (K : CochainComplex.Plus Y.Modules) (n k : ℤ)
    (a : DerivedCategory.Plus.Q.obj K ⟶ DerivedCategory.Plus.Q.obj
      ((Scheme.Modules.pushforward j).mapCochainComplexPlus.obj
        (((CochainComplex.singleFunctorPlus U.Modules n).obj L)⟦k⟧))) :
    (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus.map a ≫
        (openRestrictionCounitNat j).app
          (((CochainComplex.singleFunctorPlus U.Modules n).obj L)⟦k⟧) ≫
        ((DerivedCategory.Plus.Q (C := U.Modules)).commShiftIso k).hom.app
          ((CochainComplex.singleFunctorPlus U.Modules n).obj L) =
      openSingleDerivedHomRestriction j L K n k
        (a ≫ (openSinglePushforwardDerivedShiftIso j L n k).hom) := by
  rw [openRestrictionCounitNat_shift, openRestrictionCounitNat_single]
  simp only [Functor.map_comp]
  rw [← Functor.commShiftIso_hom_naturality_assoc]
  simp only [openSingleDerivedHomRestriction, ShiftedHom.map,
    openSinglePushforwardDerivedShiftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  rfl

/-- The literal original native restriction/counit map is bijective at every single
degree and every integer shift, for an affine open and arbitrary quasicoherent coefficient. -/
theorem affineOpenSingleDerivedHomRestriction_bijective [IsAffineHom j]
    (L : U.Modules) [L.IsQuasicoherent] (K : CochainComplex.Plus Y.Modules) (n k : ℤ) :
    Function.Bijective (openSingleDerivedHomRestriction j L K n k) := by
  let F := Scheme.Modules.restrictFunctor j
  let G := Scheme.Modules.pushforward j
  let S := ((CochainComplex.singleFunctorPlus U.Modules n).obj L)⟦k⟧
  let E₁ := Iso.homCongr (Iso.refl (DerivedCategory.Plus.Q.obj K))
    (openSinglePushforwardDerivedShiftIso j L n k)
  let E₂ := Iso.homCongr (asIso (F.rightDerivedFunctorPlusUnit.app K))
    (((DerivedCategory.Plus.Q (C := U.Modules)).commShiftIso k).app
      ((CochainComplex.singleFunctorPlus U.Modules n).obj L))
  have heq : E₂ ∘ openDerivedRestrictionCounit j K S =
      openSingleDerivedHomRestriction j L K n k ∘ E₁ := by
    funext a
    change inv (F.rightDerivedFunctorPlusUnit.app K) ≫
        openDerivedRestrictionCounit j K S a ≫ _ =
      openSingleDerivedHomRestriction j L K n k
        (𝟙 _ ≫ a ≫ (openSinglePushforwardDerivedShiftIso j L n k).hom)
    rw [Category.id_comp]
    unfold openDerivedRestrictionCounit
    simp only [Category.assoc]
    rw [IsIso.inv_hom_id_assoc]
    simpa only [openRestrictionCounitNat_app, Category.assoc, Iso.app_hom] using
      openSingleDerivedHomRestriction_transport j L K n k a
  have hfun : openSingleDerivedHomRestriction j L K n k =
      E₂ ∘ openDerivedRestrictionCounit j K S ∘ E₁.symm := by
    funext a
    simpa only [Function.comp_apply, E₁.apply_symm_apply] using
      (congrFun heq (E₁.symm a)).symm
  rw [hfun]
  exact E₂.bijective.comp
    ((affineOpenDerivedRestrictionCounit_single_bijective j L K n k).comp E₁.symm.bijective)

end AlgebraicGeometry.Scheme.Cohomology
