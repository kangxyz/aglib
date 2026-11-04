/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.DerivedAdjointChart
public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Normalized
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.MultiplicativeComparison

/-!
# Original derived adjuncts at the normalized Picard terminal chart

The actual Gm higher-image chart unit identifies the original cohomology class with
its normalized pulled-back Picard class. Equality of those original terminal values
then fixes the whole H¹ map of the original source-shifted derived adjunct.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

universe v uC vC

private theorem source_map_from_section_values
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    (Γ : C ⥤ AddCommGrpCat.{vC}) {U : C}
    (E : preadditiveCoyoneda.obj (op U) ≅ Γ)
    {A B F J N : C} (k : A ⟶ B) (r : B ⟶ F) (s : A ⟶ U)
    (a : U ⟶ J) (i : J ⟶ N) (n : F ⟶ N) (z : Γ.obj F) (t : Γ.obj N)
    (hk : k ≫ r = s ≫ E.inv.app F z)
    (hv : Γ.map n z = t) (ha : Γ.map i (E.hom.app J a) = t) :
    k ≫ r ≫ n = s ≫ a ≫ i := by
  have hn : E.inv.app F z ≫ n = E.inv.app N (Γ.map n z) :=
    (ConcreteCategory.congr_hom (E.inv.naturality n) z).symm
  have hi : a ≫ i = E.inv.app N (Γ.map i (E.hom.app J a)) := by
    have h' := (ConcreteCategory.congr_hom (E.inv.naturality i) (E.hom.app J a)).symm
    change (E.inv.app J (E.hom.app J a)) ≫ i = _ at h'
    have hid : E.inv.app J (E.hom.app J a) = a :=
      ConcreteCategory.congr_hom (E.hom_inv_id_app J) a
    exact (congrArg (fun b => b ≫ i) hid).symm.trans h'
  have hs := hn.trans ((congrArg (E.inv.app N) (hv.trans ha.symm)).trans hi.symm)
  calc
    k ≫ r ≫ n = (k ≫ r) ≫ n := (Category.assoc _ _ _).symm
    _ = (s ≫ E.inv.app F z) ≫ n := congrArg (fun f => f ≫ n) hk
    _ = s ≫ a ≫ i := (Category.assoc _ _ _).trans (congrArg (fun f => s ≫ f) hs)

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

open Kummer Scheme.RelativePicard Scheme.Modules.Invertible

universe u w s e dX dS

attribute [local instance] hasSheafifyLarge

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem etaleFamilyNormalization_apply {X S : Scheme.{u}}
    (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) (U : S.Etale)
    (L : PicardGroup (pullback p U.hom)) :
    (etaleFamilyNormalization p o ho).app (op U) L =
      normalizedFamilyClass p o ho ((Scheme.Etale.forget S).obj U) L := rfl

variable {X S : Scheme.{u}} (p : X ⟶ S) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [hChart : ∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- Evaluate the original unit and resize together while its chart remains variable. -/
private theorem gmHigherDirectImageNormalizedPicardIso_chartClass
    (U : S.Etale)
    (z : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (gm X)) 1)
    (L : PicardGroup (pullback p U.hom)) (hL : fibreProductGmPicardEquiv p U z = L) :
    (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom.hom.app (op U)
        ((fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (gm X) 1).app (op U)
          ((fibreProductResizeEquiv.{u, w, s, e} p (gm X) 1 U).symm z)) =
      normalizedFamilyClass p o ho ((Scheme.Etale.forget S).obj U) L := by
  let E := fibreProductResizeEquiv.{u, w, s, e} p (gm X) 1 U
  let a := E.symm z
  let v := fibreProductGmPicardEquiv.{u, e} p U
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (gmHigherDirectImageNormalizedPicardIso_unit.{u, w, s, e} p o ho)
      (op U)) a
  change (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom.hom.app (op U)
      ((fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (gm X) 1).app (op U) a) =
    (etaleFamilyNormalization p o ho).app (op U)
      ((fibreProductGmPicardNatTrans.{u, w, s, e} p).app (op U) a) at hu
  have hv : (fibreProductGmPicardNatTrans.{u, w, s, e} p).app (op U) a = v z :=
    congrArg v (E.apply_symm_apply z)
  have hclass := hv.trans hL
  have hn := congrArg ((etaleFamilyNormalization p o ho).app (op U)) hclass
  have hfinal := hu.trans (hn.trans (etaleFamilyNormalization_apply p o ho U L))
  dsimp only [a, E] at hfinal
  exact hfinal

/-- On the original terminal chart, the higher-image section of an original Gm
class is the normalization of the original pulled-back line-bundle class. -/
theorem gmHigherDirectImageNormalizedPicardIso_terminalValue
    (c : Sheaf.H.{w} (gm X) 1) :
    let U := etaleTerminal S
    let T := (Scheme.Etale.forget S).obj U
    (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom.hom.app (op U)
        (cohomologyToHigherSections p (gm X) 1 c) =
      normalizedFamilyClass p o ho T
        (pullbackClass (pullback.fst p (𝟙 S)) ((picardCohomologyEquiv X).symm c)) := by
  intro U T
  let P := (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom.hom.app (op U)
  let g := pullback.snd (𝟙 S) p
  let : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (𝟙 S) p)) := hChart U
  let : Etale g := inferInstanceAs (Etale (pullback.snd (𝟙 S) p))
  let z := cohomologyPullback.{u, w, e} g (gm X) 1 c
  let v := fibreProductGmPicardEquiv.{u, e} p U
  let L := (picardCohomologyEquiv X).symm c
  have hc := cohomologyToHigherSections_terminalPullback.{u, w, s, e} p (gm X) 1 c
  have hg : Sheaf.H.map (gmEtalePullbackIso g).hom 1 z = gmCohomologyPullback g 1 c :=
    congrArg (fun a => Sheaf.H.map a 1 z) (gmUnit_adjoint_etale g).symm
  have hp : v z = pullbackClass (pullback.fst p (𝟙 S)) L := by
    have he := fibreProductGmPicardEquiv_apply p U z
    let s := (pullbackSymmetry p (𝟙 S)).hom
    calc
      _ = pullbackClass s ((picardCohomologyEquiv (pullback (𝟙 S) p)).symm
          (Sheaf.H.map (gmEtalePullbackIso g).hom 1 z)) := he
      _ = pullbackClass s (pullbackClass g L) :=
        (congrArg (fun b => pullbackClass s
          ((picardCohomologyEquiv (pullback (𝟙 S) p)).symm b)) hg).trans
            (congrArg (pullbackClass s) (picardCohomologyEquiv_symm_pullback g c))
      _ = pullbackClass (s ≫ g) L := (pullbackClass_comp s g L).symm
      _ = _ := congrArg (fun b => pullbackClass b L) (pullbackSymmetry_hom_comp_snd p (𝟙 S))
  have hchart := gmHigherDirectImageNormalizedPicardIso_chartClass p o ho U z
    (pullbackClass (pullback.fst p (𝟙 S)) L) hp
  have hcoho := congrArg P hc
  dsimp +instances only [P, U] at hcoho
  dsimp +instances only [U, z, g] at hchart
  refine hcoho.trans ?_
  dsimp +instances only [T, L, U] at hchart ⊢
  -- Preserve the already typed original chart equality. The native kernel checks
  -- its full declared type without repeating the elaborator conversion.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some decl := (← Lean.getLCtx).findFromUserName? `hchart
      | throwError "Missing original normalized Picard chart equality"
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar decl.fvarId)


variable [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]

/-- The actual H¹ of the original adjunct has the specified original normalized
Picard source whenever the two original terminal values agree. -/
theorem gmDerivedAdjunct_h1_of_terminalValue
    (c : Sheaf.H.{w} (gm X) 1)
    {J : AbelianSheaf.{u, u + 1} S}
    (i : J ⟶ Kummer.normalizedPicardEtaleSheaf p o ho)
    (a : (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ J)
    (h :
      (globalSections S).map i ((constantIntegerHomGlobalSectionsIso S).hom.app J a) =
        normalizedFamilyClass p o ho ((Scheme.Etale.forget S).obj (etaleTerminal S))
          (pullbackClass (pullback.fst p (𝟙 S)) ((picardCohomologyEquiv X).symm c))) :
    let U := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map
        (cohomologyOriginalDerivedAdjunct p (gm X) c) ≫ (higherDirectImageIso p 1).inv.app (gm X) ≫
          (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (AbelianSheaf.{u, u + 1} S) 1).hom.app U ≫
        a ≫ i := by
  intro U
  let H := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1
  let e₁ := DerivedCategory.singleFunctorCompHomologyFunctorIso (AbelianSheaf.{u, u + 1} S) 1
  let N := gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho
  let E := constantIntegerHomGlobalSectionsIso S
  let F := (higherDirectImage p 1).obj (gm X)
  let z := cohomologyToHigherSections p (gm X) 1 c
  exact source_map_from_section_values (globalSections S) E
    (H.map (cohomologyOriginalDerivedAdjunct p (gm X) c))
    ((higherDirectImageIso p 1).inv.app (gm X)) (e₁.hom.app U) a i N.hom z
    (normalizedFamilyClass p o ho ((Scheme.Etale.forget S).obj (etaleTerminal S))
      (pullbackClass (pullback.fst p (𝟙 S)) ((picardCohomologyEquiv X).symm c)))
    (cohomologyOriginalDerivedAdjunct_h1_map p (gm X) c)
    (gmHigherDirectImageNormalizedPicardIso_terminalValue p o ho c) h

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
