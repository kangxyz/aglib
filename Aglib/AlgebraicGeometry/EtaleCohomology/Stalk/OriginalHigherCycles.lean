/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalCohomologyCycles
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ResolutionPresheafCycles
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductGermZero

/-! # Actual cycles representing original higher-image sections

The original represented Ext class gives an actual section of the cycle sheaf
of the original direct-image resolution. Its inclusion is the original section
cocycle and its homology projection is the original higher-image section.
Neither an isomorphism nor injectivity of section cohomology into higher-image
sections is asserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open CochainComplex.HomComplex

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Etale)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- An original represented cocycle determines an actual cycle section whose
projection is the original higher-image comparison on the same Ext class. -/
theorem originalHigherSection_exists_resolution_cycle
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X)
      ((siteBaseChange f).obj V) ⟶ I.cochainComplex.X (q : ℤ))
    (ha : a ≫ I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0) :
    let T := ((directImage f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let x := originalCohomologyResolutionEquivOfResolution f V I q
      (I.extEquivCohomologyClass.symm
        (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl ha)))
    ∃ z : (T.cycles (q : ℤ)).obj.obj (op V),
      (T.iCycles (q : ℤ)).hom.app (op V) z =
          (directImagePresheafRepresentedIso f V).hom.app _ a ∧
        (I.isoRightDerivedObjCochain (directImage f) q).hom.hom.app (op V)
          (((resolutionCohomologyToHigherDirectImage f q).app F).app (op V) x) =
            (T.homologyπ (q : ℤ)).hom.app (op V) z := by
  let P := directImagePresheaf f
  let L := presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
  let U := sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
  let E := (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op V)
  let K := (P.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let T := ((directImage f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let δ := (NatTrans.mapHomologicalComplex
    (directImagePresheafSheafificationIso f).hom (.up ℤ)).app I.cochainComplex
  let x := originalCohomologyResolutionEquivOfResolution f V I q
    (I.extEquivCohomologyClass.symm
      (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl ha)))
  let A := (E.mapHomologicalComplex (.up ℤ)).obj K
  let s := (directImagePresheafRepresentedIso f V).hom.app _ a
  have hs : A.d (q : ℤ) ((q : ℤ) + 1) s = 0 := by
    have he := ConcreteCategory.congr_hom
      ((directImagePresheafRepresentedIso f V).hom.naturality
        (I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1))) a
    change (directImagePresheafRepresentedIso f V).hom.app _
      (a ≫ I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1)) = A.d _ _ s at he
    rw [ha, map_zero] at he
    exact he.symm
  let z₀ := (A.sc (q : ℤ)).abCyclesIso.inv ⟨s, by
    change A.d (q : ℤ) ((ComplexShape.up ℤ).next (q : ℤ)) s = 0
    rw [CochainComplex.next ℤ (q : ℤ)]
    exact hs⟩
  let zK := ((K.sc (q : ℤ)).mapCyclesIso E).hom z₀
  let τ := toSheafify (Scheme.smallEtaleTopology S) (K.cycles (q : ℤ)) ≫
    U.map (((K.sc (q : ℤ)).mapCyclesIso L).inv ≫ cyclesMap δ (q : ℤ))
  have hi : τ ≫ U.map (T.iCycles (q : ℤ)) = K.iCycles (q : ℤ) := by
    have h := (sheafificationAdjunction (Scheme.smallEtaleTopology S)
      AddCommGrpCat.{u + 1}).cycles_unit_exact_left_iCycles (K.sc (q : ℤ))
        ((shortComplexFunctor (AbelianSheaf.{u, u + 1} S) (.up ℤ) (q : ℤ)).map δ)
    have hu : toSheafify (Scheme.smallEtaleTopology S) (K.X (q : ℤ)) ≫
        U.map (δ.f (q : ℤ)) = 𝟙 _ :=
      directImagePresheafSheafificationIso_unit f (I.cochainComplex.X (q : ℤ))
    change τ ≫ U.map (T.iCycles (q : ℤ)) =
      K.iCycles (q : ℤ) ≫ toSheafify (Scheme.smallEtaleTopology S) (K.X (q : ℤ)) ≫
        U.map (δ.f (q : ℤ)) at h
    rw [hu, Category.comp_id] at h
    exact h
  have hzK : E.map (K.iCycles (q : ℤ)) zK = s := by
    have h := ConcreteCategory.congr_hom ((K.sc (q : ℤ)).mapCyclesIso_hom_iCycles E) z₀
    exact h.trans ((A.sc (q : ℤ)).abCyclesIso_inv_apply_iCycles _)
  have hx : E.map (I.isoRightDerivedObjCochain P q).hom x =
      E.map (K.homologyπ (q : ℤ)) zK := by
    rw [originalCohomologyResolutionEquivOfResolution_cocycle]
    exact ConcreteCategory.congr_hom
      (ShortComplex.homologyπ_mapHomologyIso_hom E (K.sc (q : ℤ))) z₀
  have hx' : E.map (I.isoRightDerivedObjCochain P q).inv
      (E.map (K.homologyπ (q : ℤ)) zK) = x := by
    rw [← hx]
    exact ConcreteCategory.congr_hom (E.mapIso (I.isoRightDerivedObjCochain P q)).hom_inv_id x
  refine ⟨(τ.app (op V)) zK, ?_, ?_⟩
  · have h := ConcreteCategory.congr_hom (congrArg (fun k => k.app (op V)) hi) zK
    exact h.trans hzK
  · have h := resolutionCohomologyToHigherDirectImage_cycles f I q
    change K.homologyπ (q : ℤ) ≫ (I.isoRightDerivedObjCochain P q).inv ≫
        (resolutionCohomologyToHigherDirectImage f q).app F ≫
          U.map (I.isoRightDerivedObjCochain (directImage f) q).hom =
      τ ≫ U.map (T.homologyπ (q : ℤ)) at h
    have he := ConcreteCategory.congr_hom (congrArg (fun k => k.app (op V)) h) zK
    change (I.isoRightDerivedObjCochain (directImage f) q).hom.hom.app (op V)
        (((resolutionCohomologyToHigherDirectImage f q).app F).app (op V)
          (E.map (I.isoRightDerivedObjCochain P q).inv
            (E.map (K.homologyπ (q : ℤ)) zK))) =
      (T.homologyπ (q : ℤ)).hom.app (op V) ((τ.app (op V)) zK) at he
    rw [hx'] at he
    exact he

end AlgebraicGeometry.Scheme.EtaleCohomology
