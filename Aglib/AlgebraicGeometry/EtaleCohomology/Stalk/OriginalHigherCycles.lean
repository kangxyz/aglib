/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalCohomologyCycles
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ResolutionPresheafCycles
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductGermZero
public import Aglib.CategoryTheory.Adjunction.CycleSections

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
  have hs' : E.map (K.sc (q : ℤ)).g s = 0 := by
    change A.d (q : ℤ) ((ComplexShape.up ℤ).next (q : ℤ)) s = 0
    rw [CochainComplex.next ℤ (q : ℤ)]
    exact hs
  have hx : E.map (I.isoRightDerivedObjCochain P q).hom x =
      ((K.sc (q : ℤ)).mapHomologyIso E).hom
        (((K.sc (q : ℤ)).map E).homologyπ
          (((K.sc (q : ℤ)).map E).abCyclesIso.inv ⟨s, hs'⟩)) := by
    have h := originalCohomologyResolutionEquivOfResolution_cocycle f V I q a ha
    change E.map (I.isoRightDerivedObjCochain P q).hom x =
      ((K.sc (q : ℤ)).mapHomologyIso E).hom
        (addCommGrpCycleClass A (q : ℤ) s hs) at h
    dsimp only [addCommGrpCycleClass, HomologicalComplex.homologyπ,
      HomologicalComplex.sc, shortComplexFunctor, shortComplexFunctor',
      ShortComplex.map, Functor.mapHomologicalComplex, A] at h ⊢
    exact h
  change ∃ z : E.obj (U.obj (T.cycles (q : ℤ))),
    E.map (U.map (T.iCycles (q : ℤ))) z = s ∧
      E.map ((resolutionCohomologyToHigherDirectImage f q).app F ≫
        U.map (I.isoRightDerivedObjCochain (directImage f) q).hom) x =
          E.map (U.map (T.homologyπ (q : ℤ))) z
  exact (sheafificationAdjunction (Scheme.smallEtaleTopology S)
    AddCommGrpCat.{u + 1}).exists_cycleSection E (T.sc (q : ℤ))
      ((shortComplexFunctor (AbelianSheaf.{u, u + 1} S) (.up ℤ) (q : ℤ)).map δ)
      (I.isoRightDerivedObjCochain P q)
      ((resolutionCohomologyToHigherDirectImage f q).app F ≫
        U.map (I.isoRightDerivedObjCochain (directImage f) q).hom)
      (directImagePresheafSheafificationIso_unit f (I.cochainComplex.X (q : ℤ)))
      (resolutionCohomologyToHigherDirectImage_cycles f I q) x s hs' hx

end AlgebraicGeometry.Scheme.EtaleCohomology
