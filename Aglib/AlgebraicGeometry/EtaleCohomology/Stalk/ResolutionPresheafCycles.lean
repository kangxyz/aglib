/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ResolutionPresheafHomology
public import Aglib.Algebra.Homology.ShortComplex.Adjunction.ExactLeftCycles

/-! # Original higher-image comparison on actual resolution cycles

The original map from resolution cohomology to the higher direct image sends
the actual cycle projection to the original sheafification unit on cycles,
followed by native exact cycle comparison and the actual termwise counit.
This is a formula for the original map in every degree, not a new map or an
isomorphism between section cohomology and higher-image sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The original higher-image comparison retains the actual cycle-class formula
on every supplied resolution, without any positive-degree exactness of sections. -/
theorem resolutionCohomologyToHigherDirectImage_cycles
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ) :
    let P := directImagePresheaf f
    let L := presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
    let U := sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
    let K := (P.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let T := ((directImage f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let δ := (NatTrans.mapHomologicalComplex
      (directImagePresheafSheafificationIso f).hom (.up ℤ)).app I.cochainComplex
    K.homologyπ (q : ℤ) ≫ (I.isoRightDerivedObjCochain P q).inv ≫
        (resolutionCohomologyToHigherDirectImage f q).app F ≫
        U.map (I.isoRightDerivedObjCochain (directImage f) q).hom =
      toSheafify (Scheme.smallEtaleTopology S) (K.cycles (q : ℤ)) ≫
        U.map (((K.sc (q : ℤ)).mapCyclesIso L).inv ≫
          cyclesMap δ (q : ℤ) ≫ T.homologyπ (q : ℤ)) := by
  dsimp only
  have hh := resolutionCohomologyToHigherDirectImage_resolution f I q
  change (resolutionCohomologyToHigherDirectImage f q).app F ≫
    (sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).map
      (I.isoRightDerivedObjCochain (directImage f) q).hom = _ at hh
  rw [hh]
  rw [← Category.assoc (I.isoRightDerivedObjCochain (directImagePresheaf f) q).inv,
    Iso.inv_hom_id, Category.id_comp]
  let P := directImagePresheaf f
  let K := (P.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let δ := (NatTrans.mapHomologicalComplex
    (directImagePresheafSheafificationIso f).hom (.up ℤ)).app I.cochainComplex
  have hc := (sheafificationAdjunction (Scheme.smallEtaleTopology S)
    AddCommGrpCat.{u + 1}).homology_unit_exact_left_cycles (K.sc (q : ℤ))
      ((shortComplexFunctor (AbelianSheaf.{u, u + 1} S) (.up ℤ) (q : ℤ)).map δ)
  change K.homologyπ (q : ℤ) ≫
      toSheafify (Scheme.smallEtaleTopology S) (K.homology (q : ℤ)) ≫
        (sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).map
          (((K.sc (q : ℤ)).mapHomologyIso
            (presheafToSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})).inv ≫
              homologyMap δ (q : ℤ)) = _ at hc
  rw [Functor.map_comp] at hc
  exact hc

end AlgebraicGeometry.Scheme.EtaleCohomology
