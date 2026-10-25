/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalHigherCycles
public import Aglib.AlgebraicGeometry.EtaleCohomology.SlicePullback.AugmentationSections
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.ExactResolution.Ext

/-! # Original global cohomology sections on actual resolution cycles

The original global Ext class, represented in any actual injective resolution,
gives the original higher-image section by projecting an actual cycle section.
Its term is the original global cocycle transported through the native terminal
comparison. This does not assert injectivity of the higher-section map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex Opposite
open CochainComplex.HomComplex

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The actual global higher-image section of an original cocycle is represented
by a genuine cycle section with exactly the original terminal-transported term. -/
theorem cohomologyToHigherSections_exists_resolution_cycle
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ)
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ I.cochainComplex.X (q : ℤ))
    (ha : a ≫ I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0) :
    let T := ((directImage f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let x := I.extEquivCohomologyClass.symm
      (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl ha))
    ∃ z : (globalSections S).obj (T.cycles (q : ℤ)),
      (globalSections S).map (T.iCycles (q : ℤ)) z =
          (directImageGlobalSectionsIso f).inv.app _
            ((constantIntegerHomGlobalSectionsIso X).hom.app _ a) ∧
        (globalSections S).map (I.isoRightDerivedObjCochain (directImage f) q).hom
          (cohomologyToHigherSections f F q x) =
            (globalSections S).map (T.homologyπ (q : ℤ)) z := by
  let V := (siteBaseChange f).obj (etaleTerminal S)
  let b := representedIntegerAugmentation V ≫ a
  have hb : b ≫ I.cochainComplex.d (q : ℤ) ((q : ℤ) + 1) = 0 := by
    rw [Category.assoc, ha, comp_zero]
  obtain ⟨z, hz, hp⟩ := originalHigherSection_exists_resolution_cycle
    f (etaleTerminal S) I q b hb
  refine ⟨z, hz.trans (directImagePresheafRepresentedIso_augmentation f _ a), ?_⟩
  have hc : globalCohomologyTerminalClass f F q
      (I.extEquivCohomologyClass.symm
        (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl ha))) =
    I.extEquivCohomologyClass.symm
      (.mk (Cocycle.fromSingleMk b (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl hb)) := by
    change (Ext.mk₀ (representedIntegerAugmentation V)).comp
      (I.extEquivCohomologyClass.symm
        (.mk (Cocycle.fromSingleMk a (zero_add (q : ℤ)) ((q : ℤ) + 1) rfl ha)))
          (Nat.zero_add q) = _
    rw [InjectiveResolution.extEquivCohomologyClass_symm_mk_precomp,
      ← Cocycle.fromSingleMk_precomp]
  change (I.isoRightDerivedObjCochain (directImage f) q).hom.hom.app (op (etaleTerminal S))
    (((resolutionCohomologyToHigherDirectImage f q).app F).app (op (etaleTerminal S))
      (originalCohomologyResolutionEquiv f (etaleTerminal S) F q
        (globalCohomologyTerminalClass f F q _))) = _
  rw [originalCohomologyResolutionEquiv_eq_ofResolution f (etaleTerminal S) I, hc]
  exact hp

end AlgebraicGeometry.Scheme.EtaleCohomology
