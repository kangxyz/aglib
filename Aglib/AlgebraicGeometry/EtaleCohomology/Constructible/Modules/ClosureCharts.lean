/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.EtaleRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceTopology
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRestriction

/-! # Actual etale chart restrictions for constant-ring module sheaves

The native module inverse image along an etale chart is its ordinary sheaf
restriction. The genuine slice equivalence and native constant comparison
transport the local finite-presentation morphism equations without changing
coefficient maps or assuming fullness on disconnected charts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- The original ModuleCat-valued sheaf equivalence for the genuine small
etale slice, at the unchanged module-value universe. -/
def moduleEtaleSliceEquivalence {X : Scheme.{u}} (U : X.Etale) :
    ModuleSheaf R U.left ≌ Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R) := by
  let : (etaleSliceEquivalence U).inverse.IsDenseSubsite U.left.smallEtaleTopology
      (X.smallEtaleTopology.over U) := etaleSliceBackward_isDenseSubsite U
  exact ((etaleSliceEquivalence U).sheafCongr (X.smallEtaleTopology.over U)
    U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).symm

/-- Actual slice restriction is original chart restriction under the native equivalence. -/
def moduleEtaleSliceRestrictionIso {X : Scheme.{u}} (U : X.Etale) :
    X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) U ⋙
      (moduleEtaleSliceEquivalence R U).inverse ≅ moduleEtaleRestriction R U.hom :=
  Iso.refl _

/-- Constant coefficients transport through the native slice equivalence. -/
def moduleEtaleSliceConstantIso {X : Scheme.{u}} (U : X.Etale) :
    constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R) ≅
      constantSheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R) ⋙
        (moduleEtaleSliceEquivalence R U).inverse :=
  Functor.isoWhiskerLeft
    (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R))
    (moduleEtaleSliceEquivalence R U).unitIso ≪≫
    Functor.isoWhiskerRight
      (((constantSheafAdj U.left.smallEtaleTopology (ModuleCat.{u + 1} R)
        (etaleTerminalIsTerminal U.left)).comp
          (moduleEtaleSliceEquivalence R U).toAdjunction).leftAdjointUniq
        (constantSheafAdj (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)
          ((etaleTerminalIsTerminal U.left).isTerminalObj (etaleSliceBackward U))))
      (moduleEtaleSliceEquivalence R U).inverse

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
