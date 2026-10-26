/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks

/-! # Original all-degree cohomology of a compatible coefficient system -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)

local instance diagramLeftAdditive :
    ∀ {i j : I} (a : i ⟶ j), ((diagramAdjunctionData X).left a).Additive := by
  intro i j a
  change (inverseImage (X.map a).unop).Additive
  infer_instance

local instance diagramLeftPreservesFiniteLimits :
    ∀ {i j : I} (a : i ⟶ j), PreservesFiniteLimits ((diagramAdjunctionData X).left a) := by
  intro i j a
  change PreservesFiniteLimits (inverseImage (X.map a).unop)
  infer_instance

local instance diagramLeftPreservesFiniteColimits :
    ∀ {i j : I} (a : i ⟶ j), PreservesFiniteColimits ((diagramAdjunctionData X).left a) := by
  intro i j a
  change PreservesFiniteColimits (inverseImage (X.map a).unop)
  infer_instance

local instance diagramIntegerCartesian :
    ∀ {i j : I} (a : i ⟶ j),
      IsIso ((diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a) := by
  intro i j a
  exact diagramIntegerSystem_leftMap_isIso X a

variable [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  (F : DiagramCoefficientSystem X) (n : ℕ)

/-- The native stage cohomology group in the independent Ext universe. -/
abbrev diagramCohomologyObj (i : I) : AddCommGrpCat.{e} :=
  InjectiveSystem.representedCohomologyObj (diagramAdjunctionData X)
    (diagramIntegerSystem X) F n i

/-- The original stage pullback followed by its compatible coefficient morphism. -/
abbrev diagramCohomologyMap {i j : I} (a : i ⟶ j) :
    diagramCohomologyObj X F n i ⟶ diagramCohomologyObj X F n j :=
  InjectiveSystem.representedCohomologyMap (diagramAdjunctionData X)
    (diagramIntegerSystem X) F n a

/-- The shared producer retains the whole original pullback/coefficient transition. -/
lemma diagramCohomologyMap_eq_transfer {i j : I} (a : i ⟶ j) :
    diagramCohomologyMap X F n a =
      cohomologyTransfer (X.map a).unop (diagramInverseTransition X F a) n := by
  ext x
  have hu : inv ((diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a) =
      (inverseImageConstantIso (X.map a).unop).inv.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [diagramIntegerSystem_leftMap]
    exact Iso.hom_inv_id_app _ _
  change ((((diagramAdjunctionData X).left a).extPrecompMap
      (inv ((diagramIntegerSystem X).leftMap (diagramAdjunctionData X) a))
      (F.obj i) n x).comp
        (Abelian.Ext.mk₀ (F.leftMap (diagramAdjunctionData X) a)) (add_zero n)) =
    Sheaf.H.map (diagramInverseTransition X F a) n
      (cohomologyPullback (X.map a).unop (F.obj i) n x)
  rw [hu]
  rfl

lemma diagramCohomologyMap_id (i : I) : diagramCohomologyMap X F n (𝟙 i) = 𝟙 _ :=
  InjectiveSystem.representedCohomologyMap_id (diagramAdjunctionData X)
    (diagramIntegerSystem X) F n i

lemma diagramCohomologyMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    diagramCohomologyMap X F n (a ≫ b) =
      diagramCohomologyMap X F n a ≫ diagramCohomologyMap X F n b :=
  InjectiveSystem.representedCohomologyMap_comp (diagramAdjunctionData X)
    (diagramIntegerSystem X) F n a b

/-- The actual all-degree source diagram, without assuming continuity. -/
abbrev diagramCohomologyFunctor : I ⥤ AddCommGrpCat.{e} :=
  InjectiveSystem.representedCohomologyFunctor (diagramAdjunctionData X)
    (diagramIntegerSystem X) F n

variable {F} {G : DiagramCoefficientSystem X}
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F G)

/-- A morphism of actual systems induces the original cohomological coefficient maps. -/
abbrev diagramCohomologyNatTrans : diagramCohomologyFunctor X F n ⟶
    diagramCohomologyFunctor X G n :=
  InjectiveSystem.representedCohomologyNatTrans (diagramAdjunctionData X)
    (diagramIntegerSystem X) η n

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
