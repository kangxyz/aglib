/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact

/-!
# Exact coherent restriction and supported coherent categories

Open restriction uses the same finite-type quasicoherent functor. The
abelian, exact and supported Serre structures retain local Noetherianity.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

instance finiteTypeSheavesRestriction_preservesFiniteLimits : PreservesFiniteLimits
  (finiteTypeSheavesRestriction j)
  := by
  have : PreservesFiniteLimits (finiteTypeSheavesRestriction j ⋙ finiteTypeSheavesToModules U) := by
    rw [finiteTypeSheavesRestriction_comp_inclusion]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (finiteTypeSheavesRestriction j)
    (finiteTypeSheavesToModules U)

instance finiteTypeSheavesRestriction_preservesFiniteColimits : PreservesFiniteColimits
  (finiteTypeSheavesRestriction
  j) := by
  have : PreservesFiniteColimits (finiteTypeSheavesRestriction j ⋙ finiteTypeSheavesToModules U) :=
    by
    rw [finiteTypeSheavesRestriction_comp_inclusion]
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (finiteTypeSheavesRestriction j)
    (finiteTypeSheavesToModules
    U)

instance finiteTypeSheavesRestriction_additive : (finiteTypeSheavesRestriction j).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (finiteTypeSheavesRestriction j)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Actual open restriction is an exact functor on coherent sheaves. -/
def coherentRestrictionExact : ExactFunctor (coherentExactStructure X) (coherentExactStructure U)
  where
  toFunctor := finiteTypeSheavesRestriction j
  map_conflation _ h := h.map_of_exact _

instance finiteTypeSheavesSupportedAway_isSerreClass : (finiteTypeSheavesSupportedAway
  j).IsSerreClass := by
  change ((Scheme.Modules.supportedAway j).inverseImage
    (finiteTypeSheavesToModules X)).IsSerreClass
  infer_instance

instance instAbelianSupportedCoherent : Abelian (SupportedFiniteTypeSheaves j) := inferInstance
instance supportedCoherent_essentiallySmall : EssentiallySmall.{u+1} (SupportedFiniteTypeSheaves j)
  :=
  inferInstance

/-- The standard exact structure on the actual support category. -/
def supportedCoherentExactStructure : ExactStructure (SupportedFiniteTypeSheaves j) :=
  abelianExactStructure
  _

end AlgebraicGeometry.Scheme.Modules.Coherent
