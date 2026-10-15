/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.Support
/-!
# Exact restriction and actual support for global coherent sheaves

The affine-chart definition is stable under open restriction by composition
of actual affine charts. The full coherent inclusion reflects finite limits
and colimits, so restriction is exact. Its kernel is exactly vanishing on
the open, equivalently ordinary stalk support in the closed complement.
No global quotient-equivalence or global localization theorem is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Composition of affine charts proves actual open restriction preserves
the affine-local finite quasicoherent condition. -/
theorem affineLocallyFiniteType_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} (hM : affineLocallyFiniteType X M) :
    affineLocallyFiniteType U ((Scheme.Modules.restrictFunctor j).obj M) := by
  intro R f _
  exact (affineFiniteSheaf R).prop_of_iso ((Scheme.Modules.restrictFunctorComp f j).app M)
    (hM R (f ≫ j))

variable {U X : Scheme.{u}}
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Open restriction of affine-locally finite-type sheaves. -/
def finiteTypeSheavesRestriction : FiniteTypeSheaves X ⥤ FiniteTypeSheaves U :=
  (affineLocallyFiniteType U).lift ((affineLocallyFiniteType X).ι ⋙ Scheme.Modules.restrictFunctor
    j)
    (fun M => affineLocallyFiniteType_restrict j M.property)

/-- The underlying sheaf functor is literally the actual open restriction. -/
theorem finiteTypeSheavesRestriction_comp_inclusion :
    finiteTypeSheavesRestriction j ⋙ finiteTypeSheavesToModules U =
      finiteTypeSheavesToModules X ⋙ Scheme.Modules.restrictFunctor j := rfl

/-- Actual coherent sheaves vanishing on the selected open. -/
def finiteTypeSheavesSupportedAway : ObjectProperty (FiniteTypeSheaves X) :=
  (Scheme.Modules.supportedAway j).inverseImage (finiteTypeSheavesToModules X)

/-- This support property is exactly the kernel of actual finite-type sheaf restriction. -/
theorem finiteTypeSheavesRestriction_kernel_eq_support :
    (finiteTypeSheavesRestriction j).kernel = finiteTypeSheavesSupportedAway j := by
  funext M
  apply propext
  change IsZero ((finiteTypeSheavesRestriction j).obj M) ↔
    IsZero ((finiteTypeSheavesToModules U).obj ((finiteTypeSheavesRestriction j).obj M))
  exact ⟨Functor.map_isZero _, fun h => IsZero.of_full_of_faithful_of_isZero _ _ h⟩

/-- Support membership has its ordinary stalk-support meaning. -/
theorem finiteTypeSheavesSupportedAway_iff_support_subset (M : FiniteTypeSheaves X) :
    finiteTypeSheavesSupportedAway j M ↔ Scheme.Modules.support M.obj ⊆ (Set.range j)ᶜ := by
  change Scheme.Modules.supportedAway j M.obj ↔ _
  rw [Scheme.Modules.supportedAway_iff_support_disjoint]
  exact Set.disjoint_left

/-- The actual full abelian category of supported coherent sheaves. -/
abbrev SupportedFiniteTypeSheaves := (finiteTypeSheavesSupportedAway j).FullSubcategory

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
