/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
/-!
# Pullback on locally Noetherian coherent categories

The underlying functor is native geometric module-sheaf pullback. Finite
presentations supply object preservation; identity, composition and open
restriction comparisons retain the actual maps.
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

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- The canonical finite-type pullback specialized to genuine coherent
categories over locally Noetherian schemes. -/
abbrev coherentPullback (f : X ⟶ Y) : Y.CoherentSheaf ⥤ X.CoherentSheaf :=
  finiteTypePullback f

/-- The coherent interface reuses the canonical finite-type functor definitionally. -/
@[simp] theorem coherentPullback_eq_finiteTypePullback (f : X ⟶ Y) :
    coherentPullback f = finiteTypePullback f := rfl

/-- The inclusion recovers the original geometric module-sheaf pullback. -/
@[simp] theorem coherentPullback_comp_inclusion (f : X ⟶ Y) :
    coherentPullback f ⋙ finiteTypeSheavesToModules X =
      finiteTypeSheavesToModules Y ⋙ Scheme.Modules.pullback f := rfl

theorem coherentPullback_additive (f : X ⟶ Y) : (coherentPullback f).Additive := by
  infer_instance

/-- The native identity comparison specialized to coherent objects. -/
abbrev coherentPullbackIdIso (X : Scheme.{u}) [IsLocallyNoetherian X] :
    coherentPullback (𝟙 X) ≅ 𝟭 X.CoherentSheaf :=
  finiteTypePullbackIdIso X

/-- The native composition comparison specialized to coherent objects. -/
abbrev coherentPullbackCompIso {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    coherentPullback (f ≫ g) ≅ coherentPullback g ⋙ coherentPullback f :=
  finiteTypePullbackCompIso f g

/-- Actual coherent restriction agrees with the canonical coherent pullback. -/
abbrev coherentRestrictionIsoPullback (j : X ⟶ Y) [IsOpenImmersion j] :
    finiteTypeSheavesRestriction j ≅ coherentPullback j :=
  finiteTypeRestrictionIsoPullback j

end AlgebraicGeometry.Scheme.Modules.Coherent
