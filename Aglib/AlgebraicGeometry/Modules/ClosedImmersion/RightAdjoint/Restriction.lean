/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.RightAdjoint
public import Aglib.AlgebraicGeometry.Modules.Restriction.ExtensionByZero.ClosedImmersion
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Open restriction of the single closed right adjoint

The original extension-by-zero exchange is an isomorphism of the two
composite left adjoints. Native conjugation therefore identifies their
original right adjoints. The unit, counit and Hom-adjoint equations retain
that same exchange and the actual selected ordinary closed adjunctions.
The coefficient sheaves are arbitrary; no quasicoherence or finite
presentation is needed for this open comparison.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j]
  [IsClosedImmersion f] [IsClosedImmersion b] (h : IsPullback a b f j)

/-- The ordinary closed right adjoint commutes with open restriction through
its original extension-by-zero exchange. -/
def closedImmersionRightAdjointOpenIso :
    closedImmersionRightAdjoint f ⋙ restrictFunctor a ≅
      restrictFunctor j ⋙ closedImmersionRightAdjoint b :=
  conjugateIsoEquiv
    ((extensionByZeroRestrictAdjunction a).comp (closedImmersionRightAdjunction f))
    ((closedImmersionRightAdjunction b).comp (extensionByZeroRestrictAdjunction j))
    (closedPushforwardExtensionByZeroIso a b f j h)

/-- The original composite units identify the same open comparison. -/
@[reassoc]
theorem closedImmersionRightAdjointOpenIso_unit (M : W.Modules) :
    ((extensionByZeroRestrictAdjunction a).comp (closedImmersionRightAdjunction f)).unit.app M ≫
        (closedImmersionRightAdjointOpenIso a b f j h).hom.app
          ((pushforward f).obj ((extensionByZero a).obj M)) =
      ((closedImmersionRightAdjunction b).comp (extensionByZeroRestrictAdjunction j)).unit.app M ≫
        (restrictFunctor j ⋙ closedImmersionRightAdjoint b).map
          ((closedPushforwardExtensionByZeroIso a b f j h).hom.app M) :=
  unit_conjugateEquiv _ _ _ M

/-- The original composite counits identify the same open comparison. -/
@[reassoc]
theorem closedImmersionRightAdjointOpenIso_counit (N : X.Modules) :
    (pushforward b ⋙ extensionByZero j).map
        ((closedImmersionRightAdjointOpenIso a b f j h).hom.app N) ≫
      ((closedImmersionRightAdjunction b).comp (extensionByZeroRestrictAdjunction j)).counit.app N =
    (closedPushforwardExtensionByZeroIso a b f j h).hom.app
        ((restrictFunctor a).obj ((closedImmersionRightAdjoint f).obj N)) ≫
      ((extensionByZeroRestrictAdjunction a).comp
        (closedImmersionRightAdjunction f)).counit.app N :=
  conjugateEquiv_counit _ _ _ N

/-- Native Hom transposition preserves the original open exchange and the
same closed-adjoint comparison on every coefficient. -/
theorem closedImmersionRightAdjointOpenIso_homEquiv (M : W.Modules) (N : X.Modules)
    (p : (pushforward f).obj ((extensionByZero a).obj M) ⟶ N) :
    ((extensionByZeroRestrictAdjunction a).comp (closedImmersionRightAdjunction f)).homEquiv M N p ≫
        (closedImmersionRightAdjointOpenIso a b f j h).hom.app N =
      ((closedImmersionRightAdjunction b).comp (extensionByZeroRestrictAdjunction j)).homEquiv M N
        ((closedPushforwardExtensionByZeroIso a b f j h).hom.app M ≫ p) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Category.assoc]
  rw [(closedImmersionRightAdjointOpenIso a b f j h).hom.naturality p,
    ← Category.assoc, closedImmersionRightAdjointOpenIso_unit]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules
