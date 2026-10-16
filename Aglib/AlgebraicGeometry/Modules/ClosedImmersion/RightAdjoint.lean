/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion.Colimits
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# The ordinary right adjoint of closed-immersion pushforward

The actual closed pushforward preserves all small colimits on the native
Grothendieck category of module sheaves. The special adjoint functor theorem
therefore supplies its ordinary right adjoint. This single selected functor
is additive, preserves limits and sends injectives to injectives, because
the original closed pushforward is exact. No coherence assertion or derived
full faithfulness is inferred from this ordinary adjunction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- On all module sheaves, the original closed pushforward has an ordinary
right adjoint by the native special adjoint functor theorem. -/
instance pushforward_isLeftAdjoint_of_closedImmersion : (pushforward f).IsLeftAdjoint :=
  isLeftAdjoint_of_preservesColimits_of_isSeparating
    (isSeparator_separator X.Modules) (pushforward f)

/-- The single ordinary right adjoint of the original closed pushforward. -/
def closedImmersionRightAdjoint : Y.Modules ⥤ X.Modules := (pushforward f).rightAdjoint

/-- The native selected adjunction for the original closed pushforward. -/
def closedImmersionRightAdjunction : pushforward f ⊣ closedImmersionRightAdjoint f :=
  Adjunction.ofIsLeftAdjoint (pushforward f)

instance closedImmersionRightAdjoint_isRightAdjoint :
    (closedImmersionRightAdjoint f).IsRightAdjoint :=
  (closedImmersionRightAdjunction f).isRightAdjoint

instance closedImmersionRightAdjoint_additive : (closedImmersionRightAdjoint f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The ordinary right adjoint preserves injectives because the original
left adjoint is exact; no quasicoherence is required of an injective term. -/
instance closedImmersionRightAdjoint_preservesInjectiveObjects :
    (closedImmersionRightAdjoint f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (closedImmersionRightAdjunction f)

end AlgebraicGeometry.Scheme.Modules
