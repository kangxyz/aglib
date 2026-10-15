/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.GeneralPushforward
/-!
# Actual closed-immersion coherent pushforward functoriality

The original sheaf direct-image identity and composition comparisons restrict
to coherent sheaves on locally noetherian schemes with their actual
closed-immersion direct image functors.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
variable {X Y Z : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- The generic identity comparison specialized to coherent closed direct image. -/
abbrev coherentPushforwardIdIso (X : Scheme.{u}) [IsLocallyNoetherian X] :
    coherentPushforward (𝟙 X) ≅ 𝟭 (Scheme.CoherentSheaf X) :=
  finiteTypePushforwardIdIso X

/-- The generic composition comparison specialized to coherent closed direct image. -/
abbrev coherentPushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] :
    coherentPushforward f ⋙ coherentPushforward g ≅ coherentPushforward (f ≫ g) :=
  finiteTypePushforwardCompIso f g

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
