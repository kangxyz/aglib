/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.AffineFunctoriality
/-!
# Functoriality of actual finite coherent direct image

Identity and composition of the original module-sheaf pushforward restrict
to coherent sheaves. The finite construction agrees with the finite affine
and closed-immersion functors, retaining their original sheaf action.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite
variable {X Y Z : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- Identity comparison on coherent sheaves over a locally Noetherian scheme. -/
abbrev coherentPushforwardIdIso (X : Scheme.{u}) [IsLocallyNoetherian X] :
    coherentPushforward (𝟙 X) ≅ 𝟭 (Scheme.CoherentSheaf X) :=
  finiteTypePushforwardIdIso X

/-- The generic composition comparison specialized to coherent direct images. -/
abbrev coherentPushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsFinite g] :
    coherentPushforward f ⋙ coherentPushforward g ≅ coherentPushforward (f ≫ g) :=
  finiteTypePushforwardCompIso f g

/-- On an original coordinate map the coherent functor is the established
finite affine direct image, with no replacement of its sheaf action. -/
theorem coherentPushforward_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsNoetherianRing R] [IsNoetherianRing S]
    [AlgebraicGeometry.IsFinite (Spec.map φ)] :
    coherentPushforward (Spec.map φ) = Pushforward.Finite.Affine.coherentPushforward φ
      ((AlgebraicGeometry.IsFinite.SpecMap_iff φ).mp inferInstance) := rfl

/-- Finite direct image specializes to the unchanged closed-immersion functor. -/
theorem coherentPushforward_closed (f : X ⟶ Y) [IsClosedImmersion f] :
    coherentPushforward f = Pushforward.ClosedImmersion.coherentPushforward f := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite
