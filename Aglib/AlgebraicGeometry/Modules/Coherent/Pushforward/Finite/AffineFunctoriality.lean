/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.PushforwardFunctoriality
/-!
# Identity, composition and closed comparisons for finite affine direct image

The original module-sheaf comparisons restrict to actual coherent sheaves,
with the retained finite coordinate maps and closed-immersion comparison.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
variable {R S T : CommRingCat.{u}}
  [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]

/-- The generic affine identity comparison specialized to a Noetherian ring. -/
abbrev coherentPushforwardIdIso (R : CommRingCat.{u}) [IsNoetherianRing R] :
    coherentPushforward (𝟙 R) (RingHom.Finite.id R) ≅ 𝟭 (Scheme.CoherentSheaf (Spec R)) :=
  finiteTypePushforwardSpecIdIso R

/-- The generic affine composition comparison specialized to Noetherian rings. -/
abbrev coherentPushforwardCompIso (φ : R ⟶ S) (hφ : φ.hom.Finite)
    (ψ : S ⟶ T) (hψ : ψ.hom.Finite) :
    coherentPushforward ψ hψ ⋙ coherentPushforward φ hφ ≅
      coherentPushforward (φ ≫ ψ) (hψ.comp hφ) :=
  finiteTypePushforwardSpecCompIso φ hφ ψ hψ

/-- The generic closed comparison specialized to coherent direct image. -/
abbrev coherentPushforwardClosedIso (φ : R ⟶ S) (hφ : φ.hom.Finite)
    [IsClosedImmersion (Spec.map φ)] :
    coherentPushforward φ hφ ≅ Pushforward.ClosedImmersion.coherentPushforward (Spec.map φ) :=
  finiteTypePushforwardSpecClosedIso φ hφ

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
