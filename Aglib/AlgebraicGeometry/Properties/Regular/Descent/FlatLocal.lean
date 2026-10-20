/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Conditional regularity descent along flat local maps

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.FlatRegularityDescent`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `2587c8771bd9d0c963db35db6da998e99bbb6c160646a535e38c92b1d45179bd`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v

section FlatLocalRegularityDescent


/-! The separately reviewed ordinary flat-local regularity descent family,
Stacks Lemma 10.110.9 (00OF). This is an explicit unproved proposition type,
not an axiom or a specialised node/resolution conclusion. Actual scheme-stalk
locality, flatness and Noetherianness are proved from the displayed hypotheses. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.RegularityDescent

/-- Regularity descends along an actual flat local hom of Noetherian local rings.
`f.Flat` fixes the module structure induced by that same ring homomorphism. -/
def FlatLocalRegularityDescent : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B),
    IsLocalHom f → f.Flat → IsRegularLocalRing B → IsRegularLocalRing A

variable (hdesc : FlatLocalRegularityDescent.{u})
include hdesc

lemma regular_at_image {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] (x : X)
    (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) :=
  hdesc _ _ (f.stalkMap x).hom (f.toLRSHom.prop x) (Flat.stalkMap f x) hx

lemma regular_of_etale_cover {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type*} (C : ι → Scheme.{u}) (f : ∀ i, C i ⟶ X)
    [∀ i, Etale (f i)] [∀ i, IsLocallyNoetherian (C i)]
    (covers : ∀ x : X, ∃ i, x ∈ Set.range (f i))
    (regular : ∀ i, Scheme.RegularStalks (C i)) :
    Scheme.RegularStalks X := by
  intro x
  obtain ⟨i, z, rfl⟩ := covers x
  exact regular_at_image hdesc (f i) z (regular i z)

end AlgebraicGeometry.Scheme.RegularityDescent

end -- noncomputable section
end FlatLocalRegularityDescent
