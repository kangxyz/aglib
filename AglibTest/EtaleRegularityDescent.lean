/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.AlgebraicGeometry.Properties.Regular.Descent.Etale

/-! # Actual essentially etale regularity descent interfaces -/

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v

section Rings

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Module.Flat R S] [Algebra.FormallyUnramified R S]

example : Module.finrank (ResidueField S) (CotangentSpace S) =
    Module.finrank (ResidueField R) (CotangentSpace R) :=
  Algebra.FormallyUnramified.finrank_cotangentSpace_eq_of_flat R S

example : IsRegularLocalRing R ↔ IsRegularLocalRing S :=
  Algebra.FormallyUnramified.isRegularLocalRing_iff_of_flat R S

end Rings

example (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hflat : f.Flat) (hft : f.EssFiniteType)
    (hunram : f.FormallyUnramified) (hreg : IsRegularLocalRing S) :
    IsRegularLocalRing R := by
  let := hreg
  let := f.toAlgebra
  let : Module.Flat R S := hflat
  let : Algebra.EssFiniteType R S := hft
  let : Algebra.FormallyUnramified R S := hunram
  exact Algebra.FormallyUnramified.isRegularLocalRing_base_of_flat R S

section Schemes

example {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] [FormallyUnramified f] (x : X)
    (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) :=
  Scheme.RegularityDescent.Etale.regular_at_image_of_flat_formallyUnramified f x hx

example {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Etale f] (x : X)
    (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) :=
  Scheme.RegularityDescent.Etale.regular_at_image f x hx

example {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type v} (C : ι → Scheme.{u}) (f : ∀ i, C i ⟶ X)
    [∀ i, Etale (f i)] (covers : ∀ x : X, ∃ i, x ∈ Set.range (f i))
    (regular : ∀ i, Scheme.RegularStalks (C i)) : Scheme.RegularStalks X :=
  Scheme.RegularityDescent.Etale.regular_of_etale_cover C f covers regular

end Schemes
