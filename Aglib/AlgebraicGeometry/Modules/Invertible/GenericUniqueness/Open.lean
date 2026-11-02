/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Restriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.GenericUniqueness


/-!
# Ordinary line-target uniqueness along an actual nonempty open immersion

The original Hom-range comparison translates the established dense-open
section uniqueness to the actual restriction and pullback functors. Only
ordinary sheaf morphisms are compared; no derived or raw-evaluation assertion
is made.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem rangeHomToRestriction_over {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N) :
    InternalHom.rangeHomToRestriction j (f.over j.opensRange) =
      (restrictFunctor j).map f := by
  ext V m
  rfl

/-- Original maps into a line on an integral scheme agree if equal on one nonempty open chart. -/
theorem hom_ext_of_nonempty_restrict {U X : Scheme.{u}} [IsIntegral X] [Nonempty U]
    (j : U ⟶ X) [IsOpenImmersion j] {M N : X.Modules} (hN : IsLocallyRankOne X N)
    {f g : M ⟶ N} (h : (restrictFunctor j).map f = (restrictFunctor j).map g) : f = g := by
  obtain ⟨u⟩ := ‹Nonempty U›
  let : Nonempty j.opensRange := ⟨⟨j u, ⟨u, rfl⟩⟩⟩
  apply hom_ext_of_nonempty_over hN j.opensRange
  apply (InternalHom.rangeRestrictionHomEquiv j M N).symm.injective
  exact (rangeHomToRestriction_over j f).trans (h.trans (rangeHomToRestriction_over j g).symm)

/-- The original restriction/pullback comparison gives the same ordinary line-target uniqueness. -/
theorem hom_ext_of_nonempty_pullback {U X : Scheme.{u}} [IsIntegral X] [Nonempty U]
    (j : U ⟶ X) [IsOpenImmersion j] {M N : X.Modules} (hN : IsLocallyRankOne X N)
    {f g : M ⟶ N} (h : (pullback j).map f = (pullback j).map g) : f = g := by
  apply hom_ext_of_nonempty_restrict j hN
  apply (cancel_mono ((restrictFunctorIsoPullback j).hom.app N)).mp
  exact ((restrictFunctorIsoPullback j).hom.naturality f).trans
    ((congrArg (fun z => (restrictFunctorIsoPullback j).hom.app M ≫ z) h).trans
      ((restrictFunctorIsoPullback j).hom.naturality g).symm)

end AlgebraicGeometry.Scheme.Modules.Invertible
