/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Interfaces
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# Canonical Cartier restriction and image comparisons

Extracted from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Original declaration names, mathematical hypotheses, and source boundaries are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Cartier.Restriction` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5fa2c93be26b64739fcbbedf4690dbc06496a56255617f94be78f65d1fe33c2d`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (IsLocallyRankOne
    isLocallyRankOne_of_iso pullback_locallyRankOne)
universe u

open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Hom.Cartier
open AlgebraicGeometry.Scheme.Hom

/-- Actual closed-image factorization induces an isomorphism of actual ideal
modules, by the existing source-isomorphism kernel construction. -/
def idealImageIso {X D : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i] :
    idealModule i.imageι ≅ idealModule i :=
  idealSourceIso (asIso i.toImage) i.imageι ≪≫
    eqToIso (congrArg idealModule i.toImage_imageι)

/-- Generic Cartier pullback along an integral scheme avoiding containment. -/
def cartierRestrictionIso (havoid : IntegralAvoidanceCartierPullback.{u})
    {X D Y : Scheme.{u}} [IsIntegral Y] (i : D ⟶ X) (f : Y ⟶ X)
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i))
    (hn : ¬ Set.range f ⊆ Set.range i) :
    (Scheme.Modules.pullback f).obj (idealModule i) ≅ idealModule (pullback.snd i f) := by
  haveI := havoid X D Y i f inferInstance hI hn
  exact asIso (idealPullbackMap i (pullback.snd i f) f (pullback.fst i f)
    (pullback.condition (f := i) (g := f)))

theorem cartierRestriction_invertible (havoid : IntegralAvoidanceCartierPullback.{u})
    {X D Y : Scheme.{u}} [IsIntegral Y] (i : D ⟶ X) (f : Y ⟶ X)
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i))
    (hn : ¬ Set.range f ⊆ Set.range i) :
    IsLocallyRankOne Y (idealModule (pullback.snd i f)) :=
  isLocallyRankOne_of_iso Y (cartierRestrictionIso havoid i f hI hn)
    (pullback_locallyRankOne f _ hI)

end AlgebraicGeometry.Scheme.Hom.Cartier
