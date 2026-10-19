/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Fibre
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Flat
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Relative effective Cartier divisors

An effective Cartier divisor of a scheme `X` is a closed immersion `i : D ⟶ X` whose actual
kernel ideal module `idealModule i` is locally free of rank one (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, 3.1, p. 22; Stacks Project, Tag 01WR). A relative effective Cartier
divisor of `p : X ⟶ T` is an effective Cartier divisor which is flat over `T` (Kleiman,
Def. 3.3, p. 22; Stacks Project, Tag 062T). The predicates use the existing closed-immersion,
`IsLocallyRankOne` and `Flat` conditions; no new ideal-sheaf predicate is introduced.

Relative effective Cartier divisors are stable under every cartesian base change of the base
(Kleiman, the remark after Def. 3.6, p. 23; Stacks Project, Tag 056Q): flatness of `D` over `T`
makes the ideal of the base change the pullback of the ideal
(`Scheme.Hom.flatQuotient_idealPullbackMap_isIso`). In particular every fibre `D_t ⊆ X_t` of a
relative effective Cartier divisor is an effective Cartier divisor of the fibre
`X_t = p.fiber t`, which is the fibre part of the implication (i) ⇒ (ii) of Kleiman's Lemma 3.4.
No flatness, finiteness or Noetherian hypothesis on `p` is used here.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Hom

variable {D X T : Scheme.{u}}

/-- An effective Cartier divisor: a closed immersion whose actual ideal module is locally free
of rank one (Kleiman, 3.1). -/
structure IsEffectiveCartier (i : D ⟶ X) : Prop where
  isClosedImmersion : IsClosedImmersion i
  isLocallyRankOne : IsLocallyRankOne X (idealModule i)

/-- A relative effective Cartier divisor of `p : X ⟶ T`: an effective Cartier divisor
`i : D ⟶ X` such that `i ≫ p` is flat (Kleiman, Def. 3.3). -/
structure IsRelativeEffectiveCartier (i : D ⟶ X) (p : X ⟶ T) : Prop
    extends IsEffectiveCartier i where
  flat : Flat (i ≫ p)

/-- The fibre `D_t ⊆ X_t` over a point `t` of the base is an effective Cartier divisor of the
scheme-theoretic fibre `p.fiber t`. -/
abbrev FiberIsEffectiveCartier (i : D ⟶ X) (p : X ⟶ T) (t : T) : Prop :=
  IsEffectiveCartier (fibreInclusion p i (T.fromSpecResidueField t))

/-- Relative effective Cartier divisors are stable under every cartesian base change of the
base: the ideal of the base change is the pullback of the original ideal, because the original
divisor is flat over the base (Kleiman, remark after Def. 3.6). -/
theorem IsRelativeEffectiveCartier.of_isPullback {S Y D' : Scheme.{u}}
    {p : X ⟶ S} {q : T ⟶ S} {p' : Y ⟶ T} {b : Y ⟶ X}
    {i : D ⟶ X} {i' : D' ⟶ Y} {a : D' ⟶ D}
    (H : IsPullback b p' p q) (H' : IsPullback a i' i b)
    (hD : IsRelativeEffectiveCartier i p) : IsRelativeEffectiveCartier i' p' := by
  have := hD.isClosedImmersion
  have := hD.flat
  have hi' : IsClosedImmersion i' := MorphismProperty.of_isPullback H' inferInstance
  have : IsIso (idealPullbackMap i i' b a H'.w) :=
    flatQuotient_idealPullbackMap_isIso p q p' b i i' a H'.w H H'
  refine ⟨⟨hi', ?_⟩, ?_⟩
  · exact isLocallyRankOne_of_iso Y (asIso (idealPullbackMap i i' b a H'.w))
      (pullback_locallyRankOne b _ hD.isLocallyRankOne)
  · exact MorphismProperty.of_isPullback (H'.paste_vert H) hD.flat

/-- Relative effective Cartier divisors transport along isomorphisms of the divisor, the ambient
scheme and the base that commute with the closed immersions and the structure morphisms. -/
theorem IsRelativeEffectiveCartier.of_iso {D' X' T' : Scheme.{u}} {i : D ⟶ X} {p : X ⟶ T}
    {i' : D' ⟶ X'} {p' : X' ⟶ T'} (eD : D' ≅ D) (eX : X' ≅ X) (eT : T' ≅ T)
    (hi : i' ≫ eX.hom = eD.hom ≫ i) (hp : p' ≫ eT.hom = eX.hom ≫ p)
    (hD : IsRelativeEffectiveCartier i p) : IsRelativeEffectiveCartier i' p' :=
  hD.of_isPullback (IsPullback.of_horiz_isIso ⟨hp.symm⟩) (IsPullback.of_horiz_isIso ⟨hi.symm⟩)

/-- The canonical base change of a relative effective Cartier divisor along any morphism of
the base. -/
theorem IsRelativeEffectiveCartier.fibreInclusion {p : X ⟶ T} {i : D ⟶ X}
    (hD : IsRelativeEffectiveCartier i p) {T' : Scheme.{u}} (q : T' ⟶ T) :
    IsRelativeEffectiveCartier (fibreInclusion p i q) (pullback.snd p q) :=
  hD.of_isPullback (IsPullback.of_hasPullback p q) (fibreInclusion_isPullback p i q)

/-- Every fibre `D_t ⊆ X_t` of a relative effective Cartier divisor is an effective Cartier
divisor (Kleiman, Lemma 3.4, (i) ⇒ (ii), fibre part). -/
theorem IsRelativeEffectiveCartier.fiberIsEffectiveCartier {p : X ⟶ T} {i : D ⟶ X}
    (hD : IsRelativeEffectiveCartier i p) (t : T) : FiberIsEffectiveCartier i p t :=
  (hD.fibreInclusion (T.fromSpecResidueField t)).toIsEffectiveCartier

/-- The fibre condition only concerns local rank one of the actual fibre ideal: the fibre
inclusion of a closed immersion is a closed immersion. -/
theorem fiberIsEffectiveCartier_iff (p : X ⟶ T) (i : D ⟶ X) [IsClosedImmersion i] (t : T) :
    FiberIsEffectiveCartier i p t ↔ IsLocallyRankOne (p.fiber t)
      (idealModule (fibreInclusion p i (T.fromSpecResidueField t))) :=
  ⟨fun h ↦ h.isLocallyRankOne, fun h ↦ ⟨inferInstance, h⟩⟩

end AlgebraicGeometry.Scheme.Hom
