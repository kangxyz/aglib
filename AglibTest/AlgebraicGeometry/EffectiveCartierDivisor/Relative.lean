/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Fiberwise
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Open
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.BaseChange
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tilde
public import Aglib.RingTheory.Ideal.InvertiblePrincipal
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! Focused consumer of relative effective Cartier divisors: base change, the fibrewise
criterion (Kleiman, arXiv:math/0504020v1, Lemma 3.4, pp. 22-23; Stacks Project, Tag 062Y),
openness of the locus of Cartier fibres and its base-change characterization (proof of Kleiman,
Thm 3.7, p. 24), with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Hom

universe u

/-- The fibre of a relative effective Cartier divisor over every point is effective Cartier,
with no hypothesis on the ambient family. -/
example {D X T : Scheme.{u}} (p : X ⟶ T) (i : D ⟶ X) (hD : IsRelativeEffectiveCartier i p)
    (t : T) :
    IsEffectiveCartier (fibreInclusion p i (T.fromSpecResidueField t)) :=
  hD.fiberIsEffectiveCartier t

/-- Base change along an arbitrary morphism of the base. -/
example {D X T T' : Scheme.{u}} (p : X ⟶ T) (i : D ⟶ X) (hD : IsRelativeEffectiveCartier i p)
    (q : T' ⟶ T) :
    IsRelativeEffectiveCartier (fibreInclusion p i q) (pullback.snd p q) :=
  hD.fibreInclusion q

/-- The fibrewise criterion over an arbitrary, possibly non-Noetherian base. -/
example {D X T : Scheme.{u}} (p : X ⟶ T) (i : D ⟶ X) [Flat p] [LocallyOfFinitePresentation p]
    [IsClosedImmersion i] [Flat (i ≫ p)] [LocallyOfFinitePresentation (i ≫ p)] :
    IsRelativeEffectiveCartier i p ↔ ∀ t : T, FiberIsEffectiveCartier i p t :=
  isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier p i

/-- Kleiman's hypotheses: a locally Noetherian base and a flat family of finite type. -/
example {D X T : Scheme.{u}} [IsLocallyNoetherian T] (p : X ⟶ T) (i : D ⟶ X) [Flat p]
    [LocallyOfFiniteType p] [IsClosedImmersion i] [Flat (i ≫ p)] :
    IsRelativeEffectiveCartier i p ↔ ∀ t : T, FiberIsEffectiveCartier i p t :=
  isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier_of_isLocallyNoetherian p i

/-- Openness for a flat proper family over a locally Noetherian base. -/
example {D X T : Scheme.{u}} [IsLocallyNoetherian T] (p : X ⟶ T) [Flat p] [IsProper p]
    (i : D ⟶ X) [IsClosedImmersion i] [Flat (i ≫ p)] :
    IsOpen {t : T | FiberIsEffectiveCartier i p t} :=
  isOpen_setOf_fiberIsEffectiveCartier p i

/-- Over the open locus of Cartier fibres the divisor is a relative effective Cartier divisor. -/
example {D X T : Scheme.{u}} [IsLocallyNoetherian T] (p : X ⟶ T) [Flat p] [IsProper p]
    (i : D ⟶ X) [IsClosedImmersion i] [Flat (i ≫ p)] :
    IsRelativeEffectiveCartier (i ∣_ (p ⁻¹ᵁ fiberCartierLocus i p))
      (p ∣_ fiberCartierLocus i p) :=
  isRelativeEffectiveCartier_restrict_fiberCartierLocus p i

/-- The restriction statement needs no properness. -/
example {D X T : Scheme.{u}} [IsLocallyNoetherian T] (p : X ⟶ T) [Flat p]
    [LocallyOfFiniteType p] (i : D ⟶ X) [IsClosedImmersion i] [Flat (i ≫ p)] (U : T.Opens)
    (hU : ∀ t ∈ U, FiberIsEffectiveCartier i p t) :
    IsRelativeEffectiveCartier (i ∣_ (p ⁻¹ᵁ U)) (p ∣_ U) :=
  isRelativeEffectiveCartier_restrict p i U hU

/-- The base change along `g` is a relative effective Cartier divisor exactly when `g` lands in
the open locus of Cartier fibres (representability step of Kleiman's Thm 3.7). -/
example {D X T T' : Scheme.{u}} [IsLocallyNoetherian T] (p : X ⟶ T) [Flat p] [IsProper p]
    (i : D ⟶ X) [IsClosedImmersion i] [Flat (i ≫ p)] (g : T' ⟶ T) :
    IsRelativeEffectiveCartier (fibreInclusion p i g) (pullback.snd p g) ↔
      Set.range g ⊆ fiberCartierLocus i p :=
  isRelativeEffectiveCartier_fibreInclusion_iff_range_subset p i g

/-- Over an arbitrary base `T'`, for a flat finitely presented family. -/
example {D X T T' : Scheme.{u}} (p : X ⟶ T) [Flat p] [LocallyOfFinitePresentation p]
    (i : D ⟶ X) [IsClosedImmersion i] [Flat (i ≫ p)] [LocallyOfFinitePresentation (i ≫ p)]
    (g : T' ⟶ T) :
    IsRelativeEffectiveCartier (fibreInclusion p i g) (pullback.snd p g) ↔
      ∀ t' : T', FiberIsEffectiveCartier i p (g t') :=
  isRelativeEffectiveCartier_fibreInclusion_iff p i g

/-- The factorization form for arbitrary cartesian squares, as produced by a Hilbert-scheme
universal property. -/
example {D X T T' X' D' : Scheme.{u}} [IsLocallyNoetherian T] {p : X ⟶ T} [Flat p] [IsProper p]
    {i : D ⟶ X} [IsClosedImmersion i] [Flat (i ≫ p)] {g : T' ⟶ T} {b : X' ⟶ X}
    {p' : X' ⟶ T'} {a : D' ⟶ D} {i' : D' ⟶ X'} (H : IsPullback b p' p g)
    (H' : IsPullback a i' i b) :
    IsRelativeEffectiveCartier i' p' ↔
      ∃ g' : T' ⟶ (fiberCartierLocus i p).toScheme, g' ≫ (fiberCartierLocus i p).ι = g :=
  isRelativeEffectiveCartier_iff_exists_lift_of_isPullback H H'

/-- Transport along isomorphisms of the divisor, the ambient scheme and the base. -/
example {D X T D' X' T' : Scheme.{u}} {i : D ⟶ X} {p : X ⟶ T} {i' : D' ⟶ X'} {p' : X' ⟶ T'}
    (eD : D' ≅ D) (eX : X' ≅ X) (eT : T' ≅ T) (hi : i' ≫ eX.hom = eD.hom ≫ i)
    (hp : p' ≫ eT.hom = eX.hom ≫ p) (hD : IsRelativeEffectiveCartier i p) :
    IsRelativeEffectiveCartier i' p' :=
  hD.of_iso eD eX eT hi hp

/--
info: 'AlgebraicGeometry.Scheme.Hom.IsRelativeEffectiveCartier.of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.IsRelativeEffectiveCartier.of_isPullback

/--
info: 'AlgebraicGeometry.Scheme.Hom.IsRelativeEffectiveCartier.fiberIsEffectiveCartier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.IsRelativeEffectiveCartier.fiberIsEffectiveCartier

/--
info: 'AlgebraicGeometry.Scheme.Hom.spectralIdeal_isLocallyRankOne_of_fiberPullbackRankOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.spectralIdeal_isLocallyRankOne_of_fiberPullbackRankOne

/--
info: 'AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier

/--
info: 'AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier_of_isLocallyNoetherian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_iff_fiberIsEffectiveCartier_of_isLocallyNoetherian

/--
info: 'AlgebraicGeometry.Scheme.Hom.spectralIdeal_isLocallyRankOneAt_of_fiberPullbackRankOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.spectralIdeal_isLocallyRankOneAt_of_fiberPullbackRankOne

/--
info: 'AlgebraicGeometry.Scheme.Hom.isLocallyRankOneAt_idealModule_of_fiberIsEffectiveCartier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isLocallyRankOneAt_idealModule_of_fiberIsEffectiveCartier

/--
info: 'AlgebraicGeometry.Scheme.Hom.isOpen_setOf_fiberIsEffectiveCartier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isOpen_setOf_fiberIsEffectiveCartier

/--
info: 'AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_restrict

/--
info: 'AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_restrict_fiberCartierLocus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_restrict_fiberCartierLocus

/--
info: 'AlgebraicGeometry.Scheme.Hom.isLocallyRankOne_idealModule_of_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isLocallyRankOne_idealModule_of_pullback

/--
info: 'AlgebraicGeometry.Scheme.Hom.fiberIsEffectiveCartier_baseChange_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.fiberIsEffectiveCartier_baseChange_iff

/--
info: 'AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_fibreInclusion_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_fibreInclusion_iff

/--
info: 'AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_fibreInclusion_iff_range_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_fibreInclusion_iff_range_subset

/--
info: 'AlgebraicGeometry.Scheme.Hom.IsRelativeEffectiveCartier.of_iso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.IsRelativeEffectiveCartier.of_iso

/--
info: 'AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_iff_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_iff_of_isPullback

/--
info: 'AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_iff_exists_lift_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_iff_exists_lift_of_isPullback

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.tilde_isLocallyRankOne_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.tilde_isLocallyRankOne_iff

/--
info: 'Ideal.isSMulRegular_of_invertible_span_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.isSMulRegular_of_invertible_span_singleton
