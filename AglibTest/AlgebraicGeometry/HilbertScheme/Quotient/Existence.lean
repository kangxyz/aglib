/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Existence

/-!
# Existence of quotients by flat proper equivalence relations

Focused consumer of Nitsure's Theorem 6.9 (arXiv:math/0504590v1, p. 36, by the proof of
Theorem 6.8, pp. 33–35) over a Noetherian ring `A`: the quotient of an H-quasi-projective `Z` by a
relation `(p₁, p₂)` with `p₂` (or `p₁`) proper and flat, injective and an equivalence relation on
locally Noetherian points, with the consequences of the packaged `FlatProperQuotient`; the steps of
the proof (closed immersion `(p₁, p₂)`, normalized immersion into projective space, the Hilbert
datum from the finite union of Hilbert schemes); the trivial relation as an instance of the
hypotheses; and axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AglibTest.FlatProperQuotientExistence

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {Z R : Scheme.{u}}

/-- **The quotient and its consequences**: the quotient exists; `q` is flat, surjective, proper,
quasi-compact, locally of finite presentation, an effective epimorphism, a coequalizer of `p₁, p₂`
and an fppf covering; `Q` is locally Noetherian and H-quasi-projective, separated and locally of
finite type over `Spec A`; and `R = Z ×_Q Z`. -/
theorem exists_flatProperQuotient (πZ : Z ⟶ Spec (.of A)) [IsHQuasiProjective πZ]
    (p₁ p₂ : R ⟶ Z) (hp : p₁ ≫ πZ = p₂ ≫ πZ) [IsProper p₂] [Flat p₂]
    (hinj : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (r r' : T ⟶ R),
      r ≫ p₁ = r' ≫ p₁ → r ≫ p₂ = r' ≫ p₂ → r = r')
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation p₁ p₂ T)) :
    ∃ 𝔮 : FlatProperQuotient πZ p₁ p₂, 𝔮.q ≫ 𝔮.πQ = πZ ∧ IsHQuasiProjective 𝔮.πQ ∧
      Flat 𝔮.q ∧ Surjective 𝔮.q ∧ IsProper 𝔮.q ∧ IsPullback p₁ p₂ 𝔮.q 𝔮.q ∧
      QuasiCompact 𝔮.q ∧ LocallyOfFinitePresentation 𝔮.q ∧ IsLocallyNoetherian 𝔮.Q ∧
      IsSeparated 𝔮.πQ ∧ LocallyOfFiniteType 𝔮.πQ ∧ EffectiveEpi 𝔮.q ∧
      Presieve.singleton 𝔮.q ∈ Scheme.fppfPrecoverage 𝔮.Q ∧
      Nonempty (IsColimit (Cofork.ofπ 𝔮.q 𝔮.isPullback.w)) := by
  obtain ⟨𝔮⟩ := nonempty_flatProperQuotient πZ p₁ p₂ hp hinj hequiv
  exact ⟨𝔮, 𝔮.fac, 𝔮.isHQuasiProjective, 𝔮.flat, 𝔮.surjective, 𝔮.isProper, 𝔮.isPullback,
    𝔮.quasiCompact, 𝔮.locallyOfFinitePresentation, inferInstance, 𝔮.isSeparated,
    𝔮.locallyOfFiniteType, 𝔮.effectiveEpi, 𝔮.singleton_mem_fppfPrecoverage,
    ⟨𝔮.isColimitCofork⟩⟩

/-- **The first projection proper and flat**: the quotient exists, and its kernel pair is `R`
through `(p₁, p₂)`; it is the flip of a quotient by `(p₂, p₁)` with the same `q`. -/
theorem exists_flatProperQuotient_of_fst (πZ : Z ⟶ Spec (.of A)) [IsHQuasiProjective πZ]
    (p₁ p₂ : R ⟶ Z) (hp : p₁ ≫ πZ = p₂ ≫ πZ) [IsProper p₁] [Flat p₁]
    (hinj : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (r r' : T ⟶ R),
      r ≫ p₁ = r' ≫ p₁ → r ≫ p₂ = r' ≫ p₂ → r = r')
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation p₁ p₂ T)) :
    (∃ 𝔮 : FlatProperQuotient πZ p₁ p₂, IsPullback p₁ p₂ 𝔮.q 𝔮.q ∧ EffectiveEpi 𝔮.q) ∧
      ∀ 𝔮 : FlatProperQuotient πZ p₂ p₁, 𝔮.flip.q = 𝔮.q ∧ 𝔮.flip.πQ = 𝔮.πQ := by
  obtain ⟨𝔮⟩ := nonempty_flatProperQuotient_of_isProper_fst_of_flat_fst πZ p₁ p₂ hp hinj hequiv
  exact ⟨⟨𝔮, 𝔮.isPullback, 𝔮.effectiveEpi⟩, fun 𝔮 => ⟨𝔮.flip_q, 𝔮.flip_πQ⟩⟩

/-- **The trivial relation** `p₁ = p₂ = 𝟙` satisfies the hypotheses, so every H-quasi-projective
`Z` over a Noetherian ring is a flat proper quotient of itself by the diagonal. -/
theorem nonempty_flatProperQuotient_id (πZ : Z ⟶ Spec (.of A)) [IsHQuasiProjective πZ] :
    Nonempty (FlatProperQuotient πZ (𝟙 Z) (𝟙 Z)) := by
  refine nonempty_flatProperQuotient πZ (𝟙 Z) (𝟙 Z) rfl
    (fun T _ r r' h _ => by simpa using h) fun T _ => ⟨fun a => ⟨a, by simp, by simp⟩, ?_, ?_⟩
  · rintro a b ⟨r, rfl, rfl⟩
    exact ⟨r, rfl, rfl⟩
  · rintro a b c ⟨r, rfl, rfl⟩ ⟨r', hr', rfl⟩
    exact ⟨r', hr', rfl⟩

/-- **The steps of the proof**: the relation `(p₁, p₂)` is a closed immersion; `Z` has an immersion
into projective space with coordinates `Fin (n + 1)`; and a closed relation that is proper, flat
and surjective over the second factor has a Hilbert datum with `H` H-quasi-projective. -/
theorem proof_steps (πZ : Z ⟶ Spec (.of A)) [IsHQuasiProjective πZ] (p₁ p₂ : R ⟶ Z)
    (hp : p₁ ≫ πZ = p₂ ≫ πZ) [IsProper p₂]
    (hinj : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (r r' : T ⟶ R),
      r ≫ p₁ = r' ≫ p₁ → r ≫ p₂ = r' ≫ p₂ → r = r')
    (j : R ⟶ pullback πZ πZ) [IsClosedImmersion j] [IsProper (j ≫ pullback.snd πZ πZ)]
    [Flat (j ≫ pullback.snd πZ πZ)] [Surjective (j ≫ pullback.snd πZ πZ)] :
    IsClosedImmersion (pullback.lift p₁ p₂ hp) ∧
      (∃ (ι : Type u) (n : ℕ) (_ : ι ≃ Fin (n + 1)) (i : Z ⟶ ProjectiveSpace A ι),
        IsImmersion i ∧ QuasiCompact i ∧ i ≫ ProjectiveSpace.toSpec A ι = πZ) ∧
      ∃ 𝔥 : QuotientHilbertDatum πZ j, IsHQuasiProjective 𝔥.πH := by
  have := IsHQuasiProjective.isLocallyNoetherian πZ
  exact ⟨isClosedImmersion_pullback_lift_of_isProper_snd_of_locallyNoetherian_injective πZ p₁ p₂ hp
      hinj,
    IsHQuasiProjective.exists_isImmersion_equivFin πZ,
    QuotientHilbertDatum.exists_isHQuasiProjective πZ j⟩

/-- **Swapping the relation**: points related by `(p₂, p₁)` are those related by `(p₁, p₂)` in
the other order, and an equivalence relation on points stays one. -/
theorem pointsRelation_swap (p₁ p₂ : R ⟶ Z) (T : Scheme.{u})
    (h : _root_.Equivalence (pointsRelation p₁ p₂ T)) (a b : T ⟶ Z) :
    (pointsRelation p₂ p₁ T a b ↔ pointsRelation p₁ p₂ T b a) ∧
      _root_.Equivalence (pointsRelation p₂ p₁ T) :=
  ⟨pointsRelation_swap_iff p₁ p₂ T a b, equivalence_pointsRelation_swap h⟩

end AglibTest.FlatProperQuotientExistence

/-- info: 'AlgebraicGeometry.nonempty_flatProperQuotient' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.nonempty_flatProperQuotient

/-- info: 'AlgebraicGeometry.nonempty_flatProperQuotient_of_isProper_fst_of_flat_fst' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.nonempty_flatProperQuotient_of_isProper_fst_of_flat_fst

/-- info: 'AlgebraicGeometry.FlatProperQuotient.flip' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.FlatProperQuotient.flip

/-- info: 'AlgebraicGeometry.QuotientHilbertDatum.exists_isHQuasiProjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.QuotientHilbertDatum.exists_isHQuasiProjective

/--
info: 'AlgebraicGeometry.isClosedImmersion_pullback_lift_of_isProper_snd_of_locallyNoetherian_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.isClosedImmersion_pullback_lift_of_isProper_snd_of_locallyNoetherian_injective

/-- info: 'CategoryTheory.pointsRelation_swap_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.pointsRelation_swap_iff

/-- info: 'CategoryTheory.equivalence_pointsRelation_swap' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.equivalence_pointsRelation_swap

/-- info: 'AglibTest.FlatProperQuotientExistence.exists_flatProperQuotient' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FlatProperQuotientExistence.exists_flatProperQuotient

/-- info: 'AglibTest.FlatProperQuotientExistence.exists_flatProperQuotient_of_fst' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FlatProperQuotientExistence.exists_flatProperQuotient_of_fst

/-- info: 'AglibTest.FlatProperQuotientExistence.nonempty_flatProperQuotient_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FlatProperQuotientExistence.nonempty_flatProperQuotient_id

/-- info: 'AglibTest.FlatProperQuotientExistence.proof_steps' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FlatProperQuotientExistence.proof_steps
