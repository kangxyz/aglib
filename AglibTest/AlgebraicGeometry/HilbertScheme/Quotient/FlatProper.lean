/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.FlatProper

/-!
# Flat proper quotients

The declarations below restate the consequences of a `FlatProperQuotient` used by the
representability of the Picard functor: the quotient morphism is flat, surjective, proper,
quasi-compact and, over a Noetherian ring, locally of finite presentation, so an fppf covering and
an effective epimorphism, hence a coequalizer of the relation; the quotient is locally Noetherian,
separated and locally of finite type over `Spec A`. They guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AglibTest.FlatProperQuotient

variable {A : Type u} [CommRing A] {Z R : Scheme.{u}} {πZ : Z ⟶ Spec (.of A)} {p₁ p₂ : R ⟶ Z}

/-- The quotient morphism is an fppf covering and an effective epimorphism over a Noetherian
ring. -/
theorem fppf_effectiveEpi [IsNoetherianRing A] (𝔮 : FlatProperQuotient πZ p₁ p₂) :
    Presieve.singleton 𝔮.q ∈ Scheme.fppfPrecoverage 𝔮.Q ∧ EffectiveEpi 𝔮.q ∧
      Flat 𝔮.q ∧ Surjective 𝔮.q ∧ LocallyOfFinitePresentation 𝔮.q ∧ QuasiCompact 𝔮.q :=
  ⟨𝔮.singleton_mem_fppfPrecoverage, 𝔮.effectiveEpi, inferInstance, inferInstance,
    𝔮.locallyOfFinitePresentation, 𝔮.quasiCompact⟩

/-- The quotient is a locally Noetherian test scheme, separated and locally of finite type over
`Spec A`, and the quotient morphism lies over `Spec A`. -/
theorem quotient_scheme [IsNoetherianRing A] (𝔮 : FlatProperQuotient πZ p₁ p₂) :
    IsLocallyNoetherian 𝔮.Q ∧ IsSeparated 𝔮.πQ ∧ LocallyOfFiniteType 𝔮.πQ ∧
      IsHQuasiProjective 𝔮.πQ ∧ 𝔮.q ≫ 𝔮.πQ = πZ :=
  ⟨inferInstance, 𝔮.isSeparated, 𝔮.locallyOfFiniteType, inferInstance, 𝔮.fac⟩

/-- The relation is the kernel pair of the quotient morphism, which is its coequalizer. -/
theorem kernelPair_coequalizer (𝔮 : FlatProperQuotient πZ p₁ p₂) :
    IsPullback p₁ p₂ 𝔮.q 𝔮.q ∧ p₁ ≫ 𝔮.q = p₂ ≫ 𝔮.q ∧
      Nonempty (IsColimit (Cofork.ofπ 𝔮.q 𝔮.isPullback.w)) :=
  ⟨𝔮.isPullback, 𝔮.isPullback.w, ⟨𝔮.isColimitCofork⟩⟩

/-- info: 'AglibTest.FlatProperQuotient.fppf_effectiveEpi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FlatProperQuotient.fppf_effectiveEpi

/-- info: 'AglibTest.FlatProperQuotient.quotient_scheme' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FlatProperQuotient.quotient_scheme

/-- info: 'AglibTest.FlatProperQuotient.kernelPair_coequalizer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FlatProperQuotient.kernelPair_coequalizer

end AglibTest.FlatProperQuotient
