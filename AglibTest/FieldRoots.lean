/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.FieldTheory.AbsoluteGaloisGroup.RestrictScalars
import Aglib.FieldTheory.AlgebraicClosure.RelativeImage
import Aglib.FieldTheory.Divisors.FiniteConstants
import Aglib.FieldTheory.Divisors.UnitPowers
import Aglib.FieldTheory.Galois.FiniteCoefficientDependence
import Aglib.FieldTheory.Norm.RootFactorization
import Aglib.FieldTheory.Subfield.FiniteData
import Aglib.Analysis.Normed.Field.CyclicQuotient
import Aglib.RingTheory.RootsOfUnity.CharacterCompatibility
import Aglib.RingTheory.RootsOfUnity.PrimeToCharacteristic
import Aglib.RingTheory.RootsOfUnity.PrimeUnits
import Aglib.RingTheory.RootsOfUnity.NativeEmbedding
import Aglib.RingTheory.RootsOfUnity.IntegralClosureResidue
import Aglib.RingTheory.RootsOfUnity.Specialization
import Aglib.AlgebraicGeometry.FundamentalGroup.Field.ClosureAlgHom
import Aglib.AlgebraicGeometry.FundamentalGroup.Field.RootCoefficientAction

/-! Focused consumers for the actual finite scalar, conditional divisor, and root maps. -/

noncomputable section

universe u v w

open Field.absoluteGaloisGroup.RootsOfUnity

example {C K Div : Type u} [Field C] [Field K] [AddCommGroup Div]
    [IsAddTorsionFree Div] (d : Field.DivisorData C K Div)
    {n : ℕ} (hn : 0 < n) (a : Cˣ) :
    (∃ g : Kˣ, g ^ n = d.constant a) ↔ ∃ b : Cˣ, b ^ n = a :=
  d.constant_is_pow_iff hn a

example (K : Type u) [Field K] {ι : Type v}
    (p : MvPolynomial ι (AlgebraicClosure K)) :
    ∃ s : Finset (AlgebraicClosure K), ∀ g : Field.absoluteGaloisGroup K,
      (∀ a ∈ s, g.toRingHom a = a) → MvPolynomial.map g.toRingHom p = p :=
  Field.absoluteGaloisGroup.exists_finite_fixed_polynomial K p

example (K : Type u) [Field K] (n : ℕ) [NeZero n] [NeZero (n : K)] :
    Nat.card (Mu K n) = n :=
  PrimeToCharacteristic.mu_card_of_neZero K n

example {F K : Type u} [Field F] [Field K] [CharZero F] [CharZero K]
    (i : F →+* K) (n : ℕ) [NeZero n] :
    NativeEmbedding.nativeRootEmbedding i n =
      (AlgebraicGeometry.Scheme.FiniteEtale.Cyclotomic.RootCoordinates.rootEmbeddingLinear
        i n).restrictScalars ℤ := rfl

example (F : Type u) (L : Type v) (K : Type w)
    [Field F] [Field L] [Field K] [Algebra F L] [Algebra F K] [Algebra L K]
    [IsScalarTower F L K] [IsAlgClosure F L] (x : L) :
    (IsAlgClosure.algebraicImageEquiv F L K x : K) = algebraMap L K x := rfl

example {K : Type u} [Field K] (q : Kˣ)
    (hq : Function.Injective (fun z : ℤ => q ^ z))
    (H : Subgroup (QuotientGroup.CyclicQuotient q))
    (N : Units.CyclicQuotient.KernelNormalForm q hq H) :
    H = (QuotientGroup.zpowersPowerMap q N.p N.a N.b N.power_relation).ker :=
  N.actual_kernel

example {F K : Type u} [Field F] [Field K] [Algebra F K] (x : AlgebraicClosure F) :
    AlgebraicGeometry.Scheme.FiniteEtale.FieldEmbeddingBaseChange.closureAlgHom
        (F := F) (K := K) x =
      AlgebraicGeometry.Scheme.FiniteEtale.FieldEmbeddingBaseChange.closureEmbedding
        (algebraMap F K) x := rfl
