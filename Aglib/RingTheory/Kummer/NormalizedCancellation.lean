/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.HeightOneNormalizedCancellation
public import Aglib.RingTheory.IntegralClosure.FiniteEtale.Purity
public import Aglib.RingTheory.RegularLocalRing.PrimeLocalization
public import Mathlib.FieldTheory.SeparableClosure

/-! # Normalized bounded root cancellation with its original open condition

The source is the literal normalization of the original generic tensor. Its
unramifiedness off the root divisor is the retained open-cover condition;
height-one cancellation proves the missing points on that divisor. Purity for
the same potentially disconnected normalization then gives etaleness.
This is the algebraic consumer; recovery of a supplied geometric open cover
is a separate original-map comparison.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.Kummer

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
  [IsRegularLocalRing (R ⧸ Ideal.span {f})]
  (N : ℕ) (hN : 0 < N) (hreg : IsSMulRegular R f)

local notation "T" => RootAlgebra N f
local notation "θ" => AdjoinRoot.root (rootPolynomial N f)

local instance : (Ideal.span {f} : Ideal R).IsPrime := regularParameter_span_isPrime R f

variable (K F L : Type u)
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field F] [Algebra R F] [Algebra (RootAlgebra N f) F]
  [IsScalarTower R (RootAlgebra N f) F] [IsFractionRing (RootAlgebra N f) F]
  [Algebra K F] [IsScalarTower R K F]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (Ω : Type u) [Field Ω]
  [Algebra (Localization.AtPrime (Ideal.span {f} : Ideal R)) Ω]
  [IsLocalHom (algebraMap (Localization.AtPrime (Ideal.span {f} : Ideal R)) Ω)]
  [IsSepClosed Ω]

include hf hN hreg Ω in
/-- The original normalized bounded root tensor is etale if its original
complement of the root divisor is unramified. The complement condition is
not replaced by a hypothesis on the points above the root. -/
theorem parameterRoot_normalization_etale
    (hunit : IsUnit (N : R)) (hcard : Nat.card (L ≃ₐ[K] L) ∣ N)
    [Algebra.FormallyUnramified (RootAlgebra N f)
      (Localization.Away
        (algebraMap (RootAlgebra N f)
          (integralClosure (RootAlgebra N f) (F ⊗[K] L))
          (AdjoinRoot.root (rootPolynomial N f))))] :
    Algebra.Etale T (integralClosure T (F ⊗[K] L)) := by
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsRegularRing T := IsRegularLocalRing.isRegularRing_of_regularLocal T
  let : Algebra.Etale K L := by
    let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    let : Algebra.FinitePresentation K L :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact ⟨inferInstance, inferInstance⟩
  apply integralClosure.etale_of_unramified_height_one T F (F ⊗[K] L)
  intro q hq
  by_cases hd : algebraMap T (integralClosure T (F ⊗[K] L)) θ ∈ q.asIdeal
  · exact parameterRoot_normalization_formallyUnramified_at_heightOne
      R f hf N hN hreg K F L Ω hunit hcard q.asIdeal hq hd
  · exact Algebra.FormallyUnramified.atPrime_of_away T
      (integralClosure T (F ⊗[K] L))
      (algebraMap T (integralClosure T (F ⊗[K] L)) θ) q.asIdeal hd

include hf hN hreg in
/-- The point field is constructed internally from the original parameter-prime
residue field. Only the original fraction fields and original complement
condition remain as inputs. -/
theorem parameterRoot_normalization_etale_of_away
    (hunit : IsUnit (N : R)) (hcard : Nat.card (L ≃ₐ[K] L) ∣ N)
    [Algebra.FormallyUnramified (RootAlgebra N f)
      (Localization.Away
        (algebraMap (RootAlgebra N f)
          (integralClosure (RootAlgebra N f) (F ⊗[K] L))
          (AdjoinRoot.root (rootPolynomial N f))))] :
    Algebra.Etale T (integralClosure T (F ⊗[K] L)) := by
  let D₀ := Localization.AtPrime (Ideal.span {f} : Ideal R)
  let Ω₀ := SeparableClosure (IsLocalRing.ResidueField D₀)
  let : Algebra D₀ Ω₀ :=
    ((algebraMap (IsLocalRing.ResidueField D₀) Ω₀).comp (IsLocalRing.residue D₀)).toAlgebra
  let : IsLocalHom (algebraMap D₀ Ω₀) := by
    constructor
    intro r hr
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (R := D₀) r).mp
    intro hz
    apply hr.ne_zero
    change algebraMap (IsLocalRing.ResidueField D₀) Ω₀ (IsLocalRing.residue D₀ r) = 0
    rw [hz, map_zero]
  exact parameterRoot_normalization_etale R f hf N hN hreg K F L Ω₀ hunit hcard

end Algebra.Kummer
