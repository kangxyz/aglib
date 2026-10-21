/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FiniteFlatPurity
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Localization transport for finite-flat purity

These results use the actual iterated scalar extensions and prime contractions.
Flatness remains an explicit hypothesis; this is not the nonflat purity theorem.
-/

@[expose] public section

noncomputable section

open Module TensorProduct

namespace Algebra

/-- An etale fibre of a finite free algebra over a domain forces the generic fibre
 to be etale, by nonvanishing of the basis discriminant. -/
theorem etale_fractionRing_of_etale_fiber_of_basis {R B K ι : Type*}
    [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Field K] [Algebra R K] [Finite ι] (b : Basis ι R B)
    (h : Etale K (K ⊗[R] B)) : Etale (FractionRing R) (FractionRing R ⊗[R] B) := by
  classical
  let := Fintype.ofFinite ι
  have hn := (etale_iff_discr_ne_zero_of_basis (TensorProduct.basis K b)).mp h
  rw [discr_baseChange] at hn
  apply (etale_iff_discr_ne_zero_of_basis (TensorProduct.basis (FractionRing R) b)).mpr
  rw [discr_baseChange]
  intro hz
  have hd : discr R b = 0 := (IsFractionRing.injective R (FractionRing R))
    (hz.trans (map_zero _).symm)
  exact hn (by rw [hd, map_zero])

/-- Etaleness of a scalar extension persists along a further base-ring map,
with the iterated tensor product identified by the canonical cancellation map. -/
theorem etale_baseChange_of_tower {R S T B : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing B]
    [Algebra R S] [Algebra R T] [Algebra R B] [Algebra S T] [IsScalarTower R S T]
    [Etale S (S ⊗[R] B)] : Etale T (T ⊗[R] B) := by
  have : Etale T (T ⊗[S] (S ⊗[R] B)) := inferInstance
  exact Etale.of_equiv (TensorProduct.cancelBaseChange R S T T B)

/-- Etaleness is unchanged by the canonical cancellation of iterated scalar extension. -/
theorem etale_cancelBaseChange_iff {R S T B : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing B]
    [Algebra R S] [Algebra R T] [Algebra R B] [Algebra S T] [IsScalarTower R S T] :
    Etale T (T ⊗[S] (S ⊗[R] B)) ↔ Etale T (T ⊗[R] B) := by
  constructor
  · intro h
    have := h
    exact Etale.of_equiv (TensorProduct.cancelBaseChange R S T T B)
  · intro h
    have := h
    exact Etale.of_equiv (TensorProduct.cancelBaseChange R S T T B).symm

/-- Under the global generic and height-one hypotheses, every base localization
of a finite flat algebra is etale. Heights are compared by contraction along localization. -/
theorem etale_atPrime_of_generic_and_height_one_etale {R B : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B]
    (hgeneric : Etale (FractionRing R) (FractionRing R ⊗[R] B))
    (hcodim : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      Etale (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] B))
    (p : PrimeSpectrum R) :
    Etale (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] B) := by
  let S := Localization.AtPrime p.asIdeal
  have : Module.Free S (S ⊗[R] B) := Module.free_of_flat_of_isLocalRing
  apply etale_of_generic_and_height_one_etale_of_isLocalRing
  · have h : Etale (FractionRing R) (FractionRing R ⊗[S] (S ⊗[R] B)) :=
      (etale_cancelBaseChange_iff (R := R) (S := S)).mpr hgeneric
    exact etale_fractionRing_of_etale_fiber_of_basis (Module.Free.chooseBasis S (S ⊗[R] B)) h
  · intro q hq
    let q₀ : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
    have hq₀ : q₀.asIdeal.height = 1 :=
      (IsLocalization.height_under p.asIdeal.primeCompl q.asIdeal).trans hq
    let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      p.asIdeal.primeCompl q.asIdeal
    let : Algebra (Localization.AtPrime q₀.asIdeal) (Localization.AtPrime q.asIdeal) :=
      e.toRingHom.toAlgebra
    have : IsScalarTower R (Localization.AtPrime q₀.asIdeal)
        (Localization.AtPrime q.asIdeal) := IsScalarTower.of_algHom e.toAlgHom
    have := hcodim q₀ hq₀
    have : Etale (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal ⊗[R] B) :=
      etale_baseChange_of_tower (S := Localization.AtPrime q₀.asIdeal)
    exact (etale_cancelBaseChange_iff (R := R) (S := S)).mpr inferInstance

/-- Codimension-one purity for finite flat algebras over Noetherian domains.
The explicit generic etaleness hypothesis is essential when there are no height-one primes. -/
theorem etale_of_generic_and_height_one_etale {R B : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B]
    (hgeneric : Etale (FractionRing R) (FractionRing R ⊗[R] B))
    (hcodim : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      Etale (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] B)) :
    Etale R B := by
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hf (p : PrimeSpectrum R) : Etale p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] B) := by
    have := etale_atPrime_of_generic_and_height_one_etale hgeneric hcodim p
    exact etale_baseChange_of_tower (S := Localization.AtPrime p.asIdeal)
  have : Module.Finite R Ω[B⁄R] := Module.Finite.trans B Ω[B⁄R]
  have : FormallyUnramified R B := by
    constructor
    apply Module.subsingleton_of_subsingleton_residueField_tensorProduct (R := R)
    intro p
    have := hf p
    let : Algebra B (p.asIdeal.ResidueField ⊗[R] B) := TensorProduct.rightAlgebra
    exact (KaehlerDifferential.tensorKaehlerEquivBase R p.asIdeal.ResidueField B
      (p.asIdeal.ResidueField ⊗[R] B)).injective.subsingleton
  exact Etale.of_formallyUnramified_of_flat

end Algebra
