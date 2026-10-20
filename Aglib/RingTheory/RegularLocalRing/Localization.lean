/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Regularity under localization

Relocated from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing mathematical declarations and explicit source boundaries are retained.
-/

universe u

/-!
# Regularity under localization

General algebraic lemmas used by the literal DVR-node proof. They construct the
comparison between a prime localization of a localization and the original
prime localization. The only mathematical input is regularity of the coefficient
ring; no regularity premise for a node or a resolution is present.

Pinned Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/RegularLocalRing/Localization.lean` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`cd6b9c093f7e569cad7707ec7ec0bf2696689a2e5f69201afb3773f3ec2e09b4`.
-/

@[expose] public section

noncomputable section
namespace IsRegularRing

/-- A localization of a regular ring is regular. -/
lemma regular_localization (R S : Type*) [CommRing R] [CommRing S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S] [IsRegularRing R] :
    IsRegularRing S := by
  have := IsLocalization.isNoetherianRing M S (inferInstance : IsNoetherianRing R)
  apply isRegularRing_iff.mpr
  intro p hp
  let T := Localization.AtPrime p
  let : IsLocalization.AtPrime T (p.comap (algebraMap R S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M T p
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (p.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (p.comap (algebraMap R S))) T).toRingEquiv

/-- A prime stalk whose prime misses a principal open is a stalk of that open. -/
lemma regular_atPrime_of_away (R : Type*) [CommRing R] (a : R)
    [IsRegularRing (Localization.Away a)] (p : Ideal R) [p.IsPrime] (ha : a ∉ p) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let S := Localization.Away a
  let q := p.map (algebraMap R S)
  have disj : Disjoint (Submonoid.powers a : Set R) (p : Set R) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hn
    exact ha ((inferInstance : p.IsPrime).mem_of_pow_mem _ hn)
  let : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers a) S p inferInstance disj
  let T := Localization.AtPrime q
  have hq : q.comap (algebraMap R S) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) S inferInstance disj
  let : IsLocalization.AtPrime T p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers a) T q using 1
    exact hq.symm
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl T (Localization.AtPrime p)).toRingEquiv

end IsRegularRing

