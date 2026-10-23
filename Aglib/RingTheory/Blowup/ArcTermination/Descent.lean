/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.ArcTermination
public import Aglib.RingTheory.RegularLocalRing.QuotientLift
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Finite iteration of the actual local arc chart

The exponent is the least exponent realized by an actual minimum-cardinality
kernel generating set and an actual normalized squared-kernel relation. All
successor maps, generators and relations are the original constructions from
`ArcTermination`. The constructed successor strictly decreases this measure
until its actual local ring is regular. No successor decrease is an input.
-/

@[expose] public noncomputable section

universe u v

namespace Ideal

/-- A normalized two-generator relation in a minimum-cardinality generating
set has positive exponents. A zero exponent removes an actual generator by
Nakayama, including the case of a unit coefficient on the first generator. -/
theorem pos_exponents_of_minimal_generators_relation
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (p : Ideal A) (hp : p ≤ IsLocalRing.maximalIdeal A) (s : Finset A)
    (hspan : Ideal.span (s : Set A) = p) (hcard : s.card = p.spanFinrank)
    (x y : A) (hx : x ∈ s) (hy : y ∈ s) (hne : y ≠ x)
    (t : A) (a : Aˣ) (n m : ℕ)
    (hrel : t ^ n * y - (a : A) * t ^ m * x ∈ p ^ 2) : 0 < n ∧ 0 < m := by
  have hindy := not_mem_span_sdiff_sup_sq_of_minimal_generators p hp s hspan hcard y hy
  have hindx := not_mem_span_sdiff_sup_sq_of_minimal_generators p hp s hspan hcard x hx
  constructor
  · by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    apply hindy
    let J := Ideal.span ((s : Set A) \ {y}) ⊔ p ^ 2
    have hxJ : x ∈ J := Submodule.mem_sup_left (Ideal.subset_span ⟨hx, hne.symm⟩)
    have hrel0 : y - (a : A) * t ^ m * x ∈ J :=
      Submodule.mem_sup_right (by simpa only [hn0, pow_zero, one_mul] using hrel)
    have h := J.add_mem hrel0 (J.mul_mem_left ((a : A) * t ^ m) hxJ)
    simpa only [sub_add_cancel] using h
  · by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    apply hindx
    let J := Ideal.span ((s : Set A) \ {x}) ⊔ p ^ 2
    have hyJ : y ∈ J := Submodule.mem_sup_left (Ideal.subset_span ⟨hy, hne⟩)
    have hrel0 : t ^ n * y - (a : A) * x ∈ J :=
      Submodule.mem_sup_right (by simpa only [hm0, pow_zero, mul_one] using hrel)
    have hunit : (a : A) * x ∈ J := by
      simpa only [sub_sub_cancel] using J.sub_mem (J.mul_mem_left (t ^ n) hyJ) hrel0
    exact (Ideal.unit_mul_mem_iff_mem J a.isUnit).mp hunit

/-- The one-term version forces a positive exponent as well. -/
theorem pos_exponent_of_minimal_generators_torsion
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (p : Ideal A) (hp : p ≤ IsLocalRing.maximalIdeal A) (s : Finset A)
    (hspan : Ideal.span (s : Set A) = p) (hcard : s.card = p.spanFinrank)
    (x : A) (hx : x ∈ s) (t : A) (n : ℕ) (hrel : t ^ n * x ∈ p ^ 2) :
    0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  apply not_mem_span_sdiff_sup_sq_of_minimal_generators p hp s hspan hcard x hx
  exact Submodule.mem_sup_right (by simpa only [hn0, pow_zero, one_mul] using hrel)

end Ideal

namespace Localization.Away

/-- The exact kernel-generation equation, shared by the localization producer
and the abstract minimality consumer before specializing the target ring. -/
def KernelSpanEq {A B : Type*} [CommRing A] [CommRing B]
    (g : A →+* B) (s : Finset A) : Prop :=
  Ideal.span (s : Set A) = RingHom.ker g

variable {C : Type u} [CommRing C] {R : Type v} [CommRing R] [IsDomain R]

attribute [local instance] RingHom.ker_isPrime

/-- Localization of the actual chart kernel supplies its generating equation
on an abstract target ring. This fixes the equation's ring presentation before
the producer and minimality consumer are specialized to the native arc ring. -/
theorem kernelSpanEq_of_arcChart_localization
    (f : C →+* R) (t : C) (ht : f t ≠ 0)
    {D : Type*} [CommRing D] [Algebra (arcChart f t) D]
    (M : Submonoid (arcChart f t)) [IsLocalization M D]
    (H : D →+* R)
    (hcomp : H.comp (algebraMap (arcChart f t) D) = arcMap f t ht)
    {ι : Type*} (z : ι → RingHom.ker f)
    (hz : Ideal.span (Set.range fun i => (z i : C)) = RingHom.ker f)
    (v : Finset D)
    (hv : (v : Set D) = Set.range fun i =>
      algebraMap (arcChart f t) D (arcFraction f t (z i))) : KernelSpanEq H v := by
  have hker : RingHom.ker H = (RingHom.ker (arcMap f t ht)).map
      (algebraMap (arcChart f t) D) := by
    calc
      RingHom.ker H = ((RingHom.ker H).comap
          (algebraMap (arcChart f t) D)).map (algebraMap (arcChart f t) D) :=
        (IsLocalization.map_under M D (RingHom.ker H)).symm
      _ = _ := by rw [RingHom.comap_ker, hcomp]
  unfold KernelSpanEq
  rw [hv, hker, ker_arcMap_eq_span f t ht z hz, Ideal.map_span]
  congr 1
  exact Set.range_comp' (algebraMap (arcChart f t) D) (fun i => arcFraction f t (z i))

section LocalFraction

variable [IsLocalRing R]

/-- The original kernel fraction in the actual closed-point local ring. -/
def localArcFraction (f : C →+* R) (t : C) (ht : f t ≠ 0)
    (z : RingHom.ker f) : arcLocalRing f t ht :=
  algebraMap (arcChart f t) (arcLocalRing f t ht) (arcFraction f t z)

@[simp]
theorem arcLocalMap_localArcFraction (f : C →+* R) (t : C) (ht : f t ≠ 0)
    (z : RingHom.ker f) : arcLocalMap f t ht (localArcFraction f t ht z) = 0 := by
  simp only [localArcFraction, arcLocalMap_base, arcMap_arcFraction]

/-- The actual exceptional multiplication equation after closed-point localization. -/
theorem exceptional_mul_localArcFraction (f : C →+* R) (t : C) (ht : f t ≠ 0)
    (z : RingHom.ker f) :
    arcLocalBase f t ht t * localArcFraction f t ht z = arcLocalBase f t ht z := by
  simpa only [arcLocalBase, RingHom.comp_apply, localArcFraction, map_mul] using
    congrArg (algebraMap (arcChart f t) (arcLocalRing f t ht))
      (exceptional_mul_arcFraction f t z)

/-- The original scalar map to the actual local arc ring is injective over a domain. -/
theorem arcLocalBase_injective [IsDomain C]
    (f : C →+* R) (t : C) (ht : f t ≠ 0) : Function.Injective (arcLocalBase f t ht) := by
  intro x y h
  apply IsLocalization.injective (Localization.AtPrime (RingHom.ker f))
    (RingHom.ker f).primeCompl_le_nonZeroDivisors
  simpa only [arcLocalToGeneric_arcLocalBase] using congrArg (arcLocalToGeneric f t ht) h

/-- Distinct original kernel generators remain distinct after actual division
and closed-point localization. -/
theorem localArcFraction_injective [IsDomain C]
    (f : C →+* R) (t : C) (ht : f t ≠ 0) : Function.Injective (localArcFraction f t ht) := by
  intro x y h
  apply Subtype.ext
  apply arcLocalBase_injective f t ht
  have he := congrArg (fun a => arcLocalBase f t ht t * a) h
  simpa only [exceptional_mul_localArcFraction] using he

/-- Division by the exceptional unit preserves the distinguished original
generic uniformizer, using the proved original generic-ring equivalence. -/
theorem irreducible_localArcFraction_generic
    (f : C →+* R) (t : C) (ht : f t ≠ 0) (z : RingHom.ker f)
    (hz : Irreducible (algebraMap C (Localization.AtPrime (RingHom.ker f)) z)) :
    Irreducible (algebraMap (arcLocalRing f t ht)
      (Localization.AtPrime (RingHom.ker (arcLocalMap f t ht)))
        (localArcFraction f t ht z)) := by
  have hu : IsUnit (algebraMap C (Localization.AtPrime (RingHom.ker f)) t) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime (RingHom.ker f)) (RingHom.ker f) t).mpr
        (fun h => ht (RingHom.mem_ker.mp h))
  have he : algebraMap C (Localization.AtPrime (RingHom.ker f)) t *
      arcLocalToGeneric f t ht (localArcFraction f t ht z) =
        algebraMap C (Localization.AtPrime (RingHom.ker f)) z := by
    simpa only [map_mul, arcLocalToGeneric_arcLocalBase] using
      congrArg (arcLocalToGeneric f t ht) (exceptional_mul_localArcFraction f t ht z)
  have hirr : Irreducible (arcLocalToGeneric f t ht (localArcFraction f t ht z)) :=
    (irreducible_isUnit_mul hu).mp (he.symm ▸ hz)
  have hinv : (arcGenericEquiv f t ht).symm
      (algebraMap (arcLocalRing f t ht) (arcGenericLocalRing f t ht)
        (localArcFraction f t ht z)) = arcLocalToGeneric f t ht (localArcFraction f t ht z) :=
    arcGenericInverse_base f t ht _
  change Irreducible (algebraMap (arcLocalRing f t ht) (arcGenericLocalRing f t ht)
    (localArcFraction f t ht z))
  exact (MulEquiv.irreducible_iff (arcGenericEquiv f t ht).symm).mp (hinv.symm ▸ hirr)

/-- A specified actual original kernel generating set after literal division. -/
def dividedKernelFamily (f : C →+* R) (t : C) (ht : f t ≠ 0)
    (s : Finset C) (hs : Ideal.span (s : Set C) = RingHom.ker f) : s → arcLocalRing f t ht :=
  fun i => localArcFraction f t ht ⟨i, hs ▸ Ideal.subset_span i.property⟩

/-- The corresponding finite set in the actual next local ring. -/
def dividedKernelFinset (f : C →+* R) (t : C) (ht : f t ≠ 0)
    (s : Finset C) (hs : Ideal.span (s : Set C) = RingHom.ker f) :
    Finset (arcLocalRing f t ht) := by
  classical
  exact Finset.univ.image (dividedKernelFamily f t ht s hs)

theorem mem_dividedKernelFinset (f : C →+* R) (t : C) (ht : f t ≠ 0)
    (s : Finset C) (hs : Ideal.span (s : Set C) = RingHom.ker f) (i : s) :
    dividedKernelFamily f t ht s hs i ∈ dividedKernelFinset f t ht s hs := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The divided set generates the exact actual new arc kernel. -/
theorem span_dividedKernelFinset (f : C →+* R) (t : C) (ht : f t ≠ 0)
    (s : Finset C) (hs : Ideal.span (s : Set C) = RingHom.ker f) :
    KernelSpanEq (arcLocalMap f t ht) (dividedKernelFinset f t ht s hs) := by
  classical
  let z : s → RingHom.ker f := fun i => ⟨i, hs ▸ Ideal.subset_span i.property⟩
  have hz : Ideal.span (Set.range fun i => (z i : C)) = RingHom.ker f := by
    have he : Set.range (fun i : s => (i : C)) = (s : Set C) := by
      ext x
      exact ⟨fun ⟨i, hi⟩ => hi ▸ i.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    change Ideal.span (Set.range fun i : s => (i : C)) = RingHom.ker f
    rw [he]
    exact hs
  have hv : (dividedKernelFinset f t ht s hs : Set (arcLocalRing f t ht)) =
      Set.range (dividedKernelFamily f t ht s hs) := by
    ext x
    simp only [dividedKernelFinset, Finset.mem_coe, Finset.mem_image,
      Finset.mem_univ, true_and, Set.mem_range]
  refine kernelSpanEq_of_arcChart_localization f t ht
    (D := arcLocalRing f t ht) (arcClosedPoint f t ht).primeCompl
    (arcLocalMap f t ht) ?_ z hz (dividedKernelFinset f t ht s hs) ?_
  · ext x
    exact arcLocalMap_base f t ht x
  · refine hv.trans ?_
    apply congrArg Set.range
    funext i
    rfl

/-- The actual divided generating set has the original cardinality, by the
proved injectivity of division in the original domain. -/
theorem card_dividedKernelFinset [IsDomain C]
    (f : C →+* R) (t : C) (ht : f t ≠ 0)
    (s : Finset C) (hs : Ideal.span (s : Set C) = RingHom.ker f) :
    (dividedKernelFinset f t ht s hs).card = s.card := by
  classical
  have hinj : Function.Injective (dividedKernelFamily f t ht s hs) := by
    intro i j h
    apply Subtype.ext
    exact congrArg (fun x : RingHom.ker f => (x : C))
      (localArcFraction_injective f t ht h)
  simpa only [dividedKernelFinset, Finset.card_univ, Fintype.card_coe] using
    Finset.card_image_of_injective (Finset.univ : Finset s) hinj

end LocalFraction

/-- A literal normalized squared-kernel relation and its displayed positive
exponent: `n` in the torsion case, and `min n m` in the two-term case. -/
inductive ArcPowerRelation (f : C →+* R) (t z₁ z : C) : ℕ → Prop
  | torsion (n : ℕ) (hn : 0 < n) (hrel : t ^ n * z ∈ RingHom.ker f ^ 2) :
      ArcPowerRelation f t z₁ z n
  | mixed (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (a : Cˣ)
      (hrel : t ^ n * z - (a : C) * t ^ m * z₁ ∈ RingHom.ker f ^ 2) :
      ArcPowerRelation f t z₁ z (min n m)

omit [IsDomain R] in
theorem ArcPowerRelation.pos {f : C →+* R} {t z₁ z : C} {e : ℕ}
    (h : ArcPowerRelation f t z₁ z e) : 0 < e := by
  cases h with
  | torsion n hn _ => exact hn
  | mixed n m hn hm _ _ => exact lt_min hn hm

omit [IsDomain R] in
/-- Expose the literal equations without relying on an eliminated inductive
index inside a later actual-localization proof. -/
theorem ArcPowerRelation.cases_eq {f : C →+* R} {t z₁ z : C} {e : ℕ}
    (h : ArcPowerRelation f t z₁ z e) :
    (0 < e ∧ t ^ e * z ∈ RingHom.ker f ^ 2) ∨
      ∃ (n m : ℕ) (a : Cˣ), 0 < n ∧ 0 < m ∧
        t ^ n * z - (a : C) * t ^ m * z₁ ∈ RingHom.ker f ^ 2 ∧ e = min n m := by
  cases h with
  | torsion _ hn hrel => exact Or.inl ⟨hn, hrel⟩
  | mixed n m hn hm a hrel => exact Or.inr ⟨n, m, a, hn, hm, hrel, rfl⟩

/-- An exponent realized by an actual minimum-cardinality generating set,
with two distinct actual members and the original generic uniformizer. -/
def RealizesArcExponent (f : C →+* R) (t : C) (e : ℕ) : Prop :=
  ∃ (s : Finset C), KernelSpanEq f s ∧
    s.card = (RingHom.ker f).spanFinrank ∧
    ∃ z₁ ∈ s, ∃ z ∈ s, z ≠ z₁ ∧
      Irreducible (algebraMap C (Localization.AtPrime (RingHom.ker f)) z₁) ∧
      ArcPowerRelation f t z₁ z e

theorem RealizesArcExponent.pos {f : C →+* R} {t : C} {e : ℕ}
    (h : RealizesArcExponent f t e) : 0 < e := by
  obtain ⟨s, hs, hc, z₁, hz₁, z, hz, hne, huni, hrel⟩ := h
  exact hrel.pos

/-- Construct a realized torsion exponent over an abstract local ring. Its
positivity follows from the actual minimum generating data and Nakayama. -/
theorem realizesArcExponent_of_minimal_torsion [IsLocalRing C] [IsNoetherianRing C]
    (f : C →+* R) (t : C) (s : Finset C)
    (hs : KernelSpanEq f s)
    (hc : s.card = (RingHom.ker f).spanFinrank)
    (z₁ z : C) (hz₁ : z₁ ∈ s) (hz : z ∈ s) (hne : z ≠ z₁)
    (huni : Irreducible (algebraMap C (Localization.AtPrime (RingHom.ker f)) z₁))
    (n : ℕ) (hrel : t ^ n * z ∈ RingHom.ker f ^ 2) :
    RealizesArcExponent f t n := by
  have hs0 : Ideal.span (s : Set C) = RingHom.ker f := hs
  have hp := IsLocalRing.le_maximalIdeal (RingHom.ker_isPrime f).ne_top
  have hn := Ideal.pos_exponent_of_minimal_generators_torsion
    (RingHom.ker f) hp s hs0 hc z hz t n hrel
  exact ⟨s, hs, hc, z₁, hz₁, z, hz, hne, huni, ArcPowerRelation.torsion n hn hrel⟩

/-- Construct the realized exponent of an actual two-term relation over an
abstract local ring, deriving both positive exponents from minimality. -/
theorem realizesArcExponent_of_minimal_mixed [IsLocalRing C] [IsNoetherianRing C]
    (f : C →+* R) (t : C) (s : Finset C)
    (hs : KernelSpanEq f s)
    (hc : s.card = (RingHom.ker f).spanFinrank)
    (z₁ z : C) (hz₁ : z₁ ∈ s) (hz : z ∈ s) (hne : z ≠ z₁)
    (huni : Irreducible (algebraMap C (Localization.AtPrime (RingHom.ker f)) z₁))
    (n m : ℕ) (a : Cˣ)
    (hrel : t ^ n * z - (a : C) * t ^ m * z₁ ∈ RingHom.ker f ^ 2) :
    RealizesArcExponent f t (min n m) := by
  have hs0 : Ideal.span (s : Set C) = RingHom.ker f := hs
  have hp := IsLocalRing.le_maximalIdeal (RingHom.ker_isPrime f).ne_top
  obtain ⟨hn, hm⟩ := Ideal.pos_exponents_of_minimal_generators_relation
    (RingHom.ker f) hp s hs0 hc z₁ z hz₁ hz hne t a n m hrel
  exact ⟨s, hs, hc, z₁, hz₁, z, hz, hne, huni, ArcPowerRelation.mixed n m hn hm a hrel⟩

section LocalTorsion

variable [IsLocalRing R]

/-- Literal one-term division in the actual local ring, with the original
map and squared kernel fixed before the minimality argument. -/
theorem local_transformed_torsion_mem_ker_sq
    (f : C →+* R) (t : C) (ht : f t ≠ 0) (z : RingHom.ker f)
    (n : ℕ) (hn : 0 < n) (hrel : t ^ n * (z : C) ∈ RingHom.ker f ^ 2) :
    (arcLocalBase f t ht t) ^ (n - 1) * localArcFraction f t ht z ∈
      RingHom.ker (arcLocalMap f t ht) ^ 2 := by
  have hchart := transformed_torsion_relation_mem_ker_sq f t ht z n hn hrel
  have h := Ideal.mem_map_of_mem
    (algebraMap (arcChart f t) (arcLocalRing f t ht)) hchart
  rw [Ideal.map_pow, ← ker_arcLocalMap] at h
  simpa only [map_mul, map_pow, arcLocalBase, RingHom.comp_apply,
    localArcFraction] using h

end LocalTorsion

/-- The least exponent realized by the actual generating data and equations.
It is zero when there are no such data; unresolved arc states are proved below
to have a realized positive minimum. -/
def arcExponent (f : C →+* R) (t : C) : ℕ := sInf {e | RealizesArcExponent f t e}

theorem arcExponent_le {f : C →+* R} {t : C} {e : ℕ}
    (h : RealizesArcExponent f t e) : arcExponent f t ≤ e :=
  csInf_le (OrderBot.bddBelow _) h

theorem realizes_arcExponent {f : C →+* R} {t : C}
    (h : ∃ e, RealizesArcExponent f t e) : RealizesArcExponent f t (arcExponent f t) :=
  csInf_mem h

/-- The intrinsic lexicographic coordinates: the actual kernel generator
count and the least actual realized relation exponent. -/
def arcMeasure (f : C →+* R) (t : C) : ℕ × ℕ :=
  ((RingHom.ker f).spanFinrank, arcExponent f t)

/-- Equal-count descent over a fixed abstract localization of the actual
chart. The generating equation, its minimality, and the divided relations
are all produced and consumed with this same ring and quotient map. -/
theorem realizesArcExponent_step_of_arcChart_localization
    (f : C →+* R) (t : C) (ht : f t ≠ 0)
    {D : Type*} [cD : CommRing D] [localD : IsLocalRing D] [noethD : IsNoetherianRing D]
    [aD : Algebra (arcChart f t) D]
    (M : Submonoid (arcChart f t)) [IsLocalization M D]
    (H : D →+* R)
    (hcomp : H.comp (algebraMap (arcChart f t) D) = arcMap f t ht)
    (hdiv : Function.Injective fun z : RingHom.ker f =>
      algebraMap (arcChart f t) D (arcFraction f t z))
    (hgeneric : ∀ z : RingHom.ker f,
      Irreducible (algebraMap C (Localization.AtPrime (RingHom.ker f)) z) →
        Irreducible (algebraMap D (Localization.AtPrime (RingHom.ker H))
          (algebraMap (arcChart f t) D (arcFraction f t z))))
    (hcount : (RingHom.ker H).spanFinrank = (RingHom.ker f).spanFinrank)
    {e : ℕ} (he : RealizesArcExponent f t e) :
    ∃ e' < e, RealizesArcExponent H
      (algebraMap (arcChart f t) D (algebraMap C (arcChart f t) t)) e' := by
  classical
  let L : arcChart f t →+* D := algebraMap (arcChart f t) D
  let T : D := L (algebraMap C (arcChart f t) t)
  have hker : RingHom.ker H = (RingHom.ker (arcMap f t ht)).map L := by
    calc
      RingHom.ker H = ((RingHom.ker H).comap L).map L :=
        (IsLocalization.map_under M D (RingHom.ker H)).symm
      _ = _ := by rw [RingHom.comap_ker, hcomp]
  obtain ⟨s, hs, hcard, z₁, hz₁, z, hz, hne, huni, hpower⟩ := he
  have hs0 : Ideal.span (s : Set C) = RingHom.ker f := hs
  let zs : s → RingHom.ker f := fun i => ⟨i, hs0 ▸ Ideal.subset_span i.property⟩
  have hzs : Ideal.span (Set.range fun i => (zs i : C)) = RingHom.ker f := by
    have hset : Set.range (fun i : s => (i : C)) = (s : Set C) := by
      ext x
      exact ⟨fun ⟨i, hi⟩ => hi ▸ i.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    change Ideal.span (Set.range fun i : s => (i : C)) = RingHom.ker f
    rw [hset]
    exact hs0
  let w : s → D := fun i => L (arcFraction f t (zs i))
  let v : Finset D := Finset.univ.image w
  have hvset : (v : Set D) = Set.range w := by
    ext x
    simp only [v, Finset.mem_coe, Finset.mem_image, Finset.mem_univ,
      true_and, Set.mem_range]
  have hv : KernelSpanEq H v := by
    refine kernelSpanEq_of_arcChart_localization f t ht M H hcomp zs hzs v ?_
    refine hvset.trans ?_
    apply congrArg Set.range
    funext i
    rfl
  have hwinj : Function.Injective w := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun a : RingHom.ker f => (a : C)) (hdiv hij)
  have hvc : v.card = (RingHom.ker H).spanFinrank := by
    have hc : v.card = s.card := by
      simpa only [v, Finset.card_univ, Fintype.card_coe] using
        Finset.card_image_of_injective (Finset.univ : Finset s) hwinj
    exact hc.trans (hcard.trans hcount.symm)
  let i₁ : s := ⟨z₁, hz₁⟩
  let i : s := ⟨z, hz⟩
  have hw₁ : w i₁ ∈ v := Finset.mem_image.mpr ⟨i₁, Finset.mem_univ _, rfl⟩
  have hw : w i ∈ v := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hwne : w i ≠ w i₁ := by
    intro h
    exact hne (congrArg (fun j : s => (j : C)) (hwinj h))
  have hwuni : Irreducible (algebraMap D (Localization.AtPrime (RingHom.ker H)) (w i₁)) :=
    hgeneric (zs i₁) huni
  rcases hpower.cases_eq with ⟨hn, hraw⟩ | ⟨n, m, a, hn, hm, hraw, heq⟩
  · have hraw' : t ^ e * (zs i : C) ∈ RingHom.ker f ^ 2 := hraw
    have hnew0 := Ideal.mem_map_of_mem L
      (transformed_torsion_relation_mem_ker_sq f t ht (zs i) e hn hraw')
    rw [Ideal.map_pow, ← hker] at hnew0
    have hnew : T ^ (e - 1) * w i ∈ RingHom.ker H ^ 2 := by
      simpa only [map_mul, map_pow] using hnew0
    have he' : RealizesArcExponent H T (e - 1) :=
      realizesArcExponent_of_minimal_torsion H T v hv hvc
        (w i₁) (w i) hw₁ hw hwne hwuni (e - 1) hnew
    exact ⟨e - 1, Nat.sub_lt hn Nat.zero_lt_one, he'⟩
  · subst e
    let b : C →+* D := L.comp (algebraMap C (arcChart f t))
    let a' : Dˣ := Units.map b.toMonoidHom a
    have ha' : (a' : D) = L (algebraMap C (arcChart f t) (a : C)) := rfl
    have hraw' : t ^ n * (zs i : C) - (a : C) * t ^ m * (zs i₁ : C) ∈
        RingHom.ker f ^ 2 := hraw
    have hnew0 := Ideal.mem_map_of_mem L
      (transformed_relation_mem_ker_sq f t ht (zs i) (zs i₁) a n m hn hm hraw')
    rw [Ideal.map_pow, ← hker] at hnew0
    have hnew : T ^ (n - 1) * w i - (a' : D) * T ^ (m - 1) * w i₁ ∈
        RingHom.ker H ^ 2 := by
      rw [ha']
      simpa only [map_sub, map_mul, map_pow] using hnew0
    have he' : RealizesArcExponent H T (min (n - 1) (m - 1)) :=
      realizesArcExponent_of_minimal_mixed H T v hv hvc
        (w i₁) (w i) hw₁ hw hwne hwuni (n - 1) (m - 1) a' hnew
    have hlt : min (n - 1) (m - 1) < min n m := by omega
    exact ⟨min (n - 1) (m - 1), hlt, he'⟩

section StrictDescent

variable [IsLocalRing R] [IsNoetherianRing C] [IsDomain C]

omit [IsLocalRing R] in
/-- Existence of realized exponents is derived from the actual minimum
kernel generators and the surjection onto the original DVR. -/
theorem exists_realizesArcExponent [IsLocalRing C] [IsDiscreteValuationRing R]
    (f : C →+* R) (hf : Function.Surjective f) (t : C) (ht : Irreducible (f t))
    [IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker f))]
    (hc : 1 < (RingHom.ker f).spanFinrank) : ∃ e, RealizesArcExponent f t e := by
  obtain ⟨s, hcard, hs, hind, z₁, hz₁, huni⟩ :=
    exists_minimal_kernel_generators_generic_uniformizer f
  obtain ⟨z, hz, hne⟩ := Finset.exists_mem_ne (hcard.symm ▸ hc) z₁
  obtain ⟨n, hn, hrel | ⟨m, a, hm, hrel⟩⟩ :=
    exists_positive_relation_of_minimal_kernel_generators f hf t ht s hs hcard
      z₁ z hz₁ hz hne huni
  · exact ⟨n, s, hs, hcard, z₁, hz₁, z, hz, hne, huni,
      ArcPowerRelation.torsion n hn hrel⟩
  · exact ⟨min n m, s, hs, hcard, z₁, hz₁, z, hz, hne, huni,
      ArcPowerRelation.mixed n m hn hm a hrel⟩

/-- If the actual kernel count stays equal, every actual realized exponent
strictly decreases after the original closed-point arc blowup. Zero transformed
exponents contradict minimality, so their positivity is derived. -/
theorem realizesArcExponent_step_of_count_eq
    (f : C →+* R) (t : C) (ht : f t ≠ 0)
    (hcount : (RingHom.ker (arcLocalMap f t ht)).spanFinrank =
      (RingHom.ker f).spanFinrank) {e : ℕ} (he : RealizesArcExponent f t e) :
    ∃ e' < e, RealizesArcExponent (arcLocalMap f t ht) (arcLocalBase f t ht t) e' := by
  let D := arcLocalRing f t ht
  let cD : CommRing D := inferInstanceAs (CommRing (arcLocalRing f t ht))
  let localD : IsLocalRing D := inferInstanceAs (IsLocalRing (arcLocalRing f t ht))
  let noethD : IsNoetherianRing D := arcLocalRing_isNoetherian f t ht
  let aD : Algebra (arcChart f t) D :=
    inferInstanceAs (Algebra (arcChart f t) (arcLocalRing f t ht))
  let H : D →+* R := arcLocalMap f t ht
  have hcomp : H.comp (algebraMap (arcChart f t) D) = arcMap f t ht := by
    ext x
    exact arcLocalMap_base f t ht x
  have hdiv : Function.Injective fun z : RingHom.ker f =>
      algebraMap (arcChart f t) D (arcFraction f t z) := by
    intro z w h
    exact localArcFraction_injective f t ht h
  have hgeneric : ∀ z : RingHom.ker f,
      Irreducible (algebraMap C (Localization.AtPrime (RingHom.ker f)) z) →
        Irreducible (algebraMap D (Localization.AtPrime (RingHom.ker H))
          (algebraMap (arcChart f t) D (arcFraction f t z))) := by
    intro z hz
    exact irreducible_localArcFraction_generic f t ht z hz
  change ∃ e' < e, RealizesArcExponent H
    (algebraMap (arcChart f t) D (algebraMap C (arcChart f t) t)) e'
  exact realizesArcExponent_step_of_arcChart_localization f t ht
    (D := D) (cD := cD) (localD := localD) (noethD := noethD) (aD := aD)
    (arcClosedPoint f t ht).primeCompl H hcomp hdiv hgeneric hcount he

/-- A relation realizing exponent one forces an actual generator-count drop:
the putative equal-count successor would realize a positive exponent below one. -/
theorem spanFinrank_ker_arcLocalMap_lt_of_realizes_one
    (f : C →+* R) (t : C) (ht : f t ≠ 0) (he : RealizesArcExponent f t 1) :
    (RingHom.ker (arcLocalMap f t ht)).spanFinrank < (RingHom.ker f).spanFinrank := by
  have hle := spanFinrank_ker_arcLocalMap_le f t ht
  by_contra hnot
  have heq : (RingHom.ker (arcLocalMap f t ht)).spanFinrank =
      (RingHom.ker f).spanFinrank := Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  obtain ⟨e, he1, he⟩ := realizesArcExponent_step_of_count_eq f t ht heq he
  have he0 := he.pos
  omega

end StrictDescent

section DVRDescent

variable [IsNoetherianRing C] [IsDomain C]

/-- Every unresolved actual arc step strictly decreases the intrinsic
lexicographic measure. Both branches are proved for the constructed successor;
neither successor decrease nor generator deletion is an assumption. -/
theorem arcMeasure_step_lt [IsLocalRing C] [IsDiscreteValuationRing R]
    (f : C →+* R) (hf : Function.Surjective f) (t : C) (ht : Irreducible (f t))
    [IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker f))]
    (hc : 1 < (RingHom.ker f).spanFinrank) :
    Prod.Lex (· < ·) (· < ·)
      (arcMeasure (arcLocalMap f t ht.ne_zero) (arcLocalBase f t ht.ne_zero t))
      (arcMeasure f t) := by
  have hle := spanFinrank_ker_arcLocalMap_le f t ht.ne_zero
  by_cases hlt : (RingHom.ker (arcLocalMap f t ht.ne_zero)).spanFinrank <
      (RingHom.ker f).spanFinrank
  · exact Prod.Lex.left _ _ hlt
  · have heq : (RingHom.ker (arcLocalMap f t ht.ne_zero)).spanFinrank =
        (RingHom.ker f).spanFinrank := Nat.le_antisymm hle (Nat.le_of_not_gt hlt)
    have he := realizes_arcExponent (exists_realizesArcExponent f hf t ht hc)
    obtain ⟨e', he'lt, he'⟩ := realizesArcExponent_step_of_count_eq f t ht.ne_zero heq he
    have hstrict := lt_of_le_of_lt (arcExponent_le he') he'lt
    change Prod.Lex (· < ·) (· < ·)
      ((RingHom.ker (arcLocalMap f t ht.ne_zero)).spanFinrank,
        arcExponent (arcLocalMap f t ht.ne_zero) (arcLocalBase f t ht.ne_zero t))
      ((RingHom.ker f).spanFinrank, arcExponent f t)
    rw [heq]
    exact Prod.Lex.right _ hstrict

end DVRDescent

section PrincipalStopping

variable [IsDiscreteValuationRing R]

/-- A kernel with at most one generator gives regularity directly from the
actual regular DVR quotient. No dimension premise on a successor is needed. -/
theorem isRegularLocalRing_of_ker_spanFinrank_le_one
    [IsLocalRing C] [IsNoetherianRing C] [IsDomain C]
    (f : C →+* R) (hf : Function.Surjective f)
    (hc : (RingHom.ker f).spanFinrank ≤ 1) : IsRegularLocalRing C := by
  classical
  by_cases hp0 : RingHom.ker f = ⊥
  · let e := RingEquiv.ofBijective f ⟨(RingHom.injective_iff_ker_eq_bot f).mpr hp0, hf⟩
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · have hfg : Submodule.FG (RingHom.ker f : Submodule C C) := IsNoetherian.noetherian _
    have hc0 : (RingHom.ker f).spanFinrank ≠ 0 := fun h =>
      hp0 ((Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp h)
    have hc1 : (RingHom.ker f).spanFinrank = 1 := by omega
    obtain ⟨hprincipal, _⟩ := (Submodule.spanFinrank_eq_one_iff (RingHom.ker f)).mp hc1
    let := hprincipal
    obtain ⟨z, hz⟩ := Submodule.IsPrincipal.principal (RingHom.ker f : Submodule C C)
    change RingHom.ker f = Ideal.span {z} at hz
    have hz0 : z ≠ 0 := by
      intro h
      apply hp0
      simpa only [h, Ideal.span_singleton_zero] using hz
    let : IsRegularLocalRing (C ⧸ RingHom.ker f) :=
      IsRegularLocalRing.of_ringEquiv (f.quotientKerEquivOfSurjective hf).symm
    have hquot : IsRegularLocalRing (C ⧸ Ideal.span {z}) := by
      rw [← hz]
      infer_instance
    let := hquot
    apply IsRegularLocalRing.of_quotient_span_singleton C z
    exact IsSMulRegular.of_right_eq_zero_of_smul fun x hx =>
      (mul_eq_zero.mp (by simpa only [smul_eq_mul] using hx)).resolve_left hz0

end PrincipalStopping

section GenericDVRTransfer

variable [IsLocalRing R]

/-- Fix the actual kernel prime before elaborating its native localization. -/
local instance arcLocalMapKernelIsPrime (f : C →+* R) (t : C) (ht : f t ≠ 0) :
    (RingHom.ker (arcLocalMap f t ht)).IsPrime := RingHom.ker_isPrime _

/-- The literal generic localization uses the same exposed native ring
presentation as the proved generic comparison. -/
local instance arcLocalMapKernelCommRing (f : C →+* R) (t : C) (ht : f t ≠ 0) :
    CommRing (Localization.AtPrime (RingHom.ker (arcLocalMap f t ht))) :=
  arcGenericLocalRingCommRing f t ht

/-- Domainness of the literal generic localization is supplied by the actual
comparison, before its DVR proposition is elaborated. -/
local instance arcLocalMapKernelIsDomain [IsDomain C]
    (f : C →+* R) (t : C) (ht : f t ≠ 0) :
    IsDomain (Localization.AtPrime (RingHom.ker (arcLocalMap f t ht))) :=
  arcGenericLocalRing_isDomain f t ht

/-- The named actual generic local ring is the literal native localization,
with its original ring operations and coefficient map. -/
def arcGenericNativeEquiv (f : C →+* R) (t : C) (ht : f t ≠ 0) :
    arcGenericLocalRing f t ht ≃+*
      Localization.AtPrime (RingHom.ker (arcLocalMap f t ht)) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The proved generic DVR is also a DVR in the literal native localization
used by the actual next quotient map. Both domain structures are derived. -/
theorem arcLocalMap_generic_isDiscreteValuationRing [IsDomain C]
    (f : C →+* R) (t : C) (ht : f t ≠ 0)
    [IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker f))] :
    IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker (arcLocalMap f t ht))) := by
  let : IsDomain (arcGenericLocalRing f t ht) := arcGenericLocalRing_isDomain f t ht
  let : IsDiscreteValuationRing (arcGenericLocalRing f t ht) :=
    arcGenericLocalRing_isDiscreteValuationRing f t ht
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (arcGenericNativeEquiv f t ht)

end GenericDVRTransfer

/-- A local arc state records only the actual hypotheses preserved by the
constructed closed-point successor. Every quotient map has the same target `R`. -/
structure LocalArcState (R : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] where
  /-- The actual Noetherian local domain at this stage of the arc iteration. -/
  Ring : Type u
  [commRing : CommRing Ring]
  [localRing : IsLocalRing Ring]
  [noetherian : IsNoetherianRing Ring]
  [domain : IsDomain Ring]
  /-- The actual quotient map from this local ring to the same original DVR `R`. -/
  quotient : Ring →+* R
  surjective : Function.Surjective quotient
  /-- The chosen lift in this ring of a uniformizer of the original DVR `R`. -/
  parameter : Ring
  uniformizer : Irreducible (quotient parameter)
  [genericDVR : IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker quotient))]

attribute [instance] LocalArcState.commRing LocalArcState.localRing
  LocalArcState.noetherian LocalArcState.domain LocalArcState.genericDVR

namespace LocalArcState

variable [IsDiscreteValuationRing R]

/-- The successor is the original saturated chart localized at the closed
point selected by this same quotient map. Its hypotheses are all derived. -/
def next (S : LocalArcState R) : LocalArcState R where
  Ring := arcLocalRing S.quotient S.parameter S.uniformizer.ne_zero
  commRing := inferInstance
  localRing := inferInstance
  noetherian := arcLocalRing_isNoetherian S.quotient S.parameter S.uniformizer.ne_zero
  domain := arcLocalRing_isDomain S.quotient S.parameter S.uniformizer.ne_zero
  quotient := arcLocalMap S.quotient S.parameter S.uniformizer.ne_zero
  surjective := arcLocalMap_surjective S.quotient S.parameter S.uniformizer.ne_zero S.surjective
  parameter := arcLocalBase S.quotient S.parameter S.uniformizer.ne_zero S.parameter
  uniformizer := by
    rw [arcLocalMap_arcLocalBase]
    exact S.uniformizer
  genericDVR := arcLocalMap_generic_isDiscreteValuationRing
    S.quotient S.parameter S.uniformizer.ne_zero

/-- The scalar map for this actual step, before any iteration. -/
def transition (S : LocalArcState R) : S.Ring →+* S.next.Ring :=
  arcLocalBase S.quotient S.parameter S.uniformizer.ne_zero

@[simp]
theorem quotient_transition (S : LocalArcState R) (x : S.Ring) :
    S.next.quotient (S.transition x) = S.quotient x :=
  arcLocalMap_arcLocalBase S.quotient S.parameter S.uniformizer.ne_zero x

/-- The exact intrinsic coordinates of this actual ring, quotient and parameter. -/
def measure (S : LocalArcState R) : ℕ × ℕ := arcMeasure S.quotient S.parameter

theorem measure_next_lt (S : LocalArcState R)
    (hc : 1 < (RingHom.ker S.quotient).spanFinrank) :
    Prod.Lex (· < ·) (· < ·) S.next.measure S.measure :=
  arcMeasure_step_lt S.quotient S.surjective S.parameter S.uniformizer hc

/-- Iteration uses the constructed actual successor at every stage. -/
def iterate (S : LocalArcState R) : ℕ → LocalArcState R
  | 0 => S
  | n + 1 => (S.iterate n).next

@[simp]
theorem iterate_zero (S : LocalArcState R) : S.iterate 0 = S := rfl

@[simp]
theorem iterate_succ (S : LocalArcState R) (n : ℕ) :
    S.iterate (n + 1) = (S.iterate n).next := rfl

/-- Starting after the first actual step gives the tail of this same iteration. -/
theorem iterate_next (S : LocalArcState R) (n : ℕ) :
    S.next.iterate n = S.iterate (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg next ih

/-- The composite of the actual scalar maps from the original ring. -/
def iterateMap (S : LocalArcState R) : (n : ℕ) → S.Ring →+* (S.iterate n).Ring
  | 0 => RingHom.id S.Ring
  | n + 1 => (S.iterate n).transition.comp (S.iterateMap n)

/-- Every iterated quotient remains the same original quotient after the
constructed scalar map. -/
theorem quotient_comp_iterateMap (S : LocalArcState R) (n : ℕ) :
    (S.iterate n).quotient.comp (S.iterateMap n) = S.quotient := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    change (S.iterate n).next.quotient
      ((S.iterate n).transition (S.iterateMap n x)) = S.quotient x
    rw [quotient_transition]
    exact RingHom.congr_fun ih x

/-- Every parameter is the image of the original lifted uniformizer under
these same actual scalar maps. -/
theorem iterateMap_parameter (S : LocalArcState R) (n : ℕ) :
    S.iterateMap n S.parameter = (S.iterate n).parameter := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (S.iterate n).transition (S.iterateMap n S.parameter) =
      (S.iterate n).next.parameter
    rw [ih]
    rfl

/-- A finite actual iterate is regular. Well-founded induction uses the
proved strict decrease and the actual quotient stopping argument. -/
theorem exists_regular_iterate (S : LocalArcState R) :
    ∃ n : ℕ, IsRegularLocalRing (S.iterate n).Ring := by
  let wf : WellFounded (fun S T : LocalArcState R =>
      Prod.Lex (· < ·) (· < ·) S.measure T.measure) :=
    InvImage.wf measure (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  refine wf.induction (C := fun T => ∃ n : ℕ, IsRegularLocalRing (T.iterate n).Ring) S ?_
  intro S ih
  by_cases hc : 1 < (RingHom.ker S.quotient).spanFinrank
  · obtain ⟨n, hn⟩ := ih S.next (measure_next_lt S hc)
    refine ⟨n + 1, ?_⟩
    exact Eq.mp (congrArg
      (fun U : LocalArcState R => IsRegularLocalRing U.Ring) (iterate_next S n)) hn
  · exact ⟨0, isRegularLocalRing_of_ker_spanFinrank_le_one S.quotient S.surjective
      (Nat.le_of_not_gt hc)⟩

end LocalArcState

section SurfaceInput

variable [IsLocalRing C] [IsNoetherianRing C] [IsDomain C] [IsDiscreteValuationRing R]

/-- The actual kernel of the surface surjection has height one. The quotient
is the same original DVR throughout. -/
theorem height_ker_eq_one_of_surface_surjective
    (f : C →+* R) (hf : Function.Surjective f) (t : C) (ht : Irreducible (f t))
    (hd : ringKrullDim C = 2) : (RingHom.ker f).height = 1 := by
  have hp0 : RingHom.ker f ≠ ⊥ := by
    intro hp0
    let e := RingEquiv.ofBijective f ⟨(RingHom.injective_iff_ker_eq_bot f).mpr hp0, hf⟩
    have he : ringKrullDim C = 1 :=
      (ringKrullDim_eq_of_ringEquiv e).trans (IsDiscreteValuationRing.ringKrullDim_eq_one R)
    rw [hd] at he
    norm_num at he
  have htmem : t ∈ IsLocalRing.maximalIdeal C := fun hu => ht.not_isUnit (hu.map f)
  have hpm : RingHom.ker f ≠ IsLocalRing.maximalIdeal C := by
    intro h
    exact ht.ne_zero (RingHom.mem_ker.mp (h.symm ▸ htmem))
  have hlt : RingHom.ker f < IsLocalRing.maximalIdeal C :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (RingHom.ker_isPrime f).ne_top) hpm
  have hheight := Ideal.height_strict_mono_of_isPrime hlt
  have hmaxheight : (IsLocalRing.maximalIdeal C).height = 2 := by
    apply WithBot.coe_injective
    exact (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := C)).trans hd
  rw [hmaxheight] at hheight
  have hle : (RingHom.ker f).height ≤ 1 := ENat.lt_two_iff.mp hheight
  have hge : 1 ≤ (RingHom.ker f).height := Order.one_le_iff_ne_zero.mpr
    (fun h => hp0 (Ideal.height_eq_zero_iff_eq_bot.mp h))
  exact le_antisymm hle hge

/-- The original regular generic local ring is a DVR, by the actual
height-one calculation on the given two-dimensional local source. -/
theorem generic_isDiscreteValuationRing_of_regular_surface
    (f : C →+* R) (hf : Function.Surjective f) (t : C) (ht : Irreducible (f t))
    (hd : ringKrullDim C = 2)
    [IsRegularLocalRing (Localization.AtPrime (RingHom.ker f))] :
    IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker f)) := by
  have hdim : ringKrullDim (Localization.AtPrime (RingHom.ker f)) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (RingHom.ker f)
      (Localization.AtPrime (RingHom.ker f)),
      height_ker_eq_one_of_surface_surjective f hf t ht hd]
    rfl
  have hspan : (IsLocalRing.maximalIdeal
      (Localization.AtPrime (RingHom.ker f))).spanFinrank = 1 := by
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal.trans hdim
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact hspan

/-- The actual original surface data supply the first state. Regularity at
its kernel supplies the generic DVR, rather than being replaced by an input
on a different arc or a successor. -/
def LocalArcState.ofRegularGenericSurface
    (f : C →+* R) (hf : Function.Surjective f) (t : C) (ht : Irreducible (f t))
    (hd : ringKrullDim C = 2)
    [IsRegularLocalRing (Localization.AtPrime (RingHom.ker f))] : LocalArcState R := by
  let : IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker f)) :=
    generic_isDiscreteValuationRing_of_regular_surface f hf t ht hd
  exact {
    Ring := C
    commRing := inferInstance
    localRing := inferInstance
    noetherian := inferInstance
    domain := inferInstance
    quotient := f
    surjective := hf
    parameter := t
    uniformizer := ht
    genericDVR := inferInstance }

/-- Starting from the given two-dimensional local source and its original
surjection, a finite iterate of the actual local arc charts is regular. The
successor at every stage remains `arcLocalRing` with its original quotient. -/
theorem exists_regular_iterate_of_regular_surface
    (f : C →+* R) (hf : Function.Surjective f) (t : C) (ht : Irreducible (f t))
    (hd : ringKrullDim C = 2)
    [IsRegularLocalRing (Localization.AtPrime (RingHom.ker f))] :
    ∃ n : ℕ, IsRegularLocalRing
      ((LocalArcState.ofRegularGenericSurface f hf t ht hd).iterate n).Ring :=
  LocalArcState.exists_regular_iterate _

end SurfaceInput

end Localization.Away
