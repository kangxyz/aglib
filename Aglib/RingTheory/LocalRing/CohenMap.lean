/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalRing.CohenRing
public import Aglib.RingTheory.Smooth.AdicLift
public import Aglib.RingTheory.Smooth.Field
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The actual Cohen coefficient map into a complete local domain

The constructed arbitrary-residue Cohen DVR maps into the original
complete mixed-characteristic local domain. The map has the specified
residue point, is local, and is injective. Formal smoothness of the
actual integer quotient map is proved from its finite prime-field base.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsDiscreteValuationRing

private theorem formallySmooth_primeQuotient
    (C : Type*) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : C)) :
    (Ideal.quotientMap ((Ideal.span {(p : ℤ)}).map (algebraMap ℤ C))
      (algebraMap ℤ C) Ideal.le_comap_map).FormallySmooth := by
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  let J : Ideal C := I.map (algebraMap ℤ C)
  let : I.IsMaximal := Ideal.Quotient.maximal_of_isField I
    ((Int.quotientSpanNatEquivZMod p).isField (Field.toIsField (ZMod p)))
  let : Field (ℤ ⧸ I) := Ideal.Quotient.field I
  let : Finite (ℤ ⧸ I) :=
    Finite.of_equiv (ZMod p) (Int.quotientSpanNatEquivZMod p).symm.toEquiv
  have hJ : J = maximalIdeal C := by
    dsimp only [J, I]
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact hp.maximalIdeal_eq.symm
  let : J.IsMaximal := by rw [hJ]; infer_instance
  let : Field (C ⧸ J) := Ideal.Quotient.field J
  let : Algebra.FormallySmooth (ℤ ⧸ I) (C ⧸ J) :=
    Algebra.FormallySmooth.field_of_perfectField (F := ℤ ⧸ I) (K := C ⧸ J)
  change (algebraMap (ℤ ⧸ I) (C ⧸ J)).FormallySmooth
  exact RingHom.formallySmooth_algebraMap.mpr inferInstance

private theorem exists_lift_cohenPoint
    (C A : Type*) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [CharZero C]
    [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : C))
    (hpA : (p : A) ∈ maximalIdeal A) (g : C →+* ResidueField A) :
    ∃ f : C →+* A, (residue A).comp f = g := by
  let : Module.Flat ℤ C := inferInstance
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hIA : I.map (algebraMap ℤ A) ≤ maximalIdeal A := by
    change (Ideal.span {(p : ℤ)}).map (algebraMap ℤ A) ≤ maximalIdeal A
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact (Ideal.span_singleton_le_iff_mem (maximalIdeal A)).mpr hpA
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete_of_quotient
    I hIA (formallySmooth_primeQuotient C p hp) g.toIntAlgHom
  refine ⟨f.toRingHom, ?_⟩
  ext c
  exact AlgHom.congr_fun hf c

universe u

/-- A complete mixed-characteristic local domain admits an actual
injective local map from a constructed complete Cohen DVR, with
surjective original residue composite. The residue field is arbitrary. -/
theorem exists_complete_cohenMap
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [CharZero A]
    [IsAdicComplete (maximalIdeal A) A] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField A) p] :
    ∃ (C : CommRingCat.{u}) (hD : IsDomain C),
      let _ : IsDomain C := hD
      ∃ hV : IsDiscreteValuationRing C,
        let _ : IsDiscreteValuationRing C := hV
        CharZero C ∧ IsAdicComplete (maximalIdeal C) C ∧ Irreducible (p : C) ∧
          ∃ f : C →+* A, Function.Injective f ∧ IsLocalHom f ∧
            Function.Surjective ((residue A).comp f) := by
  obtain ⟨C, hD, hV, hchar, hcomplete, hp, g, hg, hker⟩ :=
    exists_complete_residuePoint p (ResidueField A)
  let : IsDomain C := hD
  let : IsDiscreteValuationRing C := hV
  let : CharZero C := hchar
  have hpA : (p : A) ∈ maximalIdeal A := by
    apply (residue_eq_zero_iff _).mp
    rw [map_natCast]
    exact CharP.cast_eq_zero (ResidueField A) p
  obtain ⟨f, hf⟩ := exists_lift_cohenPoint C A p hp hpA g
  have hlocal : IsLocalHom f := by
    constructor
    intro c hc
    by_contra hn
    have hzero : g c = 0 := hker.symm.le hn
    have hfzero : residue A (f c) = 0 := (RingHom.congr_fun hf c).trans hzero
    exact ((residue_eq_zero_iff _).mp hfzero) hc
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro c hc
    by_contra hn
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hp
    rw [map_mul, map_pow, map_natCast] at hc
    have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    exact (mul_ne_zero (u.isUnit.map f).ne_zero (pow_ne_zero n hp0)) hc
  exact ⟨C, hD, hV, hchar, hcomplete, hp, f, hinj, hlocal, hf.symm ▸ hg⟩

end IsDiscreteValuationRing
