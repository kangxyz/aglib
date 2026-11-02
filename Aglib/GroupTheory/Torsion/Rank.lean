/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.Torsion.Detectors
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness

/-!
# Finite rank from the cardinalities of the actual torsion subgroups

The prime-power argument lifts generators of the quotient by prime multiples.
Coprime levels are assembled by the actual multiplication maps and CRT.
-/

@[expose] public noncomputable section

namespace AddSubgroup.TorsionBy

variable (T : Type*) [AddCommGroup T]

/-- Taking a divisor-level torsion subgroup inside a torsion level preserves
the original elements. -/
def nestedLevelEquiv (d n : ℕ) (hdn : d ∣ n) :
    AddSubgroup.torsionBy (AddSubgroup.torsionBy T (n : ℤ)) (d : ℤ) ≃+
      AddSubgroup.torsionBy T (d : ℤ) where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    obtain ⟨k, rfl⟩ := hdn
    rw [mul_nsmul,
      AddSubgroup.torsionBy.nsmul_iff.mp x.property, nsmul_zero]⟩,
    Subtype.ext x.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl

/-- The quotient by the image of a finite-group endomorphism has the same
cardinality as its kernel. -/
theorem card_quotient_range_eq_card_ker [Finite T] (f : T →+ T) :
    Nat.card (T ⧸ f.range) = Nat.card f.ker := by
  have hker := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have hran := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.range
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv] at hker
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.range))
    (hran.symm.trans (hker.trans (Nat.mul_comm _ _)))

/-- Lifting generators modulo prime multiples works whenever a power of the
same scalar annihilates the target. This elementary argument needs no
finiteness or local-ring instance. -/
theorem surjective_of_lifts_mod_nsmul {A : Type*} [AddCommGroup A]
    (f : A →+ T) (p r : ℕ) (hkilled : ∀ x : T, p ^ r • x = 0)
    (hlift : ∀ x : T, ∃ a y, x = f a + p • y) : Function.Surjective f := by
  have hiter (k : ℕ) (x : T) : ∃ a y, x = f a + p ^ k • y := by
    induction k with
    | zero => exact ⟨0, x, by simp⟩
    | succ k ih =>
      obtain ⟨a, y, hy⟩ := ih
      obtain ⟨b, z, hz⟩ := hlift y
      refine ⟨a + p ^ k • b, z, ?_⟩
      rw [hy, hz, map_add, map_nsmul, smul_add, pow_succ, mul_smul]
      exact (add_assoc _ _ _).symm
  intro x
  obtain ⟨a, y, h⟩ := hiter r x
  exact ⟨a, by simpa only [hkilled, add_zero] using h.symm⟩

/-- A finite elementary abelian prime group of power cardinality has a basis
indexed by `Fin rank`. -/
def primeBasisOfCardPow (rank : ℕ) {p : ℕ} [Fact p.Prime] [Module (ZMod p) T] [Finite T]
    (hcard : Nat.card T = p ^ rank) : Module.Basis (Fin rank) (ZMod p) T := by
  have hdim : Module.finrank (ZMod p) T = rank := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := T)
    rw [Nat.card_zmod, hcard] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  exact Module.finBasisOfFinrankEq (ZMod p) T hdim

/-- A finite group annihilated by `p^r`, with the two expected cardinalities,
is a free rank-`rank` module over `ZMod (p^r)`. -/
theorem nonempty_equiv_primePow_of_card_pow (rank : ℕ) {p r : ℕ} (hp : p.Prime)
    [Module (ZMod (p ^ r)) T] [Finite T]
    (hcard : Nat.card T = (p ^ r) ^ rank)
    (hprime : Nat.card (AddSubgroup.torsionBy T (p : ℤ)) = p ^ rank) :
    Nonempty (T ≃+ (Fin rank → ZMod (p ^ r))) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  let f : T →+ T := nsmulAddMonoidHom p
  let Q := T ⧸ f.range
  let q : T →+ Q := QuotientAddGroup.mk' f.range
  let instQ : Module (ZMod p) Q := QuotientAddGroup.zmodModule (n := p)
    (fun x => show p • x ∈ f.range from ⟨x, rfl⟩)
  have hQ : Nat.card Q = p ^ rank := by
    rw [card_quotient_range_eq_card_ker]
    simpa only [AddSubgroup.torsionBy_natCast_eq_ker] using hprime
  let b : Module.Basis (Fin rank) (ZMod p) Q := primeBasisOfCardPow Q rank (p := p) hQ
  let bv : Fin rank → Q := fun i => b.repr.symm.toFun (Finsupp.single i 1)
  choose v hv using fun i : Fin rank => QuotientAddGroup.mk'_surjective f.range (bv i)
  let L : (Fin rank → ZMod (p ^ r)) →ₗ[ZMod (p ^ r)] T :=
    Fintype.linearCombination (ZMod (p ^ r)) v
  have hL : Function.Surjective L := by
    apply surjective_of_lifts_mod_nsmul T L.toAddMonoidHom p r
      (ZModModule.char_nsmul_eq_zero (p ^ r))
    intro x
    let c : Fin rank → ZMod p := b.equivFun.toFun (q x)
    let a : Fin rank → ZMod (p ^ r) := fun i => (c i).val
    have hq : q (L a) = q x := by
      change q (∑ i, a i • v i) = q x
      rw [map_sum]
      have hterm (i : Fin rank) : q (a i • v i) = c i • bv i := by
        change q (((c i).val : ZMod (p ^ r)) • v i) = c i • bv i
        rw [Nat.cast_smul_eq_nsmul, map_nsmul, hv]
        rw [← Nat.cast_smul_eq_nsmul (R := ZMod p), ZMod.natCast_zmod_val]
      simp_rw [hterm]
      exact b.sum_equivFun (q x)
    have hmem : x - L a ∈ f.range := by
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change q (x - L a) = 0
      rw [map_sub, hq, sub_self]
    obtain ⟨y, hy⟩ := hmem
    refine ⟨a, y, ?_⟩
    change x = L a + p • y
    simpa only [f, nsmulAddMonoidHom_apply, add_comm] using (eq_add_of_sub_eq hy.symm)
  have hbij : Function.Bijective L :=
    (Nat.bijective_iff_surjective_and_card L).mpr ⟨hL, by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin, hcard]⟩
  exact ⟨(LinearEquiv.ofBijective L hbij).symm.toAddEquiv⟩

/-- Coprime coordinates are assembled from the existing multiplication maps
on actual torsion subgroups. -/
theorem nonempty_torsionEquiv_coprime_of_card_pow (rank d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hde : d.Coprime e)
    (ed : AddSubgroup.torsionBy T (d : ℤ) ≃+ (Fin rank → ZMod d))
    (ee : AddSubgroup.torsionBy T (e : ℤ) ≃+ (Fin rank → ZMod e))
    (hcard : Nat.card (AddSubgroup.torsionBy T ((d * e : ℕ) : ℤ)) = (d * e) ^ rank) :
    Nonempty (AddSubgroup.torsionBy T ((d * e : ℕ) : ℤ) ≃+
      (Fin rank → ZMod (d * e))) := by
  classical
  let : NeZero (d * e) := ⟨(Nat.mul_pos hd he).ne'⟩
  let D := ed.toAddMonoidHom.comp (coprimeTorsionLeft T d e)
  let E := ee.toAddMonoidHom.comp (coprimeTorsionRight T d e)
  let C : AddSubgroup.torsionBy T ((d * e : ℕ) : ℤ) →+
      (Fin rank → ZMod (d * e)) := AddMonoidHom.pi fun i =>
    (ZMod.chineseRemainder hde).symm.toAddMonoidHom.comp
      (((Pi.evalAddMonoidHom (fun _ : Fin rank => ZMod d) i).comp D).prod
        ((Pi.evalAddMonoidHom (fun _ : Fin rank => ZMod e) i).comp E))
  have hinj : Function.Injective C := by
    intro x y hxy
    have hc (i : Fin rank) :
        (ed (coprimeTorsionLeft T d e x) i, ee (coprimeTorsionRight T d e x) i) =
          (ed (coprimeTorsionLeft T d e y) i, ee (coprimeTorsionRight T d e y) i) := by
      have h := congrArg (ZMod.chineseRemainder hde) (congrFun hxy i)
      exact (ZMod.chineseRemainder hde).apply_symm_apply _ |>.symm.trans
        (h.trans ((ZMod.chineseRemainder hde).apply_symm_apply _))
    apply coprimeTorsion_jointly_injective T d e hde
    · exact ed.injective (funext (fun i => congrArg Prod.fst (hc i)))
    · exact ee.injective (funext (fun i => congrArg Prod.snd (hc i)))
  exact ⟨AddEquiv.ofBijective C
    ((Nat.bijective_iff_injective_and_card C).mpr ⟨hinj, by
      rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod, hcard]⟩)⟩

/-- The divisor-level cardinalities characterize finite rank at every positive
level, including the zero coefficient ring at level one. -/
theorem nonempty_torsionEquiv_of_card_pow (rank n : ℕ) (hn : 0 < n)
    (hcard : ∀ d : ℕ, d ∣ n →
      Nat.card (AddSubgroup.torsionBy T (d : ℤ)) = d ^ rank) :
    Nonempty (AddSubgroup.torsionBy T (n : ℤ) ≃+ (Fin rank → ZMod n)) := by
  refine Nat.recOnPosPrimePosCoprime
    (motive := fun n : ℕ => 0 < n →
      (∀ d : ℕ, d ∣ n → Nat.card (AddSubgroup.torsionBy T (d : ℤ)) = d ^ rank) →
      Nonempty (AddSubgroup.torsionBy T (n : ℤ) ≃+ (Fin rank → ZMod n)))
    ?_ ?_ ?_ ?_ n hn hcard
  · intro p r hp hr hpos hc
    let M := AddSubgroup.torsionBy T ((p ^ r : ℕ) : ℤ)
    let : Module (ZMod (p ^ r)) M := AddCommGroup.zmodModule
      (fun x => Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp x.property))
    let : Finite M := Nat.finite_of_card_ne_zero (by
      rw [hc _ (dvd_refl _)]
      exact (pow_pos hpos rank).ne')
    apply nonempty_equiv_primePow_of_card_pow M rank hp (hc _ (dvd_refl _))
    have hdiv : p ∣ p ^ r := dvd_pow_self p hr.ne'
    exact (Nat.card_congr (nestedLevelEquiv T p (p ^ r) hdiv).toEquiv).trans
      (hc p hdiv)
  · intro h
    exact (Nat.not_lt_zero _ h).elim
  · intro _ _
    let : Subsingleton (AddSubgroup.torsionBy T (1 : ℤ)) := ⟨fun x y => by
      apply Subtype.ext
      have hx := AddSubgroup.torsionBy.nsmul_iff.mp x.property
      have hy := AddSubgroup.torsionBy.nsmul_iff.mp y.property
      simpa only [one_nsmul] using hx.trans hy.symm⟩
    let : Unique (AddSubgroup.torsionBy T (1 : ℤ)) :=
      ⟨⟨0⟩, fun x => Subsingleton.elim x 0⟩
    exact ⟨AddEquiv.ofUnique⟩
  · intro d e hd he hde ihd ihe _ hc
    obtain ⟨ed⟩ := ihd (Nat.zero_lt_of_lt hd)
      (fun q hq => hc q (hq.trans (dvd_mul_right d e)))
    obtain ⟨ee⟩ := ihe (Nat.zero_lt_of_lt he)
      (fun q hq => hc q (hq.trans (dvd_mul_left e d)))
    exact nonempty_torsionEquiv_coprime_of_card_pow T rank d e (Nat.zero_lt_of_lt hd)
      (Nat.zero_lt_of_lt he) hde ed ee (hc _ (dvd_refl _))

/-- An additive coordinate equivalence gives a basis for the original
`ZMod n` module structure, because every additive homomorphism is linear. -/
def basisOfEquivRank (rank : ℕ) {M : Type*} [AddCommGroup M] (n : ℕ) [Module (ZMod n) M]
    (e : M ≃+ (Fin rank → ZMod n)) : Module.Basis (Fin rank) (ZMod n) M :=
  (Pi.basisFun (ZMod n) (Fin rank)).map
    (LinearEquiv.ofBijective (e.symm.toAddMonoidHom.toZModLinearMap n) e.symm.bijective)

end AddSubgroup.TorsionBy
