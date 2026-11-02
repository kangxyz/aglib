/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.Torsion.Rank

/-! # Rank-two specializations of the general torsion cardinality criterion -/

@[expose] public noncomputable section

namespace AddSubgroup.TorsionBy

variable (T : Type*) [AddCommGroup T]

/-- The rank-two specialization of the native prime-power cardinality basis. -/
def primeBasis {p : ℕ} [Fact p.Prime] [Module (ZMod p) T] [Finite T]
    (hcard : Nat.card T = p * p) : Module.Basis (Fin 2) (ZMod p) T :=
  primeBasisOfCardPow T 2 (by simpa only [pow_two] using hcard)

/-- The rank-two specialization at a prime-power coefficient level. -/
theorem nonempty_equiv_primePow {p r : ℕ} (hp : p.Prime)
    [Module (ZMod (p ^ r)) T] [Finite T]
    (hcard : Nat.card T = p ^ r * p ^ r)
    (hprime : Nat.card (AddSubgroup.torsionBy T (p : ℤ)) = p * p) :
    Nonempty (T ≃+ (Fin 2 → ZMod (p ^ r))) :=
  nonempty_equiv_primePow_of_card_pow T 2 hp
    (by simpa only [pow_two] using hcard) (by simpa only [pow_two] using hprime)

/-- The rank-two coprime assembly through the same actual torsion maps. -/
theorem nonempty_torsionEquiv_coprime (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hde : d.Coprime e)
    (ed : AddSubgroup.torsionBy T (d : ℤ) ≃+ (Fin 2 → ZMod d))
    (ee : AddSubgroup.torsionBy T (e : ℤ) ≃+ (Fin 2 → ZMod e))
    (hcard : Nat.card (AddSubgroup.torsionBy T ((d * e : ℕ) : ℤ)) = (d * e) * (d * e)) :
    Nonempty (AddSubgroup.torsionBy T ((d * e : ℕ) : ℤ) ≃+
      (Fin 2 → ZMod (d * e))) :=
  nonempty_torsionEquiv_coprime_of_card_pow T 2 d e hd he hde ed ee
    (by simpa only [pow_two] using hcard)

/-- The rank-two specialization of the divisor-cardinality criterion. -/
theorem nonempty_torsionEquiv_of_card (n : ℕ) (hn : 0 < n)
    (hcard : ∀ d : ℕ, d ∣ n →
      Nat.card (AddSubgroup.torsionBy T (d : ℤ)) = d * d) :
    Nonempty (AddSubgroup.torsionBy T (n : ℤ) ≃+ (Fin 2 → ZMod n)) :=
  nonempty_torsionEquiv_of_card_pow T 2 n hn (fun d hd => by simpa only [pow_two] using hcard d hd)

/-- The rank-two basis on the original scalar action. -/
def basisOfEquiv {M : Type*} [AddCommGroup M] (n : ℕ) [Module (ZMod n) M]
    (e : M ≃+ (Fin 2 → ZMod n)) : Module.Basis (Fin 2) (ZMod n) M :=
  basisOfEquivRank 2 n e

end AddSubgroup.TorsionBy
