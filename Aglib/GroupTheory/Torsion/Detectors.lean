/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.Torsion.Finite
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Int.GCD
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Prod

/-!
# Coprime and prime-power assembly of torsion detectors

All detector maps and their injectivity inputs remain explicit.

Source: `R5Lab.Aglib.GroupTheory.Torsion.Detectors`.
Packet SHA-256:
`4bced9aa8589663b3ef3ae270c5d479b4f362e1e2e011429cab404df785c41a3`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
open AddSubgroup
namespace AddSubgroup.TorsionBy
section TorsionTransport
variable (A : Type*) [AddCommGroup A]

/-- A positive finite level in the torsion subgroup is exactly the same level
in its original ambient group. Both directions preserve the actual element. -/
def levelInTorsionEquiv (U : ℕ) (hU : 0 < U) :
    torsionBy (AddCommGroup.torsion A) U ≃+ torsionBy A U where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨U, hU, torsionBy.nsmul_iff.mp x.property⟩⟩, Subtype.ext x.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The canonical inclusion into a level which has been proved to annihilate
an entire group. The map retains exactly the original element. -/
def killedLevelMap (U : ℕ) (killed : ∀ x : A, U • x = 0) :
    A →+ torsionBy A U where
  toFun x := ⟨x, torsionBy.nsmul_iff.mpr (killed x)⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem killedLevelMap_injective (U : ℕ) (killed : ∀ x : A, U • x = 0) :
    Function.Injective (killedLevelMap A U killed) :=
  fun _ _ h => congrArg Subtype.val h

end TorsionTransport
end AddSubgroup.TorsionBy
namespace AddSubgroup.TorsionBy

open AddSubgroup

section CoprimeTorsion

variable (T : Type*) [AddCommGroup T]

/-- The two Bézout coefficients reconstruct any element from its `d` and
`e` multiples. This identity requires no torsion hypothesis. -/
private theorem coprime_nsmul_reconstruct (d e : ℕ) (hde : d.Coprime e) (x : T) :
    Nat.gcdA d e • (d • x) + Nat.gcdB d e • (e • x) = x := by
  have hbez : Nat.gcdA d e * (d : ℤ) + Nat.gcdB d e * (e : ℤ) = 1 := by
    rw [mul_comm (Nat.gcdA d e) (d : ℤ), mul_comm (Nat.gcdB d e) (e : ℤ),
      ← Nat.gcd_eq_gcd_ab, hde.gcd_eq_one, Int.natCast_one]
  calc
    Nat.gcdA d e • (d • x) + Nat.gcdB d e • (e • x) =
        (Nat.gcdA d e * (d : ℤ) + Nat.gcdB d e * (e : ℤ)) • x := by
      simp only [add_smul, mul_smul, natCast_zsmul]
    _ = x := by rw [hbez, one_smul]

/-- Multiplication by the other factor, landing in `d`-torsion. -/
def coprimeTorsionLeft (d e : ℕ) : torsionBy T ((d * e : ℕ) : ℤ) →+ torsionBy T d where
  toFun x := ⟨e • (x : T), by
    apply torsionBy.nsmul_iff.mpr
    rw [← mul_smul]
    exact torsionBy.nsmul_iff.mp x.property⟩
  map_zero' := by
    apply Subtype.ext
    exact nsmul_zero e
  map_add' x y := by
    apply Subtype.ext
    exact (nsmulAddMonoidHom e : T →+ T).map_add (x : T) (y : T)

/-- Multiplication by the other factor, landing in `e`-torsion. -/
def coprimeTorsionRight (d e : ℕ) : torsionBy T ((d * e : ℕ) : ℤ) →+ torsionBy T e where
  toFun x := ⟨d • (x : T), by
    apply torsionBy.nsmul_iff.mpr
    rw [← mul_smul, Nat.mul_comm e d]
    exact torsionBy.nsmul_iff.mp x.property⟩
  map_zero' := by
    apply Subtype.ext
    exact nsmul_zero d
  map_add' x y := by
    apply Subtype.ext
    exact (nsmulAddMonoidHom d : T →+ T).map_add (x : T) (y : T)

/-- The left factor map has an explicit Bézout lift. -/
theorem coprimeTorsionLeft_surjective (d e : ℕ) (hde : d.Coprime e) :
    Function.Surjective (coprimeTorsionLeft T d e) := by
  intro y
  have hy : d • (y : T) = 0 := torsionBy.nsmul_iff.mp y.property
  refine ⟨⟨Nat.gcdB d e • (y : T), ?_⟩, ?_⟩
  · apply torsionBy.nsmul_iff.mpr
    rw [smul_comm (d * e) (Nat.gcdB d e), Nat.mul_comm d e, mul_smul,
      hy, smul_zero, smul_zero]
  · apply Subtype.ext
    change e • (Nat.gcdB d e • (y : T)) = (y : T)
    rw [smul_comm e (Nat.gcdB d e)]
    simpa only [hy, smul_zero, zero_add] using
      coprime_nsmul_reconstruct T d e hde (y : T)

/-- The right factor map has an explicit Bézout lift. -/
theorem coprimeTorsionRight_surjective (d e : ℕ) (hde : d.Coprime e) :
    Function.Surjective (coprimeTorsionRight T d e) := by
  intro y
  have hy : e • (y : T) = 0 := torsionBy.nsmul_iff.mp y.property
  refine ⟨⟨Nat.gcdA d e • (y : T), ?_⟩, ?_⟩
  · apply torsionBy.nsmul_iff.mpr
    rw [smul_comm (d * e) (Nat.gcdA d e), mul_smul,
      hy, smul_zero, smul_zero]
  · apply Subtype.ext
    change d • (Nat.gcdA d e • (y : T)) = (y : T)
    rw [smul_comm d (Nat.gcdA d e)]
    simpa only [hy, smul_zero, add_zero] using
      coprime_nsmul_reconstruct T d e hde (y : T)

/-- The pair of factor maps is injective, even for an infinite ambient group. -/
theorem coprimeTorsion_jointly_injective (d e : ℕ) (hde : d.Coprime e)
    {x y : torsionBy T ((d * e : ℕ) : ℤ)}
    (hleft : coprimeTorsionLeft T d e x = coprimeTorsionLeft T d e y)
    (hright : coprimeTorsionRight T d e x = coprimeTorsionRight T d e y) : x = y := by
  have he : e • (x : T) = e • (y : T) := congrArg Subtype.val hleft
  have hd : d • (x : T) = d • (y : T) := congrArg Subtype.val hright
  apply Subtype.ext
  calc
    (x : T) = Nat.gcdA d e • (d • (x : T)) + Nat.gcdB d e • (e • (x : T)) :=
      (coprime_nsmul_reconstruct T d e hde (x : T)).symm
    _ = Nat.gcdA d e • (d • (y : T)) + Nat.gcdB d e • (e • (y : T)) := by
      rw [hd, he]
    _ = (y : T) := coprime_nsmul_reconstruct T d e hde (y : T)

end CoprimeTorsion

section Detectors

variable (A B : Type*) [AddCommGroup A] [AddCommGroup B]

/-- The explicit coprime assembly of two additive detectors. Both variables
are projected to the factor-torsion groups, and CRT combines the outputs. -/
def coprimeLevelDetector (d e : ℕ) (hde : d.Coprime e)
    (δd : torsionBy A d →+ (torsionBy B d →+ ZMod d))
    (δe : torsionBy A e →+ (torsionBy B e →+ ZMod e)) :
    torsionBy A ((d * e : ℕ) : ℤ) →+ (torsionBy B ((d * e : ℕ) : ℤ) →+ ZMod (d * e)) where
  toFun x := (ZMod.chineseRemainder hde).symm.toAddMonoidHom.comp
    (((δd (coprimeTorsionLeft A d e x)).comp (coprimeTorsionLeft B d e)).prod
      ((δe (coprimeTorsionRight A d e x)).comp (coprimeTorsionRight B d e)))
  map_zero' := by
    ext z
    change (ZMod.chineseRemainder hde).symm
      (δd (coprimeTorsionLeft A d e 0) (coprimeTorsionLeft B d e z),
        δe (coprimeTorsionRight A d e 0) (coprimeTorsionRight B d e z)) = 0
    simp
  map_add' x y := by
    ext z
    change (ZMod.chineseRemainder hde).symm
      (δd (coprimeTorsionLeft A d e (x + y)) (coprimeTorsionLeft B d e z),
        δe (coprimeTorsionRight A d e (x + y)) (coprimeTorsionRight B d e z)) =
      (ZMod.chineseRemainder hde).symm
        (δd (coprimeTorsionLeft A d e x) (coprimeTorsionLeft B d e z),
          δe (coprimeTorsionRight A d e x) (coprimeTorsionRight B d e z)) +
      (ZMod.chineseRemainder hde).symm
        (δd (coprimeTorsionLeft A d e y) (coprimeTorsionLeft B d e z),
          δe (coprimeTorsionRight A d e y) (coprimeTorsionRight B d e z))
    simpa only [map_add, AddMonoidHom.add_apply, Prod.mk_add_mk] using
      (ZMod.chineseRemainder hde).symm.map_add
        (δd (coprimeTorsionLeft A d e x) (coprimeTorsionLeft B d e z),
          δe (coprimeTorsionRight A d e x) (coprimeTorsionRight B d e z))
        (δd (coprimeTorsionLeft A d e y) (coprimeTorsionLeft B d e z),
          δe (coprimeTorsionRight A d e y) (coprimeTorsionRight B d e z))

/-- Injectivity follows from factor injectivity, the surjectivity of each
factor projection on `B`, and joint injectivity of the projections on `A`. -/
theorem coprimeLevelDetector_injective (d e : ℕ) (hde : d.Coprime e)
    (δd : torsionBy A d →+ (torsionBy B d →+ ZMod d))
    (δe : torsionBy A e →+ (torsionBy B e →+ ZMod e))
    (hδd : Function.Injective δd) (hδe : Function.Injective δe) :
    Function.Injective (coprimeLevelDetector A B d e hde δd δe) := by
  intro x y hxy
  have hpairs (z : torsionBy B ((d * e : ℕ) : ℤ)) :
      (δd (coprimeTorsionLeft A d e x) (coprimeTorsionLeft B d e z),
        δe (coprimeTorsionRight A d e x) (coprimeTorsionRight B d e z)) =
      (δd (coprimeTorsionLeft A d e y) (coprimeTorsionLeft B d e z),
        δe (coprimeTorsionRight A d e y) (coprimeTorsionRight B d e z)) := by
    have hz := congrArg
      (fun f : torsionBy B ((d * e : ℕ) : ℤ) →+ ZMod (d * e) =>
        ZMod.chineseRemainder hde (f z)) hxy
    change (ZMod.chineseRemainder hde)
        ((ZMod.chineseRemainder hde).symm
          (δd (coprimeTorsionLeft A d e x) (coprimeTorsionLeft B d e z),
            δe (coprimeTorsionRight A d e x) (coprimeTorsionRight B d e z))) =
      (ZMod.chineseRemainder hde)
        ((ZMod.chineseRemainder hde).symm
          (δd (coprimeTorsionLeft A d e y) (coprimeTorsionLeft B d e z),
            δe (coprimeTorsionRight A d e y) (coprimeTorsionRight B d e z))) at hz
    simpa only [RingEquiv.apply_symm_apply] using hz
  apply coprimeTorsion_jointly_injective A d e hde
  · apply hδd
    ext w
    obtain ⟨z, hz⟩ := coprimeTorsionLeft_surjective B d e hde w
    simpa only [hz] using congrArg Prod.fst (hpairs z)
  · apply hδe
    ext w
    obtain ⟨z, hz⟩ := coprimeTorsionRight_surjective B d e hde w
    simpa only [hz] using congrArg Prod.snd (hpairs z)

/-- An additive detector at a level, together with its injectivity proof. -/
structure InjectiveLevelDetector (n : ℕ) where
  /-- The additive pairing from the level-`n` torsion groups to `ZMod n`. -/
  detector : torsionBy A n →+ (torsionBy B n →+ ZMod n)
  injective : Function.Injective detector

/-- The level-one package is explicitly the zero map on the trivial group. -/
def oneLevelDetector : InjectiveLevelDetector A B 1 where
  detector := 0
  injective := by
    intro x y _
    apply Subtype.ext
    have hx : (x : A) = 0 := by
      simpa only [one_nsmul] using (torsionBy.nsmul_iff (n := 1)).mp x.property
    have hy : (y : A) = 0 := by
      simpa only [one_nsmul] using (torsionBy.nsmul_iff (n := 1)).mp y.property
    exact hx.trans hy.symm

/-- Construct detector data at every positive level from the prime-power input families. -/
def assemblePrimePowerDetectorData
    (δ : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      torsionBy A ((p ^ r : ℕ) : ℤ) →+ (torsionBy B ((p ^ r : ℕ) : ℤ) →+ ZMod (p ^ r)))
    (δ_injective : ∀ (p : ℕ) (hp : p.Prime) (r : ℕ), Function.Injective (δ p hp r)) :
    ∀ U : ℕ, 0 < U → InjectiveLevelDetector A B U :=
  Nat.recOnPosPrimePosCoprime
    (motive := fun U : ℕ => 0 < U → InjectiveLevelDetector A B U)
    (fun p r hp _ _ => ⟨δ p hp r, δ_injective p hp r⟩)
    (fun h => False.elim (Nat.not_lt_zero 0 h))
    (fun _ => oneLevelDetector A B)
    (fun d e hd he hde Dd De _ =>
      let Dd' := Dd (lt_trans Nat.zero_lt_one hd)
      let De' := De (lt_trans Nat.zero_lt_one he)
      ⟨coprimeLevelDetector A B d e hde Dd'.detector De'.detector,
        coprimeLevelDetector_injective A B d e hde Dd'.detector De'.detector
          Dd'.injective De'.injective⟩)

/-- A constructed additive detector at every positive level from constructed
prime-power detectors. The injectivity inputs refer only to prime powers. -/
def assemblePrimePowerDetector
    (δ : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      torsionBy A ((p ^ r : ℕ) : ℤ) →+ (torsionBy B ((p ^ r : ℕ) : ℤ) →+ ZMod (p ^ r)))
    (δ_injective : ∀ (p : ℕ) (hp : p.Prime) (r : ℕ), Function.Injective (δ p hp r))
    (U : ℕ) (hU : 0 < U) :
    torsionBy A U →+ (torsionBy B U →+ ZMod U) :=
  (assemblePrimePowerDetectorData A B δ δ_injective U hU).detector

/-- The positive-level detector assembled above is injective. -/
theorem assemblePrimePowerDetector_injective
    (δ : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      torsionBy A ((p ^ r : ℕ) : ℤ) →+ (torsionBy B ((p ^ r : ℕ) : ℤ) →+ ZMod (p ^ r)))
    (δ_injective : ∀ (p : ℕ) (hp : p.Prime) (r : ℕ), Function.Injective (δ p hp r))
    (U : ℕ) (hU : 0 < U) :
    Function.Injective (assemblePrimePowerDetector A B δ δ_injective U hU) :=
  (assemblePrimePowerDetectorData A B δ δ_injective U hU).injective

end Detectors
end AddSubgroup.TorsionBy
