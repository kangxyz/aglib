/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Regular-curve Picard supplier

Source: `R5Lab.AlgebraicGeometry.Curves.Picard.KummerPairs`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`fbddaa6835616d701824106f3d305c175bdc7b39d8a846df55112fb509904aa9`.
Actual divisors, quotient relations, fractional inclusions, tensor comparisons,
equality transports and principal trivializations are preserved. The original
regularity, level and product-formula premises remain explicit. General native
line-bundle, tensor, descent and cohomology suppliers are reused.
-/

@[expose] public section


/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/

/-!
# Genuine divisor/function pairs

C3 preparatory algebra, K2-018 `lem:k2018-geometric-exact-order`, source
basis `7f86e4a`. All divisors and rational functions here are the actual objects
constructed in C1. The quotient is by `(div(h), h^n)`, giving precisely the
relation `(D,f) ~ (D + div(h), f h^n)` with the positive sign convention.
This file constructs the algebraic pair model. Identification with line bundles,
Picard torsion, and étale H¹ is separate and is not asserted here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.KummerPairs
universe u
variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] (n : ℕ)

/-- Genuine solutions of `div(f) = n D`, with the inherited componentwise group law. -/
def pairs : AddSubgroup (Divisor X × Additive X.functionFieldˣ) where
  carrier := {p | principal X p.2 = n • p.1}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change principal X (p.2 + q.2) = n • (p.1 + q.1)
    rw [map_add, hp, hq, nsmul_add]
  neg_mem' := by
    intro p hp
    change principal X (-p.2) = n • (-p.1)
    rw [map_neg, hp, smul_neg]

/-- Changes of a rational trivialization. -/
def relation : Additive X.functionFieldˣ →+ pairs X n where
  toFun h := ⟨(principal X h, n • h), by exact (principal X).map_nsmul n h⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' h k := by apply Subtype.ext; simp [nsmul_add]

/-- The actual quotient of divisor/function pairs by change of trivialization. -/
abbrev T := pairs X n ⧸ (relation X n).range

/-- The divisor-class quotient; no identification with Picard is implicit. -/
abbrev DivisorClass := Divisor X ⧸ (principal X).range

/-- The divisor class of a genuine pair. -/
def pairClass : pairs X n →+ DivisorClass X where
  toFun p := QuotientAddGroup.mk p.val.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Changing a rational trivialization does not change the divisor class. -/
theorem relation_le_ker_pairClass : (relation X n).range ≤ (pairClass X n).ker := by
  rintro _ ⟨h, rfl⟩
  change QuotientAddGroup.mk (principal X h) = (0 : DivisorClass X)
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨h, rfl⟩

/-- The well-defined class map on the genuine pair quotient. -/
def toClass : T X n →+ DivisorClass X :=
  QuotientAddGroup.lift _ (pairClass X n) (relation_le_ker_pairClass X n)

/-- Every pair has an n-torsion divisor class. -/
theorem pairClass_nsmul (p : pairs X n) : n • pairClass X n p = 0 := by
  change n • (QuotientAddGroup.mk' (principal X).range) p.val.1 = 0
  rw [← map_nsmul, ← p.property]
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨p.val.2, rfl⟩

/-- The class map lands in n-torsion, before any properness or Kummer comparison. -/
theorem toClass_nsmul (t : T X n) : n • toClass X n t = 0 := by
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact pairClass_nsmul X n p

/-- A chosen genuine pair representing a quotient class. -/
def representative (t : T X n) : pairs X n :=
  (QuotientAddGroup.mk_surjective t).choose

theorem representative_spec (t : T X n) :
    QuotientAddGroup.mk (representative X n t) = t :=
  (QuotientAddGroup.mk_surjective t).choose_spec

/-- The chosen divisor, which is deliberately not required to be additive. -/
def divisorRepresentative (t : T X n) : Divisor X := (representative X n t).val.1

/-- The chosen actual rational function, also not required to be additive. -/
def functionRepresentative (t : T X n) : X.functionFieldˣ :=
  (representative X n t).val.2.toMul

theorem divisor_representative (t : T X n) :
    principal X (Additive.ofMul (functionRepresentative X n t)) =
      n • divisorRepresentative X n t := (representative X n t).property

theorem class_representative (t : T X n) :
    QuotientAddGroup.mk (divisorRepresentative X n t) = toClass X n t := by
  change pairClass X n (representative X n t) = toClass X n t
  conv_rhs => rw [← representative_spec X n t]
  rfl

/-- Level one is trivial already at the genuine pair quotient. -/
theorem level_one_eq_zero (t : T X 1) : t = 0 := by
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective t
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨p.val.2, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change principal X p.val.2 = p.val.1
    have hp : principal X p.val.2 = 1 • p.val.1 := p.property
    simpa only [one_smul] using hp
  · simp [relation]

/-- Actual n-torsion subgroup of the divisor-class quotient. -/
def torsionClasses : AddSubgroup (DivisorClass X) where
  carrier := {c | n • c = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp only [Set.mem_ofPred_eq] at *; rw [nsmul_add, ha, hb,
      add_zero]
  neg_mem' := by
    intro a ha
    change n • (-a) = 0
    change n • a = 0 at ha
    calc
      n • (-a) = -(n • a) := (nsmulAddMonoidHom n).map_neg a
      _ = 0 := by rw [ha, neg_zero]

/-- The pair quotient maps canonically to actual torsion divisor classes. -/
def toTorsionClasses : T X n →+ torsionClasses X n :=
  (toClass X n).codRestrict _ (toClass_nsmul X n)

/-- Torsion classes have genuine pair lifts, without a Picard or H¹ assumption. -/
theorem toTorsionClasses_surjective : Function.Surjective (toTorsionClasses X n) := by
  intro c
  obtain ⟨D, hD⟩ := QuotientAddGroup.mk_surjective c.val
  have hz : (QuotientAddGroup.mk' (principal X).range) (n • D) = 0 := by
    rw [map_nsmul]
    change n • QuotientAddGroup.mk D = 0
    rw [hD]
    exact c.property
  obtain ⟨f, hf⟩ := (QuotientAddGroup.eq_zero_iff _).mp hz
  let p : pairs X n := ⟨(D, f), hf⟩
  refine ⟨QuotientAddGroup.mk p, ?_⟩
  apply Subtype.ext
  exact hD

/-- If the kernel of the actual principal map is n-divisible, the genuine
pair quotient injects into divisor classes. This is algebra, not a supplied
Picard or H¹ injection; the geometric divisibility application is separate. -/
theorem toClass_injective_of_kernel_divisible (hdiv : ∀ z : Additive X.functionFieldˣ,
    principal X z = 0 →
    ∃ w : Additive X.functionFieldˣ, principal X w = 0 ∧ n • w = z) :
    Function.Injective (toClass X n) := by
  apply (injective_iff_map_eq_zero (toClass X n)).mpr
  intro t ht
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective t
  change QuotientAddGroup.mk p.val.1 = (0 : DivisorClass X) at ht
  obtain ⟨h, hh⟩ := (QuotientAddGroup.eq_zero_iff _).mp ht
  have hz : principal X (p.val.2 - n • h) = 0 := by
    rw [map_sub, map_nsmul, hh]
    exact sub_eq_zero.mpr p.property
  obtain ⟨w, hw, hpow⟩ := hdiv _ hz
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨h + w, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change principal X (h + w) = p.val.1
    rw [map_add, hh, hw, add_zero]
  · change n • (h + w) = p.val.2
    rw [nsmul_add, hpow]
    abel

variable {k : Type u} [Field k]

/-- Algebraic closure removes the constant-unit/n kernel of the actual pair quotient.
The zero-order kernel theorem used here was proved by actual local-ring and
sheaf-gluing arguments in `Divisors.Basic`. -/
theorem toClass_injective_of_global_constants [IsAlgClosed k]
    (p : X ⟶ Spec (.of k))
    (hconstants : Function.Surjective
      (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom))
    (hpoints : ∀ x : X, x = genericPoint X ∨ IsClosed ({x} : Set X))
    (hcodim : ∀ x : ClosedPoint X, Order.coheight x.val = 1)
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (hn : 0 < n) : Function.Injective (toClass X n) := by
  apply toClass_injective_of_kernel_divisible X n
  intro z hz
  obtain ⟨a, ha⟩ := (kernel_eq_constants_from_global_functions X p hconstants
    hpoints hcodim z.toMul).mp hz
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) hn
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt hn)] at hb
    exact a.ne_zero hb.symm
  let b' : kˣ := Units.mk0 b hb0
  have hb' : b' ^ n = a := by apply Units.ext; simpa [b'] using hb
  refine ⟨Additive.ofMul (Units.map (Scheme.functionFieldConstants X p).toMonoidHom b'), ?_, ?_⟩
  · exact (kernel_eq_constants_from_global_functions X p hconstants hpoints hcodim _).mpr
      ⟨b', rfl⟩
  · change (Units.map (Scheme.functionFieldConstants X p).toMonoidHom b') ^ n = z.toMul
    rw [← map_pow, hb', ha]

/-- The equivalence from divisor/function pairs to `n`-torsion divisor classes
over an algebraically closed field, under the stated global-constants, point,
codimension-one and discrete-valuation hypotheses. -/
def torsionEquivOfGlobalConstants [IsAlgClosed k]
    (p : X ⟶ Spec (.of k))
    (hconstants : Function.Surjective
      (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom))
    (hpoints : ∀ x : X, x = genericPoint X ∨ IsClosed ({x} : Set X))
    (hcodim : ∀ x : ClosedPoint X, Order.coheight x.val = 1)
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (hn : 0 < n) : T X n ≃+ torsionClasses X n :=
  AddEquiv.ofBijective (toTorsionClasses X n)
    ⟨fun _ _ h => toClass_injective_of_global_constants X n p hconstants hpoints hcodim hn
      (congrArg Subtype.val h), toTorsionClasses_surjective X n⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.KummerPairs
