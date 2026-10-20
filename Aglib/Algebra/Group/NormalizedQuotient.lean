/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Aglib.GroupTheory.Torsion.Equivalence

/-!
# Normalized representatives of quotients by split additive subgroups

A supplied additive retraction identifies the kernel with the quotient
by the section range, including their natural torsion subgroups. The
retraction is a hypothesis throughout.

Source: `R5Lab.Aglib.Algebra.Group.NormalizedQuotient`.
Packet SHA-256:
`e41ac84df68e29ede42c46946b21eb80200f38e6680b0b2fe71e04b8c993c0cb`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

namespace AddMonoidHom.Retraction

section Normalization

variable {C I : Type*} [AddCommGroup C] [AddCommGroup I]

/-- Constant subtraction in `K2-018#sec:k2018-splitting`, generalized to additive groups. -/
def normalize (c : C →+ I) (s : I →+ C) : I →+ I :=
  AddMonoidHom.id I - c.comp s

/-- The normalized representative formula in `K2-018#sec:k2018-splitting`. -/
@[simp] theorem normalize_apply (c : C →+ I) (s : I →+ C) (x : I) :
    normalize c s x = x - c (s x) := rfl

/-- Normalization kills specialization, conditional on the source's retraction identity. -/
theorem specialize_normalize (c : C →+ I) (s : I →+ C)
    (hsc : Function.LeftInverse s c) (x : I) : s (normalize c s x) = 0 := by
  rw [normalize_apply, map_sub, hsc (s x), sub_self]

/-- Constants vanish after the normalization in `K2-018#sec:k2018-splitting`. -/
theorem normalize_constant (c : C →+ I) (s : I →+ C)
    (hsc : Function.LeftInverse s c) (a : C) : normalize c s (c a) = 0 := by
  rw [normalize_apply, hsc a, sub_self]

/-- An already normalized representative is unchanged in `K2-018#sec:k2018-splitting`. -/
theorem normalize_of_specialize_eq_zero (c : C →+ I) (s : I →+ C)
    {x : I} (hx : s x = 0) : normalize c s x = x := by
  simp [hx]

/-- Normalization with codomain the origin kernel, from `K2-018#sec:k2018-splitting`. -/
def normalizedHom (c : C →+ I) (s : I →+ C)
    (hsc : Function.LeftInverse s c) : I →+ s.ker :=
  (normalize c s).codRestrict s.ker (fun x => specialize_normalize c s hsc x)

/-- Canonical normalization of a reduced class, from `K2-018#sec:k2018-splitting`. -/
def reducedNormalize (c : C →+ I) (s : I →+ C)
    (hsc : Function.LeftInverse s c) : (I ⧸ c.range) →+ s.ker :=
  QuotientAddGroup.lift c.range (normalizedHom c s hsc) (by
    rintro x ⟨a, rfl⟩
    apply Subtype.ext
    exact normalize_constant c s hsc a)

/-- A reduced class is normalized by subtracting its origin constant. -/
theorem reducedNormalize_mk (c : C →+ I) (s : I →+ C)
    (hsc : Function.LeftInverse s c) (x : I) :
    (reducedNormalize c s hsc (QuotientAddGroup.mk' c.range x) : I) =
      normalize c s x := rfl

/-- Constant subtraction preserves the quotient class in `K2-018#sec:k2018-splitting`. -/
theorem quotient_normalize (c : C →+ I) (s : I →+ C) (x : I) :
    QuotientAddGroup.mk' c.range (normalize c s x) =
      QuotientAddGroup.mk' c.range x := by
  rw [normalize_apply, map_sub]
  have hc : QuotientAddGroup.mk' c.range (c (s x)) = 0 :=
    (QuotientAddGroup.eq_zero_iff (c (s x))).mpr ⟨s x, rfl⟩
  rw [hc, sub_zero]

/-- The retraction identifies the reduced quotient with the origin kernel.
Source: `K2-018#sec:k2018-splitting`, lines 244–253; the retraction is a premise. -/
def normalizedQuotientEquiv (c : C →+ I) (s : I →+ C)
    (hsc : Function.LeftInverse s c) : s.ker ≃+ (I ⧸ c.range) where
  toFun := fun x => QuotientAddGroup.mk' c.range x
  invFun := reducedNormalize c s hsc
  left_inv := by
    intro x
    apply Subtype.ext
    exact normalize_of_specialize_eq_zero c s x.property
  right_inv := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective c.range q
    exact quotient_normalize c s x
  map_add' := by
    intro x y
    exact map_add (QuotientAddGroup.mk' c.range) (x : I) (y : I)

/-- Unique normalized representatives, conditional on `K2-018`'s origin retraction. -/
theorem existsUnique_normalized_representative (c : C →+ I) (s : I →+ C)
    (hsc : Function.LeftInverse s c) (q : I ⧸ c.range) :
    ∃! x : I, s x = 0 ∧ QuotientAddGroup.mk' c.range x = q := by
  refine ⟨reducedNormalize c s hsc q, ⟨(reducedNormalize c s hsc q).property,
    (normalizedQuotientEquiv c s hsc).apply_symm_apply q⟩, ?_⟩
  intro x hx
  have heq : (⟨x, hx.1⟩ : s.ker) = reducedNormalize c s hsc q :=
    (normalizedQuotientEquiv c s hsc).injective
      (hx.2.trans ((normalizedQuotientEquiv c s hsc).apply_symm_apply q).symm)
  exact congrArg Subtype.val heq

/-- Every reduced `n`-torsion class has a unique normalized `n`-torsion lift.
Source: the quotient splitting used in `K2-018#prop:k2018-arithmetic-characters`;
this is an additive-group consequence, with no K-theory group instantiated. -/
theorem existsUnique_normalized_torsion_representative (c : C →+ I) (s : I →+ C)
    (hsc : Function.LeftInverse s c) (n : ℕ) (q : I ⧸ c.range) (hq : n • q = 0) :
    ∃! x : I, s x = 0 ∧ QuotientAddGroup.mk' c.range x = q ∧ n • x = 0 := by
  obtain ⟨x, hx, huniq⟩ := existsUnique_normalized_representative c s hsc q
  have hn : n • x = 0 := by
    have hzero : n • (⟨x, hx.1⟩ : s.ker) = 0 :=
      (normalizedQuotientEquiv c s hsc).injective (by
        rw [map_nsmul]
        change n • QuotientAddGroup.mk' c.range x = QuotientAddGroup.mk' c.range 0
        rw [hx.2, hq, map_zero])
    exact congrArg Subtype.val hzero
  exact ⟨x, ⟨hx.1, hx.2, hn⟩, fun y hy => huniq y ⟨hy.1, hy.2.1⟩⟩

end Normalization

/-- Origin-normalized torsion, the representative form of `K2-018`'s reduced torsion. -/
def normalizedTorsion {C A : Type*} [AddCommGroup C] [AddCommGroup A]
    (s : A →+ C) (n : ℕ) : AddSubgroup A :=
  s.ker ⊓ AddSubgroup.torsionBy A (n : ℤ)

/-- Normalized torsion is torsion in the origin kernel; generic subtype bookkeeping. -/
def normalizedTorsionEquiv {C A : Type*} [AddCommGroup C] [AddCommGroup A]
    (s : A →+ C) (n : ℕ) : normalizedTorsion s n ≃+ AddSubgroup.torsionBy s.ker (n : ℤ) where
  toFun := fun x => ⟨⟨x, x.property.1⟩, by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    change n • (⟨x, x.property.1⟩ : s.ker) = 0
    exact Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp x.property.2)⟩
  invFun := fun x => ⟨x.val.val, ⟨x.val.property, by
    exact congrArg Subtype.val x.property⟩⟩
  left_inv := fun x => Subtype.ext rfl
  right_inv := fun x => Subtype.ext (Subtype.ext rfl)
  map_add' := fun x y => Subtype.ext (Subtype.ext rfl)

/-- The source's retraction identifies normalized torsion with reduced-quotient torsion. -/
def normalizedTorsionQuotientEquiv {C A : Type*} [AddCommGroup C] [AddCommGroup A]
    (c : C →+ A) (s : A →+ C) (hsc : Function.LeftInverse s c) (n : ℕ) :
    normalizedTorsion s n ≃+ AddSubgroup.torsionBy (A ⧸ c.range) (n : ℤ) :=
  (normalizedTorsionEquiv s n).trans (AddEquiv.torsionByNat n (normalizedQuotientEquiv c s hsc))


end AddMonoidHom.Retraction
