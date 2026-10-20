/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.MultiplicationCone

/-!
# Termwise quotients of multiplication cones

First-component projection compares the actual cone and termwise quotient cohomology.
Its surjectivity and injectivity retain the separate degree-three and degree-two
injectivity hypotheses on multiplication by the coefficient.

Source: `lean/R5Lab/Aglib/Algebra/Homology/MultiplicationCone/Quotient.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `dacc2f2f0de5bd91c930daf4ce10f989e28de7eafd50c4b103d3aec50d0ffc49`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace AddCommGrpCat.MultiplicationCone

universe u v

namespace ModTerm
variable (A : Type u) [AddCommGroup A]

def multiples (n : ℕ) : AddSubgroup A := (n • AddMonoidHom.id A).range
abbrev Quotient (n : ℕ) := A ⧸ multiples A n

def mk (n : ℕ) : A →+ Quotient A n := QuotientAddGroup.mk' _

@[simp] theorem mk_nsmul (n : ℕ) (a : A) : mk A n (n • a) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨a, rfl⟩

theorem mk_eq_zero_iff (n : ℕ) (a : A) :
    mk A n a = 0 ↔ ∃ b, n • b = a := by
  exact QuotientAddGroup.eq_zero_iff _

variable {A} {B : Type v} [AddCommGroup B]

def map (f : A →+ B) (n : ℕ) : Quotient A n →+ Quotient B n :=
  QuotientAddGroup.map _ _ f (by
    rintro _ ⟨a, rfl⟩
    exact ⟨f a, by simp⟩)

@[simp] theorem map_mk (f : A →+ B) (n : ℕ) (a : A) :
    map f n (mk A n a) = mk B n (f a) := rfl

/-- Ordinary quotient reduction; its representative is unchanged. -/
def reduction (A : Type u) [AddCommGroup A] (d e : ℕ) :
    Quotient A (d * e) →+ Quotient A d :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id A) (by
    rintro _ ⟨a, rfl⟩
    refine ⟨e • a, ?_⟩
    simp [smul_smul])

/-- Coefficient insertion has precisely the representative e • a. -/
def insertion (A : Type u) [AddCommGroup A] (d e : ℕ) :
    Quotient A d →+ Quotient A (d * e) :=
  QuotientAddGroup.map _ _ (e • AddMonoidHom.id A) (by
    rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp [smul_smul, Nat.mul_comm])

@[simp] theorem reduction_mk (A : Type u) [AddCommGroup A] (d e : ℕ) (a : A) :
    reduction A d e (mk A (d * e) a) = mk A d a := rfl

@[simp] theorem insertion_mk (A : Type u) [AddCommGroup A] (d e : ℕ) (a : A) :
    insertion A d e (mk A d a) = mk A (d * e) (e • a) := rfl

end ModTerm

variable {A₀ A₁ A₂ A₃ : Type*}
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]

namespace Complex
variable (C : Complex A₀ A₁ A₂ A₃)

/-- Quotient every term and every differential by the actual multiples of n. -/
def modComplex (n : ℕ) : Complex (ModTerm.Quotient A₀ n) (ModTerm.Quotient A₁ n)
    (ModTerm.Quotient A₂ n) (ModTerm.Quotient A₃ n) where
  d₀ := ModTerm.map C.d₀ n
  d₁ := ModTerm.map C.d₁ n
  d₂ := ModTerm.map C.d₂ n
  d₁_d₀ x := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₀ n) x
    change ModTerm.mk A₂ n (C.d₁ (C.d₀ a)) = 0
    rw [C.d₁_d₀, map_zero]
  d₂_d₁ x := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₁ n) x
    change ModTerm.mk A₃ n (C.d₂ (C.d₁ a)) = 0
    rw [C.d₂_d₁, map_zero]

/-- First-component projection on cone cocycles. -/
def projectCycles (n : ℕ) : C.Cocycles n →+ (C.modComplex n).Cycles₁ where
  toFun x := ⟨ModTerm.mk A₁ n x.val.1, by
    change ModTerm.mk A₂ n (C.d₁ x.val.1) = 0
    rw [x.property.1, ModTerm.mk_nsmul]⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- The actual map [(a,b)] ↦ [a mod n]. -/
def projectMod (n : ℕ) : C.H₁mod n →+ (C.modComplex n).H₁ :=
  QuotientAddGroup.map _ _ (C.projectCycles n) (by
    rintro _ ⟨a, rfl⟩
    refine ⟨ModTerm.mk A₀ n a.1, ?_⟩
    apply Subtype.ext
    change ModTerm.mk A₁ n (C.d₀ a.1) =
      ModTerm.mk A₁ n (C.d₀ a.1 + n • a.2)
    rw [map_add, ModTerm.mk_nsmul, add_zero])

@[simp] theorem projectMod_class (n : ℕ) (x : C.Cocycles n) :
    C.projectMod n (C.classMod n x) =
      QuotientAddGroup.mk' _ (C.projectCycles n x) := rfl

/-- Surjectivity only uses n-torsion-freeness of the term after C². -/
theorem projectMod_surjective (n : ℕ)
    (h₃ : Function.Injective (fun x : A₃ => n • x)) :
    Function.Surjective (C.projectMod n) := by
  intro q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (C.modComplex n).boundary₁.range q
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₁ n) z.val
  have hd : ModTerm.mk A₂ n (C.d₁ a) = 0 := by
    have hz := z.property
    change ModTerm.map C.d₁ n z.val = 0 at hz
    rw [← ha] at hz
    exact hz
  obtain ⟨b, hb⟩ := (ModTerm.mk_eq_zero_iff A₂ n (C.d₁ a)).mp hd
  have hdb : C.d₂ b = 0 := by
    apply h₃
    change n • C.d₂ b = n • (0 : A₃)
    rw [← map_nsmul, hb, C.d₂_d₁, smul_zero]
  let x : C.Cocycles n := ⟨(a, b), hb.symm, hdb⟩
  refine ⟨C.classMod n x, ?_⟩
  rw [projectMod_class]
  congr 1
  apply Subtype.ext
  exact ha

/-- Injectivity only uses n-torsion-freeness of C². -/
theorem projectMod_injective (n : ℕ)
    (h₂ : Function.Injective (fun x : A₂ => n • x)) :
    Function.Injective (C.projectMod n) := by
  suffices hz : ∀ q, C.projectMod n q = 0 → q = 0 by
    intro x y hxy
    exact sub_eq_zero.mp (hz (x - y) (by rw [map_sub, hxy, sub_self]))
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary n).range q
  have hp : C.projectMod n (C.classMod n x) = 0 := hq
  rw [projectMod_class] at hp
  obtain ⟨cbar, hcbar⟩ := (QuotientAddGroup.eq_zero_iff _).mp hp
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₀ n) cbar
  have ha : ModTerm.mk A₁ n (x.val.1 - C.d₀ c) = 0 := by
    have he := congrArg Subtype.val hcbar
    change ModTerm.map C.d₀ n cbar = ModTerm.mk A₁ n x.val.1 at he
    rw [← hc] at he
    change ModTerm.mk A₁ n (C.d₀ c) = ModTerm.mk A₁ n x.val.1 at he
    rw [map_sub, he, sub_self]
  obtain ⟨e, he⟩ := (ModTerm.mk_eq_zero_iff A₁ n _).mp ha
  have hae : C.d₀ c + n • e = x.val.1 := by rw [he]; abel
  have hbe : C.d₁ e = x.val.2 := by
    apply h₂
    change n • C.d₁ e = n • x.val.2
    rw [← map_nsmul, he, map_sub, C.d₁_d₀, sub_zero, x.property.1]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨(c, e), ?_⟩
  apply Subtype.ext
  exact Prod.ext hae hbe

/-- Cone cohomology agrees with the cohomology of the actual quotient complex. -/
def projectModEquiv (n : ℕ)
    (h₂ : Function.Injective (fun x : A₂ => n • x))
    (h₃ : Function.Injective (fun x : A₃ => n • x)) :
    C.H₁mod n ≃+ (C.modComplex n).H₁ :=
  AddEquiv.ofBijective (C.projectMod n)
    ⟨C.projectMod_injective n h₂, C.projectMod_surjective n h₃⟩

/-- Reduction of cycles in the actual quotient complexes. -/
def modReductionCycles (d e : ℕ) :
    (C.modComplex (d * e)).Cycles₁ →+ (C.modComplex d).Cycles₁ where
  toFun x := ⟨ModTerm.reduction A₁ d e x.val, by
    have hx := x.property
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₁ (d * e)) x.val
    rw [← ha] at hx ⊢
    change ModTerm.mk A₂ d (C.d₁ a) = 0
    change ModTerm.mk A₂ (d * e) (C.d₁ a) = 0 at hx
    exact congrArg (ModTerm.reduction A₂ d e) hx⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- Insertion of cycles in the actual quotient complexes. -/
def modInsertionCycles (d e : ℕ) :
    (C.modComplex d).Cycles₁ →+ (C.modComplex (d * e)).Cycles₁ where
  toFun x := ⟨ModTerm.insertion A₁ d e x.val, by
    have hx := x.property
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₁ d) x.val
    rw [← ha] at hx ⊢
    change ModTerm.mk A₂ (d * e) (C.d₁ (e • a)) = 0
    rw [map_nsmul]
    change ModTerm.mk A₂ d (C.d₁ a) = 0 at hx
    simpa only [ModTerm.insertion_mk, map_zero] using
      congrArg (ModTerm.insertion A₂ d e) hx⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- Ordinary coefficient reduction on quotient cohomology. -/
def modReduction (d e : ℕ) : (C.modComplex (d * e)).H₁ →+ (C.modComplex d).H₁ :=
  QuotientAddGroup.map _ _ (C.modReductionCycles d e) (by
    rintro _ ⟨c, rfl⟩
    refine ⟨ModTerm.reduction A₀ d e c, ?_⟩
    apply Subtype.ext
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₀ (d * e)) c
    rfl)

/-- Ordinary coefficient insertion on quotient cohomology. -/
def modInsertion (d e : ℕ) : (C.modComplex d).H₁ →+ (C.modComplex (d * e)).H₁ :=
  QuotientAddGroup.map _ _ (C.modInsertionCycles d e) (by
    rintro _ ⟨c, rfl⟩
    refine ⟨ModTerm.insertion A₀ d e c, ?_⟩
    apply Subtype.ext
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₀ d) c
    change ModTerm.mk A₁ (d * e) (C.d₀ (e • a)) =
      ModTerm.mk A₁ (d * e) (e • C.d₀ a)
    rw [map_nsmul])

/-- The projection intertwines the actual cone reduction and quotient reduction. -/
theorem projectMod_reduction (d e : ℕ) (x : C.H₁mod (d * e)) :
    C.projectMod d (C.reduction d e x) =
      C.modReduction d e (C.projectMod (d * e) x) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary (d * e)).range x
  rfl

/-- The projection intertwines the actual cone insertion and multiplication-by-e
insertion. There is no sign or extra factor of e. -/
theorem projectMod_insertion (d e : ℕ) (x : C.H₁mod d) :
    C.projectMod (d * e) (C.insertion d e x) =
      C.modInsertion d e (C.projectMod d x) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary d).range x
  rfl

end Complex
variable {B₀ B₁ B₂ B₃ : Type*}
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
  {C : Complex A₀ A₁ A₂ A₃} {D : Complex B₀ B₁ B₂ B₃}

namespace ChainMap

/-- An actual integral chain map induces the termwise quotient chain map. -/
def modChainMap (f : ChainMap C D) (n : ℕ) :
    ChainMap (C.modComplex n) (D.modComplex n) where
  f₀ := ModTerm.map f.f₀ n
  f₁ := ModTerm.map f.f₁ n
  f₂ := ModTerm.map f.f₂ n
  f₃ := ModTerm.map f.f₃ n
  comm₀ x := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₀ n) x
    change ModTerm.mk B₁ n (f.f₁ (C.d₀ a)) = ModTerm.mk B₁ n (D.d₀ (f.f₀ a))
    rw [f.comm₀]
  comm₁ x := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₁ n) x
    change ModTerm.mk B₂ n (f.f₂ (C.d₁ a)) = ModTerm.mk B₂ n (D.d₁ (f.f₁ a))
    rw [f.comm₁]
  comm₂ x := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (ModTerm.multiples A₂ n) x
    change ModTerm.mk B₃ n (f.f₃ (C.d₂ a)) = ModTerm.mk B₃ n (D.d₂ (f.f₂ a))
    rw [f.comm₂]

/-- Projection is natural for every actual chain map. -/
theorem projectMod_naturality (f : ChainMap C D) (n : ℕ) (x : C.H₁mod n) :
    D.projectMod n (f.onH₁mod n x) =
      (f.modChainMap n).onH₁ (C.projectMod n x) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary n).range x
  rfl

end ChainMap
end AddCommGrpCat.MultiplicationCone
