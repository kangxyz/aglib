/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Tactic.Abel

/-!
# Four-term additive complexes and multiplication cones

The three consecutive-zero differentials are inputs. Connecting maps, coefficient
insertion/reduction and low-degree comparison are constructed on the original quotient groups.

Source: `lean/R5Lab/Aglib/Algebra/Homology/MultiplicationCone.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `02693a10563e179348231eee5e2c389dd7c904eba342cfe6d9a9ebd7f9ccfb83`.
-/

@[expose] public section

namespace AddCommGrpCat.MultiplicationCone

variable (A₀ A₁ A₂ A₃ : Type*)
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]

/-- Four adjacent terms of an actual cochain complex. -/
structure Complex where
  /-- The differential from `A₀` to `A₁`. -/
  d₀ : A₀ →+ A₁
  /-- The differential from `A₁` to `A₂`. -/
  d₁ : A₁ →+ A₂
  /-- The differential from `A₂` to `A₃`. -/
  d₂ : A₂ →+ A₃
  d₁_d₀ : ∀ a, d₁ (d₀ a) = 0
  d₂_d₁ : ∀ a, d₂ (d₁ a) = 0

variable {A₀ A₁ A₂ A₃}
variable (C : Complex A₀ A₁ A₂ A₃)

namespace Complex

/-- Degree-two cycles, the kernel of `d₂`. -/
abbrev Cycles₂ := C.d₂.ker

/-- The differential `d₁` with codomain restricted to degree-two cycles. -/
def boundary₂ : A₁ →+ C.Cycles₂ where
  toFun a := ⟨C.d₁ a, C.d₂_d₁ a⟩
  map_zero' := by ext; exact C.d₁.map_zero
  map_add' a b := by ext; exact C.d₁.map_add a b

/-- Degree-two cohomology, the quotient of cycles by the image of `d₁`. -/
abbrev H₂ := C.Cycles₂ ⧸ C.boundary₂.range

/-- The quotient map from degree-two cycles to cohomology. -/
def class₂ : C.Cycles₂ →+ C.H₂ := QuotientAddGroup.mk' _

/-- Degree-one cocycles of the coefficient mapping cone, with sign convention
`d₁ a = n • b`, `d₂ b = 0`. -/
def cocycles (n : ℕ) : AddSubgroup (A₁ × A₂) where
  carrier := {x | C.d₁ x.1 = n • x.2 ∧ C.d₂ x.2 = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    constructor
    · simp only [map_add, Prod.fst_add, Prod.snd_add, nsmul_add, hx.1, hy.1]
    · simp only [map_add, Prod.snd_add, hx.2, hy.2, zero_add]
  neg_mem' hx := by
    constructor
    · simp only [map_neg, Prod.fst_neg, Prod.snd_neg, smul_neg, hx.1]
    · simp only [map_neg, Prod.snd_neg, hx.2, neg_zero]

/-- The additive group of coefficient-cone cocycles for multiplication by `n`. -/
abbrev Cocycles (n : ℕ) := C.cocycles n

/-- Degree-zero differential of the coefficient cone. -/
def boundary (n : ℕ) : A₀ × A₁ →+ C.Cocycles n where
  toFun x := ⟨(C.d₀ x.1 + n • x.2, C.d₁ x.2), by
    constructor
    · simp [C.d₁_d₀]
    · exact C.d₂_d₁ x.2⟩
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [smul_add]; abel

/-- Degree-one cohomology of the coefficient cone. -/
abbrev H₁mod (n : ℕ) := C.Cocycles n ⧸ (C.boundary n).range

/-- The quotient map from coefficient-cone cocycles to their cohomology classes. -/
def classMod (n : ℕ) : C.Cocycles n →+ C.H₁mod n := QuotientAddGroup.mk' _

/-- The map sending a cone cocycle to the degree-two class of its second component. -/
def betaOnCycles (n : ℕ) : C.Cocycles n →+ C.H₂ where
  toFun x := C.class₂ ⟨x.val.2, x.property.2⟩
  map_zero' := by change C.class₂ 0 = 0; exact map_zero _
  map_add' x y := by
    change C.class₂ (⟨x.val.2, x.property.2⟩ + ⟨y.val.2, y.property.2⟩) = _
    exact map_add _ _ _

/-- Genuine connecting map induced by the second component of a cone cocycle. -/
def beta (n : ℕ) : C.H₁mod n →+ C.H₂ :=
  QuotientAddGroup.lift _ (C.betaOnCycles n) (by
    rintro x ⟨a, rfl⟩
    change C.class₂ (C.boundary₂ a.2) = 0
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨a.2, rfl⟩)

@[simp] theorem beta_class (n : ℕ) (x : C.Cocycles n) :
    C.beta n (C.classMod n x) = C.class₂ ⟨x.val.2, x.property.2⟩ := rfl

/-- Annihilation is derived from the cone cocycle identity. -/
theorem annihilation (n : ℕ) (q : C.H₁mod n) : n • C.beta n q = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary n).range q
  rw [show (QuotientAddGroup.mk' (C.boundary n).range) x = C.classMod n x from rfl,
    beta_class, ← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨x.val.1, ?_⟩
  apply Subtype.ext
  exact x.property.1

/-- Every n-torsion class has a cone cocycle lift; no exactness assumption. -/
theorem torsion_surjectivity (n : ℕ) (x : C.H₂) (hx : n • x = 0) :
    ∃ q : C.H₁mod n, C.beta n q = x := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective C.boundary₂.range x
  change n • C.class₂ b = 0 at hx
  rw [← map_nsmul] at hx
  obtain ⟨a, ha⟩ := (QuotientAddGroup.eq_zero_iff _).mp hx
  have hab : C.d₁ a = n • b.val := congrArg Subtype.val ha
  refine ⟨C.classMod n ⟨(a, b.val), hab, b.property⟩, ?_⟩
  rfl


/-- Insertion of coefficient cones for m=d*e; crucially only the first
component is multiplied by e. This is not a tensor-square roots inclusion. -/
def insertionCycles (d e : ℕ) : C.Cocycles d →+ C.Cocycles (d * e) where
  toFun x := ⟨(e • x.val.1, x.val.2), by
    constructor
    · simp only [map_nsmul, x.property.1, smul_smul, Nat.mul_comm]
    · exact x.property.2⟩
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [smul_add]

/-- Reduction of coefficient cones for m=d*e. -/
def reductionCycles (d e : ℕ) : C.Cocycles (d * e) →+ C.Cocycles d where
  toFun x := ⟨(x.val.1, e • x.val.2), by
    constructor
    · simpa only [smul_smul] using x.property.1
    · simp only [map_nsmul, x.property.2, smul_zero]⟩
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [smul_add]

/-- The map from coefficient `d` to coefficient `d * e` induced by cone insertion. -/
def insertion (d e : ℕ) : C.H₁mod d →+ C.H₁mod (d * e) :=
  QuotientAddGroup.map _ _ (C.insertionCycles d e) (by
    rintro x ⟨a, rfl⟩
    refine ⟨(e • a.1, a.2), ?_⟩
    apply Subtype.ext
    ext <;> simp [boundary, insertionCycles, smul_add, smul_smul, Nat.mul_comm])

/-- The map from coefficient `d * e` to coefficient `d` induced by cone reduction. -/
def reduction (d e : ℕ) : C.H₁mod (d * e) →+ C.H₁mod d :=
  QuotientAddGroup.map _ _ (C.reductionCycles d e) (by
    rintro x ⟨a, rfl⟩
    refine ⟨(a.1, e • a.2), ?_⟩
    apply Subtype.ext
    ext <;> simp [boundary, reductionCycles, smul_smul])

/-- First coefficient Bockstein operator identity, derived on actual cone maps. -/
theorem beta_insertion (d e : ℕ) :
    (C.beta (d * e)).comp (C.insertion d e) = C.beta d := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary d).range q
  rfl

/-- Second coefficient Bockstein identity; written pointwise to make scaling clear. -/
theorem beta_reduction (d e : ℕ) (q : C.H₁mod (d * e)) :
    C.beta d (C.reduction d e q) = e • C.beta (d * e) q := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary (d * e)).range q
  change C.class₂ (e • (⟨x.val.2, x.property.2⟩ : C.Cycles₂)) =
    e • C.class₂ ⟨x.val.2, x.property.2⟩
  exact map_nsmul _ _ _

/-- Coefficients of level one are acyclic in degree one. -/
theorem level_one_zero (q : C.H₁mod 1) : q = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary 1).range q
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨(0, x.val.1), ?_⟩
  apply Subtype.ext
  ext
  · simp [boundary]
  · change C.d₁ x.val.1 = x.val.2
    simpa only [one_smul] using x.property.1


/-- Integral degree-one cycles. -/
abbrev Cycles₁ := C.d₁.ker

/-- The differential `d₀` with codomain restricted to degree-one cycles. -/
def boundary₁ : A₀ →+ C.Cycles₁ where
  toFun a := ⟨C.d₀ a, C.d₁_d₀ a⟩
  map_zero' := by ext; exact map_zero _
  map_add' a b := by ext; exact map_add _ _ _

/-- Degree-one cohomology, the quotient of cycles by the image of `d₀`. -/
abbrev H₁ := C.Cycles₁ ⧸ C.boundary₁.range

/-- The inclusion of an integral degree-one cycle as the cone cocycle `(a, 0)`. -/
def integralToCycles (n : ℕ) : C.Cycles₁ →+ C.Cocycles n where
  toFun a := ⟨(a.val, 0), by
    constructor
    · have ha : C.d₁ a.val = 0 := a.property
      simpa only [smul_zero] using ha
    · exact map_zero _⟩
  map_zero' := rfl
  map_add' a b := by ext <;> simp

/-- The integral-to-finite map on H¹, induced by the actual cone inclusion. -/
def integralToFinite (n : ℕ) : C.H₁ →+ C.H₁mod n :=
  QuotientAddGroup.map _ _ (C.integralToCycles n) (by
    rintro x ⟨a, rfl⟩
    refine ⟨(a, 0), ?_⟩
    apply Subtype.ext
    simp [boundary, boundary₁, integralToCycles])

@[simp] theorem beta_integralToFinite (n : ℕ) (a : C.H₁) :
    C.beta n (C.integralToFinite n a) = 0 := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective C.boundary₁.range a
  change C.class₂ 0 = 0
  exact map_zero _

/-- Exactness at H¹ of the coefficient cone. This does not claim that the
field cohomology group injects into its Bockstein target. -/
theorem beta_eq_zero_iff (n : ℕ) (q : C.H₁mod n) :
    C.beta n q = 0 ↔ ∃ a : C.H₁, C.integralToFinite n a = q := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary n).range q
    change C.class₂ ⟨x.val.2, x.property.2⟩ = 0 at h
    obtain ⟨b, hb⟩ := (QuotientAddGroup.eq_zero_iff _).mp h
    have hb' : C.d₁ b = x.val.2 := congrArg Subtype.val hb
    let c : C.Cycles₁ := ⟨x.val.1 - n • b, by
      change C.d₁ (x.val.1 - n • b) = 0
      rw [map_sub, map_nsmul, hb', x.property.1, sub_self]⟩
    refine ⟨QuotientAddGroup.mk' _ c, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    refine ⟨(0, -b), ?_⟩
    apply Subtype.ext
    ext <;> simp [boundary, integralToCycles, c, hb']
  · rintro ⟨a, rfl⟩
    exact C.beta_integralToFinite n a


/-- Multiples of n in integral H¹ map to zero in finite H¹. -/
theorem integralToFinite_nsmul (n : ℕ) (a : C.H₁) :
    C.integralToFinite n (n • a) = 0 := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective C.boundary₁.range a
  rw [← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨(0, b.val), ?_⟩
  apply Subtype.ext
  have hb : C.d₁ b.val = 0 := b.property
  ext <;> simp [boundary, integralToCycles, hb]

/-- The integral-to-finite kernel is exactly n H¹, giving the H¹/n term
of the coefficient short exact sequence. -/
theorem integralToFinite_eq_zero_iff (n : ℕ) (a : C.H₁) :
    C.integralToFinite n a = 0 ↔ ∃ b : C.H₁, n • b = a := by
  constructor
  · intro h
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective C.boundary₁.range a
    obtain ⟨p, hp⟩ := (QuotientAddGroup.eq_zero_iff _).mp h
    have h₁ : C.d₀ p.1 + n • p.2 = c.val := congrArg (fun x => x.val.1) hp
    have h₂ : C.d₁ p.2 = 0 := congrArg (fun x => x.val.2) hp
    let b : C.Cycles₁ := ⟨p.2, h₂⟩
    refine ⟨QuotientAddGroup.mk' _ b, ?_⟩
    rw [← map_nsmul]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    refine ⟨-p.1, ?_⟩
    apply Subtype.ext
    change C.d₀ (-p.1) = n • p.2 - c.val
    rw [map_neg, ← h₁]
    abel
  · rintro ⟨b, rfl⟩
    exact C.integralToFinite_nsmul n b

end Complex


variable {B₀ B₁ B₂ B₃ : Type*}
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
variable (D : Complex B₀ B₁ B₂ B₃)

/-- An actual map on each term, commuting with all three differentials. -/
structure ChainMap where
  /-- The additive map on the `A₀` term. -/
  f₀ : A₀ →+ B₀
  /-- The additive map on the `A₁` term. -/
  f₁ : A₁ →+ B₁
  /-- The additive map on the `A₂` term. -/
  f₂ : A₂ →+ B₂
  /-- The additive map on the `A₃` term. -/
  f₃ : A₃ →+ B₃
  comm₀ : ∀ a, f₁ (C.d₀ a) = D.d₀ (f₀ a)
  comm₁ : ∀ a, f₂ (C.d₁ a) = D.d₁ (f₁ a)
  comm₂ : ∀ a, f₃ (C.d₂ a) = D.d₂ (f₂ a)

namespace ChainMap
variable {C D}

/-- The map on integral degree-one cycles induced by a chain map. -/
def onCycles₁ (f : ChainMap C D) : C.Cycles₁ →+ D.Cycles₁ where
  toFun x := ⟨f.f₁ x.val, by
    change D.d₁ (f.f₁ x.val) = 0
    rw [← f.comm₁, x.property, map_zero]⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- The integral degree-one cohomology map induced by the actual chain map. -/
def onH₁ (f : ChainMap C D) : C.H₁ →+ D.H₁ :=
  QuotientAddGroup.map _ _ f.onCycles₁ (by
    rintro x ⟨a, rfl⟩
    refine ⟨f.f₀ a, ?_⟩
    apply Subtype.ext
    exact (f.comm₀ a).symm)

/-- The map on degree-two cycles induced by a chain map. -/
def onCycles₂ (f : ChainMap C D) : C.Cycles₂ →+ D.Cycles₂ where
  toFun x := ⟨f.f₂ x.val, by
    change D.d₂ (f.f₂ x.val) = 0
    rw [← f.comm₂, x.property, map_zero]⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- The map on degree-two cohomology induced by a chain map. -/
def onH₂ (f : ChainMap C D) : C.H₂ →+ D.H₂ :=
  QuotientAddGroup.map _ _ f.onCycles₂ (by
    rintro x ⟨a, rfl⟩
    refine ⟨f.f₁ a, ?_⟩
    apply Subtype.ext
    exact (f.comm₁ a).symm)

/-- The componentwise map on coefficient-cone cocycles induced by a chain map. -/
def onCocycles (f : ChainMap C D) (n : ℕ) : C.Cocycles n →+ D.Cocycles n where
  toFun x := ⟨(f.f₁ x.val.1, f.f₂ x.val.2), by
    constructor
    · rw [← f.comm₁, x.property.1, map_nsmul]
    · rw [← f.comm₂, x.property.2, map_zero]⟩
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

/-- The map on coefficient-cone degree-one cohomology induced by a chain map. -/
def onH₁mod (f : ChainMap C D) (n : ℕ) : C.H₁mod n →+ D.H₁mod n :=
  QuotientAddGroup.map _ _ (f.onCocycles n) (by
    rintro x ⟨a, rfl⟩
    refine ⟨(f.f₀ a.1, f.f₁ a.2), ?_⟩
    apply Subtype.ext
    ext <;> simp [Complex.boundary, onCocycles, f.comm₀, f.comm₁])

/-- Naturality is proved for the constructed connecting map. -/
theorem beta_naturality (f : ChainMap C D) (n : ℕ) :
    (D.beta n).comp (f.onH₁mod n) = f.onH₂.comp (C.beta n) := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary n).range q
  rfl

theorem integralToFinite_naturality (f : ChainMap C D) (n : ℕ) (a : C.H₁) :
    f.onH₁mod n (C.integralToFinite n a) = D.integralToFinite n (f.onH₁ a) := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective C.boundary₁.range a
  change D.classMod n (f.onCocycles n (C.integralToCycles n c)) =
    D.classMod n (D.integralToCycles n (f.onCycles₁ c))
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact map_zero _

theorem beta_naturality_apply (f : ChainMap C D) (n : ℕ) (a : C.H₁mod n) :
    D.beta n (f.onH₁mod n a) = f.onH₂ (C.beta n a) :=
  DFunLike.congr_fun (f.beta_naturality n) a

theorem insertion_naturality (f : ChainMap C D) (d e : ℕ) (a : C.H₁mod d) :
    f.onH₁mod (d * e) (C.insertion d e a) =
      D.insertion d e (f.onH₁mod d a) := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary d).range a
  change D.classMod (d * e) (f.onCocycles (d * e) (C.insertionCycles d e c)) =
    D.classMod (d * e) (D.insertionCycles d e (f.onCocycles d c))
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · exact map_nsmul _ _ _
  · rfl

theorem reduction_naturality (f : ChainMap C D) (d e : ℕ) (a : C.H₁mod (d * e)) :
    f.onH₁mod d (C.reduction d e a) =
      D.reduction d e (f.onH₁mod (d * e) a) := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective (C.boundary (d * e)).range a
  change D.classMod d (f.onCocycles d (C.reductionCycles d e c)) =
    D.classMod d (D.reductionCycles d e (f.onCocycles (d * e) c))
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact map_nsmul _ _ _

theorem onH₁mod_injective (f : ChainMap C D)
    (h₁ : Function.Bijective f.onH₁) (h₂ : Function.Injective f.onH₂) (n : ℕ) :
    Function.Injective (f.onH₁mod n) := by
  suffices hz : ∀ x, f.onH₁mod n x = 0 → x = 0 by
    intro x y hxy
    exact sub_eq_zero.mp (hz (x - y) (by rw [map_sub, hxy, sub_self]))
  intro x hx
  have hb : C.beta n x = 0 := h₂ (by
    rw [← f.beta_naturality_apply n x, hx, map_zero, map_zero])
  obtain ⟨a, ha⟩ := (C.beta_eq_zero_iff n x).mp hb
  have hd : D.integralToFinite n (f.onH₁ a) = 0 := by
    rw [← f.integralToFinite_naturality, ha, hx]
  obtain ⟨b, hb⟩ := (D.integralToFinite_eq_zero_iff n (f.onH₁ a)).mp hd
  obtain ⟨c, hc⟩ := h₁.2 b
  have hca : n • c = a := h₁.1 (by rw [map_nsmul, hc, hb])
  rw [← ha, ← hca, C.integralToFinite_nsmul]

theorem onH₁mod_surjective (f : ChainMap C D)
    (h₁ : Function.Surjective f.onH₁) (h₂ : Function.Bijective f.onH₂) (n : ℕ) :
    Function.Surjective (f.onH₁mod n) := by
  intro y
  obtain ⟨b, hb⟩ := h₂.2 (D.beta n y)
  have hnb : n • b = 0 := h₂.1 (by
    rw [map_nsmul, hb, D.annihilation, map_zero])
  obtain ⟨x, hx⟩ := C.torsion_surjectivity n b hnb
  have hdiff : D.beta n (y - f.onH₁mod n x) = 0 := by
    rw [map_sub, f.beta_naturality_apply, hx, hb, sub_self]
  obtain ⟨a, ha⟩ := (D.beta_eq_zero_iff n (y - f.onH₁mod n x)).mp hdiff
  obtain ⟨c, hc⟩ := h₁ a
  refine ⟨x + C.integralToFinite n c, ?_⟩
  rw [map_add, f.integralToFinite_naturality, hc, ha]
  abel

/-- Integral comparison in precisely degrees one and two suffices. No
degreewise flatness, injectivity of multiplication by n, or positivity of n
is used by this actual mapping-cone argument. -/
theorem onH₁mod_bijective (f : ChainMap C D)
    (h₁ : Function.Bijective f.onH₁) (h₂ : Function.Bijective f.onH₂) (n : ℕ) :
    Function.Bijective (f.onH₁mod n) :=
  ⟨f.onH₁mod_injective h₁ h₂.1 n, f.onH₁mod_surjective h₁.2 h₂ n⟩

/-- Finite-coefficient comparison obtained from the same integral chain map. -/
noncomputable def finiteEquiv (f : ChainMap C D)
    (h₁ : Function.Bijective f.onH₁) (h₂ : Function.Bijective f.onH₂) (n : ℕ) :
    C.H₁mod n ≃+ D.H₁mod n :=
  AddEquiv.ofBijective (f.onH₁mod n) (f.onH₁mod_bijective h₁ h₂ n)

end ChainMap
end AddCommGrpCat.MultiplicationCone
