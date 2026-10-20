/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.Galois
public import Aglib.GroupCohomology.H1.Continuous
public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Actual continuous Kummer cocycles

The coefficient is the group of roots in the fixed algebraic closure, and a
cocycle is obtained from an actual nth root. Choice independence is proved by
an explicit principal cocycle, not imposed as a quotient relation.
-/
@[expose] public section

noncomputable section
namespace GroupCohomology.Kummer
open Field.absoluteGaloisGroup.RootsOfUnity _root_.GroupCohomology.ContinuousH1
variable (K : Type*) [Field K]
local notation "Kbar" => AlgebraicClosure K
local notation "G" => Field.absoluteGaloisGroup K

local instance closureTopology : TopologicalSpace Kbar := ⊥
local instance closureDiscrete : DiscreteTopology Kbar := ⟨rfl⟩
local instance closureAction : MulSemiringAction G Kbar :=
  inferInstanceAs (MulSemiringAction (Kbar ≃ₐ[K] Kbar) Kbar)
local instance closureContinuous : ContinuousSMul G Kbar := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  exact stabilizer_isOpen_of_isIntegral (K := K) x

/-- The actual inclusion of base-field units into the algebraic closure. -/
def baseUnits : Kˣ →* (AlgebraicClosure K)ˣ := Units.map (algebraMap K Kbar).toMonoidHom

/-- Galois action on the actual units of the algebraic closure. -/
def unitAction (g : G) : (AlgebraicClosure K)ˣ →* (AlgebraicClosure K)ˣ :=
  Units.map (show Kbar ≃ₐ[K] Kbar from g).toRingHom.toMonoidHom

@[simp] theorem unitAction_mul (g h : G) (a : (AlgebraicClosure K)ˣ) :
    unitAction K (g * h) a = unitAction K g (unitAction K h a) := rfl

@[simp] theorem unitAction_base (g : G) (f : Kˣ) :
    unitAction K g (baseUnits K f) = baseUnits K f := by
  ext
  exact (show Kbar ≃ₐ[K] Kbar from g).commutes f

/-- Positive powers are surjective on units in the actual algebraic closure. -/
theorem exists_root (n : ℕ) (hn : 0 < n) (f : Kˣ) :
    ∃ a : (AlgebraicClosure K)ˣ, a ^ n = baseUnits K f := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K Kbar (f : K)) hn
  have hne : a ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt hn)] at ha
    exact ((map_ne_zero (algebraMap K Kbar)).mpr f.ne_zero) ha.symm
  refine ⟨Units.mk0 a hne, ?_⟩
  apply Units.ext
  exact ha

variable (n : ℕ) {f : Kˣ} (a : (AlgebraicClosure K)ˣ) (ha : a ^ n = baseUnits K f)

/-- The Kummer crossed-homomorphism value σ(a)/a, as an actual root of unity. -/
def value (a : (AlgebraicClosure K)ˣ) {f : Kˣ}
    (ha : a ^ n = baseUnits K f) (g : G) : Mu K n := by
  refine Additive.ofMul (⟨unitAction K g a / a, ?_⟩ : rootsOfUnity n (AlgebraicClosure K))
  rw [mem_rootsOfUnity, div_pow, ← map_pow, ha, unitAction_base, div_self']

@[simp] theorem value_units (g : G) :
    ((value K n a ha g).toMul : (AlgebraicClosure K)ˣ) = unitAction K g a / a := rfl

/-- Continuity comes from the actual Krull-continuous orbit of the chosen root. -/
theorem value_continuous : Continuous (value K n a ha) := by
  have horbit : Continuous (fun g : G => (g • (a : Kbar) : Kbar)) :=
    continuous_id.smul continuous_const
  have hquot : Continuous (fun g : G => (g • (a : Kbar) : Kbar) / (a : Kbar)) :=
    horbit.div_const _
  have hcast : Function.Injective (fun x : Mu K n => ((x.toMul : (AlgebraicClosure K)ˣ) : Kbar)) :=
    by
    intro x y h
    apply Additive.toMul.injective
    apply Subtype.ext
    exact Units.ext h
  let j : Mu K n → Kbar := fun x => ((x.toMul : (AlgebraicClosure K)ˣ) : Kbar)
  have hc : Continuous (Function.invFun j) := continuous_of_discreteTopology
  apply (hc.comp hquot).congr
  intro g
  have hval : j (value K n a ha g) = (g • (a : Kbar) : Kbar) / (a : Kbar) := by
    simp only [j, value_units, Units.val_div_eq_div_val]
    congr 1
  change Function.invFun j ((g • (a : Kbar) : Kbar) / (a : Kbar)) = _
  rw [← hval]
  exact Function.leftInverse_invFun hcast (value K n a ha g)


/-- The crossed-homomorphism identity is an identity of actual field units. -/
theorem value_mul (g h : G) :
    value K n a ha (g * h) = value K n a ha g + g • value K n a ha h := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change unitAction K (g * h) a / a =
    (unitAction K g a / a) * unitAction K g (unitAction K h a / a)
  rw [unitAction_mul, map_div]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The actual continuous Kummer cocycle of a selected nth root. -/
def cocycle : Cocycle G (Mu K n) :=
  ⟨⟨value K n a ha, value_continuous K n a ha⟩, value_mul K n a ha⟩

@[simp] theorem cocycle_value (g : G) :
    (cocycle K n a ha).val g = value K n a ha g := rfl

/-- The ratio of two nth roots of the same unit is an actual nth root of unity. -/
def rootRatio (b : (AlgebraicClosure K)ˣ) (hb : b ^ n = baseUnits K f) : Mu K n :=
  Additive.ofMul ⟨b / a, by rw [mem_rootsOfUnity, div_pow, hb, ha, div_self']⟩

/-- Root choices differ by the explicit principal cocycle of their ratio. -/
theorem cocycle_sub (b : (AlgebraicClosure K)ˣ) (hb : b ^ n = baseUnits K f) :
    cocycle K n b hb - cocycle K n a ha = principal G (Mu K n) (rootRatio K n a ha b hb) := by
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro g
  apply Additive.toMul.injective
  apply Subtype.ext
  change (unitAction K g b / b) / (unitAction K g a / a) =
    unitAction K g (b / a) / (b / a)
  rw [map_div]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The Kummer cohomology class is independent of its actual nth-root choice. -/
theorem class_independent (b : (AlgebraicClosure K)ˣ) (hb : b ^ n = baseUnits K f) :
    classOf G (Mu K n) (cocycle K n b hb) = classOf G (Mu K n) (cocycle K n a ha) := by
  rw [classOf_eq_iff]
  exact ⟨rootRatio K n a ha b hb, (cocycle_sub K n a ha b hb).symm⟩

/-- A selected actual nth root, used only after root-choice independence. -/
def chosenRoot (hn : 0 < n) (f : Kˣ) : (AlgebraicClosure K)ˣ :=
  (exists_root K n hn f).choose

theorem chosenRoot_pow (hn : 0 < n) (f : Kˣ) :
    chosenRoot K n hn f ^ n = baseUnits K f :=
  (exists_root K n hn f).choose_spec

/-- The actual continuous Kummer class with values in roots of unity. -/
def kummer (hn : 0 < n) (f : Kˣ) : H1 G (Mu K n) :=
  classOf G (Mu K n) (cocycle K n (chosenRoot K n hn f) (chosenRoot_pow K n hn f))

theorem kummer_eq_class (hn : 0 < n) :
    kummer K n hn f = classOf G (Mu K n) (cocycle K n a ha) :=
  class_independent K n a ha (chosenRoot K n hn f) (chosenRoot_pow K n hn f)

/-- Multiplication of actual roots gives addition of the continuous Kummer cocycles. -/
theorem cocycle_mul {f' : Kˣ} (b : (AlgebraicClosure K)ˣ) (hb : b ^ n = baseUnits K f') :
    cocycle K n (f := f * f') (a * b) (by rw [mul_pow, ha, hb, map_mul]) =
      cocycle K n a ha + cocycle K n b hb := by
  apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
  intro g
  apply Additive.toMul.injective
  apply Subtype.ext
  change unitAction K g (a * b) / (a * b) =
    (unitAction K g a / a) * (unitAction K g b / b)
  rw [map_mul]
  exact mul_div_mul_comm _ _ _ _

/-- The unit has the zero Kummer class. -/
@[simp] theorem kummer_one (hn : 0 < n) : kummer K n hn 1 = 0 := by
  rw [kummer_eq_class K n 1 (by simp) hn]
  have h : cocycle K n 1 (show (1 : (AlgebraicClosure K)ˣ) ^ n = baseUnits K 1 by simp) = 0 := by
    apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
    intro g
    apply Additive.toMul.injective
    apply Subtype.ext
    change unitAction K g 1 / 1 = 1
    simp
  rw [h, map_zero]

/-- The genuine continuous Kummer class is multiplicative in the field unit. -/
theorem kummer_mul (hn : 0 < n) (f f' : Kˣ) :
    kummer K n hn (f * f') = kummer K n hn f + kummer K n hn f' := by
  let a := chosenRoot K n hn f
  let b := chosenRoot K n hn f'
  have ha : a ^ n = baseUnits K f := chosenRoot_pow K n hn f
  have hb : b ^ n = baseUnits K f' := chosenRoot_pow K n hn f'
  have hab : (a * b) ^ n = baseUnits K (f * f') := by rw [mul_pow, ha, hb, map_mul]
  rw [kummer_eq_class K n (a * b) hab hn, cocycle_mul K n a ha b hb, map_add,
    ← kummer_eq_class K n a ha hn, ← kummer_eq_class K n b hb hn]

/-- An nth power has a root in the base field, so its Kummer class vanishes. -/
theorem kummer_nthPower (hn : 0 < n) (f : Kˣ) :
    kummer K n hn (f ^ n) = 0 := by
  have ha : (baseUnits K f) ^ n = baseUnits K (f ^ n) := (map_pow _ _ _).symm
  rw [kummer_eq_class K n (baseUnits K f) ha hn]
  have h : cocycle K n (baseUnits K f) ha = 0 := by
    apply _root_.GroupCohomology.ContinuousH1.Cocycle.ext
    intro g
    apply Additive.toMul.injective
    apply Subtype.ext
    change unitAction K g (baseUnits K f) / baseUnits K f = 1
    simp
  rw [h, map_zero]

/-- The degree-one Kummer construction includes every field unit and is zero. -/
@[simp] theorem kummer_level_one (f : Kˣ) : kummer K 1 (by decide) f = 0 := by
  simpa using kummer_nthPower K 1 (by decide) f

/-- Kummer as a homomorphism into additive cohomology, written multiplicatively. -/
def kummerHom (hn : 0 < n) : Kˣ →* Multiplicative (H1 G (Mu K n)) where
  toFun f := Multiplicative.ofAdd (kummer K n hn f)
  map_one' := kummer_one K n hn
  map_mul' f f' := kummer_mul K n hn f f'

/-- The additive version of the same genuine Kummer homomorphism. -/
def kummerAddHom (hn : 0 < n) : Additive Kˣ →+ H1 G (Mu K n) :=
  (kummerHom K n hn).toAdditive

@[simp] theorem kummer_inv (hn : 0 < n) (f : Kˣ) :
    kummer K n hn f⁻¹ = -kummer K n hn f :=
  (kummerHom K n hn).map_inv f

end GroupCohomology.Kummer
