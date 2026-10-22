/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Units over a square-zero ideal

For a square-zero ideal `I`, the actual map `x ↦ 1 + x` identifies the additive
group of `I` with the kernel of the original quotient map on units. Quotient
units lift over every nilpotent ideal. These are the local algebra inputs for
the square-zero unit sequence and the obstruction to lifting line bundles.
-/

@[expose] public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Two elements of a square-zero ideal have zero product in the original ring. -/
theorem mul_eq_zero_of_mem_of_square_zero (I : Ideal R) (hI : I ^ 2 = ⊥)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have hxy : x * y ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hx hy
  simpa only [hI, Ideal.mem_bot] using hxy

/-- The original element `1 + x`, with its explicit inverse `1 - x`. -/
def oneAddUnitOfSquareZero (I : Ideal R) (hI : I ^ 2 = ⊥) (x : I) : Rˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := by
    have hx := I.mul_eq_zero_of_mem_of_square_zero hI x.property x.property
    calc
      (1 + (x : R)) * (1 - x) = 1 - (x : R) * x := by ring
      _ = 1 := by rw [hx, sub_zero]
  inv_val := by
    have hx := I.mul_eq_zero_of_mem_of_square_zero hI x.property x.property
    calc
      (1 - (x : R)) * (1 + x) = 1 - (x : R) * x := by ring
      _ = 1 := by rw [hx, sub_zero]

@[simp]
theorem coe_oneAddUnitOfSquareZero (I : Ideal R) (hI : I ^ 2 = ⊥) (x : I) :
    (I.oneAddUnitOfSquareZero hI x : R) = 1 + x := rfl

/-- Addition in a square-zero ideal is multiplication of the original units. -/
def oneAddUnitsHom (I : Ideal R) (hI : I ^ 2 = ⊥) : Multiplicative I →* Rˣ where
  toFun x := I.oneAddUnitOfSquareZero hI x.toAdd
  map_one' := by
    apply Units.ext
    simp
  map_mul' x y := by
    apply Units.ext
    have hxy := I.mul_eq_zero_of_mem_of_square_zero hI x.toAdd.property y.toAdd.property
    change 1 + ((x.toAdd : R) + y.toAdd) =
      (1 + (x.toAdd : R)) * (1 + (y.toAdd : R))
    simp only [add_mul, mul_add, one_mul, mul_one, hxy]
    ring

@[simp]
theorem coe_oneAddUnitsHom (I : Ideal R) (hI : I ^ 2 = ⊥) (x : Multiplicative I) :
    (I.oneAddUnitsHom hI x : R) = 1 + x.toAdd := rfl

/-- Every original one-plus unit restricts to one in the quotient. -/
@[simp]
theorem quotient_map_oneAddUnitsHom (I : Ideal R) (hI : I ^ 2 = ⊥)
    (x : Multiplicative I) :
    Units.map (Ideal.Quotient.mk I : R →* R ⧸ I) (I.oneAddUnitsHom hI x) = 1 := by
  apply Units.ext
  change Ideal.Quotient.mk I (1 + (x.toAdd : R)) = 1
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr x.toAdd.property]

/-- The actual one-plus map, valued in the kernel of the original quotient map. -/
def oneAddUnitsKerHom (I : Ideal R) (hI : I ^ 2 = ⊥) :
    Multiplicative I →* (Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)).ker :=
  (I.oneAddUnitsHom hI).codRestrict _ fun x => I.quotient_map_oneAddUnitsHom hI x

/-- The one-plus map identifies the additive ideal with the actual unit kernel. -/
noncomputable def oneAddUnitsKerEquiv (I : Ideal R) (hI : I ^ 2 = ⊥) :
    Multiplicative I ≃* (Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)).ker := by
  apply MulEquiv.ofBijective (I.oneAddUnitsKerHom hI)
  constructor
  · intro x y hxy
    have h := congrArg Units.val (congrArg Subtype.val hxy)
    change 1 + (x.toAdd : R) = 1 + (y.toAdd : R) at h
    exact Multiplicative.toAdd.injective (Subtype.ext (add_left_cancel h))
  · intro u
    have hu : Ideal.Quotient.mk I (u.val : R) = 1 :=
      congrArg (fun v : (R ⧸ I)ˣ => (v : R ⧸ I)) u.property
    let x : I := ⟨(u.val : R) - 1, (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp hu⟩
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change 1 + ((u.val : R) - 1) = (u.val : R)
    ring

@[simp]
theorem coe_oneAddUnitsKerEquiv (I : Ideal R) (hI : I ^ 2 = ⊥)
    (x : Multiplicative I) :
    ((I.oneAddUnitsKerEquiv hI x : Rˣ) : R) = 1 + x.toAdd := rfl

/-- The original one-plus units commute with every ideal-preserving ring map. -/
theorem map_oneAddUnitOfSquareZero (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hI : I ^ 2 = ⊥) (hJ : J ^ 2 = ⊥) (h : I ≤ J.comap f) (x : I) :
    Units.map (f : R →* S) (I.oneAddUnitOfSquareZero hI x) =
      J.oneAddUnitOfSquareZero hJ ⟨f x, h x.property⟩ := by
  apply Units.ext
  change f (1 + (x : R)) = 1 + f x
  rw [map_add, map_one]

/-- Quotient units lift over a nilpotent ideal, through the original map on units. -/
theorem units_quotient_map_surjective (I : Ideal R) (hI : IsNilpotent I) :
    Function.Surjective (Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)) := by
  intro u
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : R ⧸ I)
  have hunit : IsUnit x := hI.isUnit_quotient_mk_iff.mp (hx.symm ▸ u.isUnit)
  refine ⟨hunit.unit, ?_⟩
  apply Units.ext
  change Ideal.Quotient.mk I (hunit.unit : R) = (u : R ⧸ I)
  rw [hunit.unit_spec, hx]

end Ideal

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- One-plus units in the ring kernel, valued in the kernel of the original
map on units. Surjectivity of the ring map is not required. -/
def oneAddUnitsKerHom (f : R →+* S) (hf : RingHom.ker f ^ 2 = ⊥) :
    Multiplicative (RingHom.ker f) →* (Units.map (f : R →* S)).ker :=
  ((RingHom.ker f).oneAddUnitsHom hf).codRestrict _ fun x => by
    apply Units.ext
    change f (1 + (x.toAdd : R)) = 1
    rw [map_add, map_one, show f (x.toAdd : R) = 0 from x.toAdd.property, add_zero]

/-- The additive ring kernel is canonically the kernel of the original map on
units whenever the ring kernel is square zero. -/
noncomputable def oneAddUnitsKerEquiv (f : R →+* S) (hf : RingHom.ker f ^ 2 = ⊥) :
    Multiplicative (RingHom.ker f) ≃* (Units.map (f : R →* S)).ker := by
  apply MulEquiv.ofBijective (f.oneAddUnitsKerHom hf)
  constructor
  · intro x y hxy
    have h := congrArg Units.val (congrArg Subtype.val hxy)
    change 1 + (x.toAdd : R) = 1 + (y.toAdd : R) at h
    exact Multiplicative.toAdd.injective (Subtype.ext (add_left_cancel h))
  · intro u
    have hu : f (u.val : R) = 1 :=
      congrArg (fun v : Sˣ => (v : S)) u.property
    let x : RingHom.ker f := ⟨(u.val : R) - 1, by
      change f ((u.val : R) - 1) = 0
      rw [map_sub, map_one, hu, sub_self]⟩
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change 1 + ((u.val : R) - 1) = (u.val : R)
    ring

@[simp]
theorem coe_oneAddUnitsKerEquiv (f : R →+* S) (hf : RingHom.ker f ^ 2 = ⊥)
    (x : Multiplicative (RingHom.ker f)) :
    ((f.oneAddUnitsKerEquiv hf x : Rˣ) : R) = 1 + x.toAdd := rfl

/-- Exactness uses the literal ring map and the literal one-plus units. -/
theorem oneAddUnitsHom_mulExact (f : R →+* S) (hf : RingHom.ker f ^ 2 = ⊥) :
    Function.MulExact ((RingHom.ker f).oneAddUnitsHom hf)
      (Units.map (f : R →* S)) := by
  intro u
  constructor
  · intro hu
    obtain ⟨x, hx⟩ := (f.oneAddUnitsKerEquiv hf).surjective ⟨u, hu⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, rfl⟩
    exact (f.oneAddUnitsKerHom hf x).property

/-- The original one-plus map into units is injective. -/
theorem oneAddUnitsHom_injective (f : R →+* S) (hf : RingHom.ker f ^ 2 = ⊥) :
    Function.Injective ((RingHom.ker f).oneAddUnitsHom hf) := by
  intro x y hxy
  apply (f.oneAddUnitsKerEquiv hf).injective
  exact Subtype.ext hxy

/-- Subtracting one on the original unit kernel is an additive homomorphism. -/
noncomputable def unitsKerSubOneHom (f : R →+* S) (hf : RingHom.ker f ^ 2 = ⊥) :
    Additive (Units.map (f : R →* S)).ker →+ RingHom.ker f where
  toFun x := ((f.oneAddUnitsKerEquiv hf).symm x.toMul).toAdd
  map_zero' := congrArg Multiplicative.toAdd (map_one (f.oneAddUnitsKerEquiv hf).symm)
  map_add' x y := congrArg Multiplicative.toAdd
    (map_mul (f.oneAddUnitsKerEquiv hf).symm x.toMul y.toMul)

@[simp]
theorem coe_unitsKerSubOneHom (f : R →+* S) (hf : RingHom.ker f ^ 2 = ⊥)
    (x : Additive (Units.map (f : R →* S)).ker) :
    (f.unitsKerSubOneHom hf x : R) = ((x.toMul : Rˣ) : R) - 1 := by
  have h := congrArg (fun q : (Units.map (f : R →* S)).ker => ((q : Rˣ) : R))
    ((f.oneAddUnitsKerEquiv hf).apply_symm_apply x.toMul)
  change 1 + (f.unitsKerSubOneHom hf x : R) = ((x.toMul : Rˣ) : R) at h
  rw [← h]
  ring

/-- Lifting a unit and its inverse suffices to lift invertibility over a
square-zero kernel; no surjectivity on all ring sections is assumed. -/
theorem isUnit_of_unit_and_inv_lift (f : R →+* S) (hf : RingHom.ker f ^ 2 = ⊥)
    (u : Sˣ) {x y : R} (hx : f x = (u : S)) (hy : f y = (u⁻¹ : Sˣ)) :
    IsUnit x := by
  have hmem : x * y - 1 ∈ RingHom.ker f := by
    change f (x * y - 1) = 0
    rw [map_sub, map_mul, map_one, hx, hy, u.mul_inv, sub_self]
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by
    simpa only [pow_two] using
      (RingHom.ker f).mul_eq_zero_of_mem_of_square_zero hf hmem hmem⟩
  have hunit : IsUnit (x * y) := by
    simpa only [sub_add_cancel] using hnil.isUnit_add_one
  exact (IsUnit.mul_iff.mp hunit).1

end RingHom
