/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.MultiplicationCone
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The zero-differential units complex

A single nonzero units group in degree two gives explicit integral and finite-coefficient
classes and their connecting map. Identification with any external cohomology theory is
a separate input to a downstream application.

Source: `lean/R5Lab/Aglib/Algebra/Homology/UnitsComplex.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `4b8af4b3f67c445d6710aab3f56296ea502d2485c3c1cd2ddaa8a3718349f9b9`.
-/

@[expose] public section

namespace AddCommGrpCat.UnitsComplex
noncomputable section
variable (K : Type*) [Field K]

/-- The units complex, shifted so its sole term lies in degree two. -/
def lowDegree : AddCommGrpCat.MultiplicationCone.Complex
    PUnit.{1} PUnit.{1} (Additive Kˣ) PUnit.{1} where
  d₀ := 0
  d₁ := 0
  d₂ := 0
  d₁_d₀ _ := rfl
  d₂_d₁ _ := rfl

abbrev H2 := (lowDegree K).H₂
abbrev H1mod (n : ℕ) := (lowDegree K).H₁mod n

/-- The inclusion of actual field units as integral cohomology classes. -/
def unitClass : Additive Kˣ →+ H2 K where
  toFun a := (lowDegree K).class₂ ⟨a, rfl⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Projection of the zero-differential cohomology back to actual units. -/
def unitValue : H2 K →+ Additive Kˣ :=
  QuotientAddGroup.lift _ (lowDegree K).d₂.ker.subtype (by
    rintro x ⟨a, rfl⟩
    rfl)

@[simp] theorem unitValue_unitClass (a : Additive Kˣ) :
    unitValue K (unitClass K a) = a := rfl

@[simp] theorem unitClass_unitValue (a : H2 K) :
    unitClass K (unitValue K a) = a := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (lowDegree K).boundary₂.range a
  rfl

/-- The explicit integral identification, with inverse actual unit class. -/
def unitEquiv : H2 K ≃+ Additive Kˣ where
  toFun := unitValue K
  invFun := unitClass K
  left_inv := unitClass_unitValue K
  right_inv := unitValue_unitClass K
  map_add' := map_add _

/-- The finite-coefficient class of an actual n-th root of unity. -/
def rootCocycle (n : ℕ) (z : rootsOfUnity n K) : (lowDegree K).Cocycles n :=
  ⟨(0, Additive.ofMul (z : Kˣ)), by
    constructor
    · change (0 : Additive Kˣ) = n • Additive.ofMul (z : Kˣ)
      apply Additive.toMul.injective
      exact z.property.symm
    · rfl⟩

def rootClass (n : ℕ) (z : rootsOfUnity n K) : H1mod K n :=
  (lowDegree K).classMod n (rootCocycle K n z)

/-- Root normalization for the actual units coefficient complex, computed
straight from the cone projection. -/
theorem beta_root (n : ℕ) (z : rootsOfUnity n K) :
    unitValue K ((lowDegree K).beta n (rootClass K n z)) = Additive.ofMul (z : Kˣ) := rfl

/-- The same computation before identifying integral cohomology with units. -/
theorem beta_root_class (n : ℕ) (z : rootsOfUnity n K) :
    (lowDegree K).beta n (rootClass K n z) = unitClass K (Additive.ofMul (z : Kˣ)) := rfl

end
end AddCommGrpCat.UnitsComplex


namespace AddCommGrpCat.UnitsComplex
noncomputable section
universe u
variable (K : Type u) [Field K]

theorem units_rootClass_mul (n : ℕ) (z w : rootsOfUnity n K) :
    UnitsComplex.rootClass K n (z*w) =
      UnitsComplex.rootClass K n z + UnitsComplex.rootClass K n w := by
  change (UnitsComplex.lowDegree K).classMod n (UnitsComplex.rootCocycle K n (z*w)) =
    (UnitsComplex.lowDegree K).classMod n (UnitsComplex.rootCocycle K n z) +
      (UnitsComplex.lowDegree K).classMod n (UnitsComplex.rootCocycle K n w)
  rw [← map_add]
  congr 1

theorem units_rootClass_one (n : ℕ) : UnitsComplex.rootClass K n 1 = 0 := by
  have h : UnitsComplex.rootCocycle K n 1 = 0 := by
    apply Subtype.ext
    rfl
  change (UnitsComplex.lowDegree K).classMod n (UnitsComplex.rootCocycle K n 1) = 0
  rw [h, map_zero]

end
end AddCommGrpCat.UnitsComplex

namespace AddCommGrpCat.UnitsComplex
noncomputable section
universe u
variable {K : Type u} [Field K]

/-- Injectivity of the explicit units-complex boundary follows on its cocycles. -/
theorem units_beta_injective (n : ℕ) :
    Function.Injective ((UnitsComplex.lowDegree K).beta n) := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective ((UnitsComplex.lowDegree K).boundary n).range x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective ((UnitsComplex.lowDegree K).boundary n).range y
  have hv := congrArg (UnitsComplex.unitValue K) h
  change a.val.2 = b.val.2 at hv
  congr 1
  apply Subtype.ext
  exact Prod.ext (Subsingleton.elim _ _) hv

end
end AddCommGrpCat.UnitsComplex
