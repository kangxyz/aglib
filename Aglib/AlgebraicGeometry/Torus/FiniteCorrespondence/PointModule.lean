/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.FlatMultiplicity
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.ModuleCycle
public import Aglib.RingTheory.Length.PrimeQuotient

/-!
# PointModule for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `PointModule.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`18784b00f5df23bfbca370b924c6174e090f709cbe72d1e79ca944401b5b57fa`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct AlgebraMonoidAlgebra
namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u
variable {K : Type u} [Field K]

/-- The literal quotient algebra of the finite prime label. -/
abbrev PointAlgebra (p : FiniteDominantPrime K) := Laurent K ⧸ p.val

/-- Every character acts on the literal quotient by multiplication by a unit. -/
def pointCharacter (p : FiniteDominantPrime K) : Character →* (PointAlgebra p ≃ₗ[K] PointAlgebra
    p) :=
  (Units.mulLeftLinearEquiv K (PointAlgebra p)).comp
    (((Ideal.Quotient.mk p.val).toMonoidHom.comp (MonoidAlgebra.of K Character)).toHomUnits)

@[simp] theorem pointCharacter_apply (p : FiniteDominantPrime K) (m : Character) (x :
    PointAlgebra p) :
    pointCharacter p m x = Ideal.Quotient.mk p.val (MonoidAlgebra.single m 1) * x := rfl

/-- A genuine original Object K attached to a finite prime label, with no
supplied support or coefficient equation. -/
def pointObject (p : FiniteDominantPrime K) : Object K where
  carrier := PointAlgebra p
  a := pointCharacter p (Multiplicative.ofAdd (1, 0))
  b := pointCharacter p (Multiplicative.ofAdd (0, 1))
  commute x := by simp only [pointCharacter_apply]; exact mul_left_comm _ _ _

theorem pointObject_exponent (p : FiniteDominantPrime K) (m : Character) :
    exponentAction (pointObject p) m = pointCharacter p m := by
  change pointCharacter p (Multiplicative.ofAdd (1, 0)) ^ m.toAdd.1 *
    pointCharacter p (Multiplicative.ofAdd (0, 1)) ^ m.toAdd.2 = _
  rw [← map_zpow (pointCharacter p), ← map_zpow (pointCharacter p), ← map_mul]
  congr 1
  apply (Multiplicative.toAdd : Character ≃ ℤ × ℤ).injective
  ext <;> simp

/-- The complete original Laurent action is quotient multiplication. -/
theorem representation_pointObject (p : FiniteDominantPrime K) (a : Laurent K) (x : PointAlgebra
    p) :
    representation (pointObject p) a x = Ideal.Quotient.mk p.val a * x := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_mul]
  | single m r =>
    rw [representation_single]
    change r • (exponentAction (pointObject p) m) x = _
    rw [pointObject_exponent]
    change r • (Ideal.Quotient.mk p.val (MonoidAlgebra.single m 1) * x) = _
    rw [← smul_mul_assoc]
    congr 1
    change r • (Ideal.Quotient.mkₐ K p.val) (MonoidAlgebra.single m 1) =
      (Ideal.Quotient.mkₐ K p.val) (MonoidAlgebra.single m r)
    rw [← map_smul]
    congr 1
    simp

/-- The actual annihilator of the point object equals the supplied prime. -/
theorem supportIdeal_pointObject (p : FiniteDominantPrime K) : supportIdeal (pointObject p) =
    p.val := by
  ext a
  change representation (pointObject p) a = 0 ↔ a ∈ p.val
  constructor
  · intro h
    have h1 := LinearMap.congr_fun h (1 : PointAlgebra p)
    rw [representation_pointObject, mul_one] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  · intro h
    ext x
    rw [representation_pointObject, Ideal.Quotient.eq_zero_iff_mem.mpr h, zero_mul]
    rfl

/-- Identity on the literal carrier identifies its constructed Laurent action
with the ordinary quotient module action. -/
def pointObjectLaurentEquiv (p : FiniteDominantPrime K) :
    Realization (pointObject p) ≃ₗ[Laurent K] PointAlgebra p where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl
  map_smul' a x := representation_pointObject p a x

/-- The local length at the represented prime is one, proved by identifying
the localized original module with the local ring's residue field. -/
theorem ambientLength_pointObject_self (p : FiniteDominantPrime K) :
    ambientLength (pointObject p) p.val = 1 := by
  let : CommRing (Localization.AtPrime p.val) := inferInstance
  let : AddCommGroup (LocalRealization (pointObject p) p.val) := inferInstance
  let : AddCommGroup (Localization.AtPrime p.val ⊗[Laurent K] PointAlgebra p) := inferInstance
  let e : LocalRealization (pointObject p) p.val ≃ₗ[Localization.AtPrime p.val]
      Localization.AtPrime p.val ⊗[Laurent K] PointAlgebra p :=
    (pointObjectLaurentEquiv p).baseChange (Laurent K) (Localization.AtPrime p.val) _ _
  change Module.length (Localization.AtPrime p.val) (LocalRealization (pointObject p) p.val) = 1
  rw [e.length_eq]
  exact Module.primeQuotient_local_length p.val

@[simp] theorem coefficient_pointObject_self (p : FiniteDominantPrime K) : coefficient
    (pointObject p) p = 1 := by
  simp [coefficient, ambientLength_pointObject_self]

open Classical in
/-- The point object has no coefficient at any distinct actual cycle label. -/
theorem coefficient_pointObject (p r : FiniteDominantPrime K) :
    coefficient (pointObject p) r = if r = p then 1 else 0 := by
  classical
  by_cases h : r = p
  · subst r; simp
  · rw [ite_eq_right h]
    by_contra hn
    have hr := pointLength_support (pointObject p) r
      ((ambientLength_ne_zero_iff (pointObject p) r.val).mpr
        ((coefficient_ne_zero_iff (pointObject p) r).mp hn))
    rw [supportIdeal_pointObject, Ideal.minimalPrimes_eq_subsingleton_self] at hr
    exact h (Subtype.ext (Set.mem_singleton_iff.mp hr))

/-- Equality of actual finite cycles may be checked at every ordinary prime label. -/
theorem cycle_eq_of_coeff_eq {R : Type u} [CommRing R]
    {a b : FreeAbelianGroup (FiniteDominantPrime R)}
    (h : ∀ p, FreeAbelianGroup.coeff p a = FreeAbelianGroup.coeff p b) : a = b := by
  apply (FreeAbelianGroup.equivFinsupp (FiniteDominantPrime R)).injective
  ext p
  exact h p

/-- The point object realizes exactly the original free prime generator. -/
theorem objectCycle_pointObject (p : FiniteDominantPrime K) : objectCycle (pointObject p) =
    FreeAbelianGroup.of p := by
  classical
  apply cycle_eq_of_coeff_eq
  intro r
  rw [objectCycle_coeff, coefficient_pointObject]
  by_cases h : r = p
  · subst r; simp [FreeAbelianGroup.coeff]
  · simp [h, FreeAbelianGroup.coeff]

end AlgebraicGeometry.Torus.FiniteCorrespondence
