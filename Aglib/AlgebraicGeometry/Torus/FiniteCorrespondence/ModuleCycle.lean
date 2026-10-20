/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportPoints
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# ModuleCycle for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `ModuleCycle.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3429225d43c9348b6a3c3a3fd40deee9795ef84498b83432ea246ef8a32dbe06`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Torus.FiniteCorrespondence
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u
variable {R : Type u} [CommRing R]

/-- The actual finite function of integral local multiplicities. -/
def coefficients [IsNoetherianRing R] (X : Object R) : FiniteDominantPrime R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun p => (coefficient X p : ℤ)) (by
    have h : Function.support (fun p => (coefficient X p : ℤ)) =
        Function.support (coefficient X) := by ext p; simp
    rw [h]
    exact coefficient_finiteSupport X)

@[simp] theorem coefficients_apply [IsNoetherianRing R] (X : Object R) (p : FiniteDominantPrime R) :
    coefficients X p = (coefficient X p : ℤ) := rfl

/-- A finite integral sum in the LITERAL free abelian group on torus prime labels. -/
def objectCycle [IsNoetherianRing R] (X : Object R) : FreeAbelianGroup (FiniteDominantPrime R) :=
  Finsupp.toFreeAbelianGroup (coefficients X)

@[simp] theorem objectCycle_coeff [IsNoetherianRing R] (X : Object R) (p : FiniteDominantPrime R) :
    FreeAbelianGroup.coeff p (objectCycle X) = (coefficient X p : ℤ) := by
  simp [FreeAbelianGroup.coeff, objectCycle]

/-- The constructed object cycle is explicitly the finite sum of its ORIGINAL
module-length coefficients. -/
theorem objectCycle_eq_finiteSum [IsNoetherianRing R] (X : Object R) :
    objectCycle X = ∑ p ∈ (objectCycle X).support,
      (coefficient X p : ℤ) • FreeAbelianGroup.of p := by
  simpa using FreeAbelianGroup.eq_sum_support_coeff_smul_of (objectCycle X)

/-- Every summand is an actual minimal component of the original support. -/
theorem objectCycle_support [IsNoetherianRing R] (X : Object R) (p : FiniteDominantPrime R)
    (hp : p ∈ (objectCycle X).support) : p.val ∈ (supportIdeal X).minimalPrimes := by
  have hn : coefficient X p ≠ 0 := by
    simpa using (FreeAbelianGroup.mem_support_iff p (objectCycle X)).mp hp
  apply pointLength_support X p
  intro hz
  apply hn
  simp [coefficient, hz]

/-- On EVERY actual minimal support component over a domain the cycle has the
accepted intrinsic multiplicity. -/
theorem objectCycle_coeff_intrinsic [IsNoetherianRing R] [IsDomain R] (X : Object R)
    (q : Ideal (Support X)) [q.IsPrime] (hq : q ∈ minimalPrimes (Support X)) :
    FreeAbelianGroup.coeff (intrinsicPoint X q hq) (objectCycle X) = (multiplicity X q : ℤ) := by
  rw [objectCycle_coeff, coefficient_intrinsicPoint]

theorem objectCycle_iso [IsNoetherianRing R] {X Y : Object R} (e : Object.Iso X Y) :
    objectCycle X = objectCycle Y := by
  apply congrArg Finsupp.toFreeAbelianGroup
  ext p
  simp [coefficient_iso e]

theorem objectCycle_sum [IsNoetherianRing R] (X Y : Object R) :
    objectCycle (X.sum Y) = objectCycle X + objectCycle Y := by
  unfold objectCycle
  rw [← map_add]
  apply congrArg Finsupp.toFreeAbelianGroup
  ext p
  simp [coefficient_sum]

/-- The two identity axes, expressed by their literal Laurent equations. -/
def OnIdentityAxis (p : FiniteDominantPrime R) : Prop :=
  firstCoordinate R - 1 ∈ p.val ∨ secondCoordinate R - 1 ∈ p.val

end AlgebraicGeometry.Torus.FiniteCorrespondence
