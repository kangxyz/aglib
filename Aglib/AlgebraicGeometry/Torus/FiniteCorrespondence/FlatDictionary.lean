/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.FlatPullback
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PrincipalFibres

/-!
# FlatDictionary for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `FlatDictionary.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`aa7746ebff915145ac6df8dfb9ae601a826f7d2482d2ce35fafdc6c93841bd1d`.

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
namespace AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u
section NativeFlatDictionary
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat R S] [IsNoetherianRing S]

omit [IsNoetherianRing S] in
open Classical in
/-- On a flat coefficient extension, the ordinary fibre length is precisely
the native contracted-prime residue length, including zero off that fibre. -/
theorem quotientLength_eq_residue_if (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) :
    quotientFibreLength (S := S) p q =
      if q.val.under (Laurent R) = p.val then residueFibreLength (R := R) q.val else 0 := by
  by_cases h : q.val.under (Laurent R) = p.val
  · rw [ite_eq_left h, residueFibreLength_eq_quotient, h]
    rfl
  · rw [ite_eq_right h]
    by_contra hn
    have hle := (quotientFibreLength_ne_zero_iff p q).mp hn
    let := quotientBaseChange_finite (S := S) p.val
    exact h (minimalFibre_under p q.val
      (minimal_of_finite_quotient_le _ q.val q.under_eq_bot hle))

theorem quotientCycle_eq_flatPullback :
    quotientFibreCycleMap (R := R) (S := S) = flatPullback (R := R) (S := S) := by
  classical
  apply FreeAbelianGroup.lift_ext
  intro p
  apply (FreeAbelianGroup.equivFinsupp _).injective
  ext q
  change FreeAbelianGroup.coeff q (quotientFibreCycleMap (FreeAbelianGroup.of p)) =
    FreeAbelianGroup.coeff q (flatPullback (FreeAbelianGroup.of p))
  rw [quotientFibreCycleMap_of_coeff, flatPullback_of_coeff]
  by_cases h : q.val.under (Laurent R) = p.val
  all_goals simp [quotientFibreMultiplicity, quotientLength_eq_residue_if,
    residueFibreMultiplicity, h]
end NativeFlatDictionary

end AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange
