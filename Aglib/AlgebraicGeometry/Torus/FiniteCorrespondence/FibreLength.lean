/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.DominantFibres
public import Aglib.RingTheory.Localization.LengthSurjective
public import Aglib.RingTheory.Localization.MinimalQuotientLength

/-!
# FibreLength for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `FibreLength.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`aa294c36910a70807375aef5e2134dd081205a9618f811625891d92fffc17581`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

open _root_.Module (length_localization_of_surjective)


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

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The literal local residue fibre equals the localized quotient by the
extension of the actual contracted prime. -/
theorem residueFibreLength_eq_quotient (q : Ideal (Laurent S)) [q.IsPrime] :
    residueFibreLength (R := R) q =
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⊗[Laurent S]
          (Laurent S ⧸ (q.under (Laurent R)).map (coefficientMap (algebraMap R S)))) := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under (Laurent R)) q
  change Module.length (Localization.AtPrime q)
    (Localization.AtPrime q ⧸
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under (Laurent R)))).map
        (algebraMap (Localization.AtPrime (q.under (Laurent R))) (Localization.AtPrime q))) = _
  have hI :
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under (Laurent R)))).map
        (algebraMap (Localization.AtPrime (q.under (Laurent R))) (Localization.AtPrime q)) =
      ((q.under (Laurent R)).map (coefficientMap (algebraMap R S))).map
        (algebraMap (Laurent S) (Localization.AtPrime q)) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (q.under (Laurent R))
      (Localization.AtPrime (q.under (Laurent R))), Ideal.map_map, Ideal.map_map]
    change (q.under (Laurent R)).map
      ((algebraMap (Localization.AtPrime (q.under (Laurent R))) (Localization.AtPrime q)).comp
        (algebraMap (Laurent R) (Localization.AtPrime (q.under (Laurent R))))) =
    (q.under (Laurent R)).map
      ((algebraMap (Laurent S) (Localization.AtPrime q)).comp
        (algebraMap (Laurent R) (Laurent S)))
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  rw [hI]
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime q)
    ((q.under (Laurent R)).map (coefficientMap (algebraMap R S)))).toLinearEquiv.length_eq

/-- Finite fibre length at every target label over a finite dominant source
label, independent of a chosen original Object and its projectivity. -/
theorem dominantFibreLength_ne_top [IsNoetherianRing S] [Module.Flat R S]
    (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) (h : q.val.under (Laurent R) = p.val) :
    residueFibreLength (R := R) q.val ≠ ⊤ := by
  let := quotientBaseChange_finite (S := S) p.val
  let : IsNoetherianRing (Laurent S ⧸ p.val.map (coefficientMap (algebraMap R S))) :=
    IsNoetherianRing.of_finite S _
  have hl := Module.length_localized_quotient_ne_top _ q.val ((fibre_under_iff_minimal p q).mp h)
  rw [residueFibreLength_eq_quotient (R := R) q.val]
  have hL := congrArg (fun I : Ideal (Laurent R) =>
    Module.length (Localization.AtPrime q.val)
      (Localization.AtPrime q.val ⊗[Laurent S]
        (Laurent S ⧸ I.map (coefficientMap (algebraMap R S))))) h
  exact fun ht => hl (hL.symm.trans ht)

theorem dominantFibreMultiplicity_coe [IsNoetherianRing S] [Module.Flat R S]
    (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) (h : q.val.under (Laurent R) = p.val) :
    (residueFibreMultiplicity (R := R) q.val : ℕ∞) = residueFibreLength (R := R) q.val :=
  ENat.natCast_toNat (dominantFibreLength_ne_top p q h)

theorem dominantFibreMultiplicity_pos [IsNoetherianRing S] [Module.Flat R S]
    (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) (h : q.val.under (Laurent R) = p.val) :
    0 < residueFibreMultiplicity (R := R) q.val := by
  have hn := residueFibreLength_ne_zero (R := R) q.val
  rw [← dominantFibreMultiplicity_coe p q h] at hn
  exact_mod_cast (pos_iff_ne_zero.mpr hn)

end AlgebraicGeometry.Torus.FiniteCorrespondence
