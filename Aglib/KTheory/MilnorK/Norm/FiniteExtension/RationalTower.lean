/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Tower
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalFunction

/-!
# Actual rational coefficient norms and their towers

The rational-function norm used in the proved residue diagrams is exactly the
actual finite-extension norm. General norm transitivity therefore applies to
literal coefficient-field towers, not to an assumed rational norm system.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue PolynomialNorm
open scoped RatFunc

attribute [local instance] Polynomial.algebra

universe u

/-- Rational coefficient extension preserves the original finite degree. -/
local instance rationalFinite {k E : Type u} [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] : FiniteDimensional (RatFunc k) (RatFunc E) :=
  FiniteDimensional.of_finrank_pos (by
    rw [RatFunc.finrank_ratFunc_ratFunc]
    exact Module.finrank_pos)

local instance rationalRootFinite {k : Type u} [Field k] (p : MonicIrreducible k) :
    FiniteDimensional k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

/-- The original rational norm in the residue squares is the actual finite
norm on the original rational-function field, with no change of field map. -/
theorem rationalFunctionNorm_eq_finiteExtensionNorm
    {k : Type u} [Field k] [CharZero k] (p : MonicIrreducible k) (n : ℕ) :
    rationalFunctionNorm n p = finiteExtensionNorm (RatFunc k) (RatFunc (AdjoinRoot p.val)) n := by
  rw [finiteExtensionNorm_eq_presentation _ _ n (rationalCoefficientPolynomial p)
    (AdjoinRoot.rationalCoefficientAlgEquiv p.val p.property.1)]
  rfl

/-- The original rational coefficient tower has exactly its native scalar maps. -/
theorem rationalCoefficientScalarTower
    {k L E : Type u} [Field k] [Field L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E] :
    @IsScalarTower (RatFunc k) (RatFunc L) (RatFunc E)
      (inferInstance : Algebra (RatFunc k) (RatFunc L)).toSMul
      (inferInstance : Algebra (RatFunc L) (RatFunc E)).toSMul
      (inferInstance : Algebra (RatFunc k) (RatFunc E)).toSMul := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
  apply RingHom.ext
  intro f
  simp only [RingHom.comp_apply, ratFunc_algebraMap_eq_fractionMap,
    fractionMap_polynomial, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

/-- Actual rational norms compose along arbitrary original finite coefficient
field towers; this is a direct consumer of general finite norm transitivity. -/
theorem finiteExtensionNorm_rational_tower
    {k : Type u} [Field k] [CharZero k] (L E : Type u)
    [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E] (n : ℕ) :
    finiteExtensionNorm (RatFunc k) (RatFunc E) n =
      (finiteExtensionNorm (RatFunc k) (RatFunc L) n).comp
        (finiteExtensionNorm (RatFunc L) (RatFunc E) n) := by
  let := rationalCoefficientScalarTower (k := k) (L := L) (E := E)
  exact finiteExtensionNorm_tower_comp (RatFunc L) (RatFunc E) n

end MilnorK
