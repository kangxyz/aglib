/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The rank at a prime from the residue field

`Module.rankAtStalk_eq_finrank_of_extendScalars_iso`: for a finite flat module `H` over `R` and a
prime `p`, an isomorphism of the scalar extension `κ(p) ⊗_R H` with a `κ(p)`-module `N` gives
`rankAtStalk H p = dim_{κ(p)} N`. It is `Module.rankAtStalk_baseChange` at the unique prime of
`κ(p)`, which lies over `p`.
-/

@[expose] public section

universe u v

namespace Module

/-- **The rank at a prime from the fiber**: for a finite flat module `H` over `R`, a prime `p` and
an isomorphism of `(R →+* κ(p))`-scalar extension of `H` with a `κ(p)`-module `N`,
`rankAtStalk H p = dim_{κ(p)} N`. -/
theorem rankAtStalk_eq_finrank_of_extendScalars_iso {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (H : ModuleCat.{max u v} R) [Module.Flat R H] [Module.Finite R H]
    (N : ModuleCat.{max u v} p.asIdeal.ResidueField)
    (e : (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).obj H ≅ N) :
    Module.rankAtStalk (R := R) H p = Module.finrank p.asIdeal.ResidueField N := by
  let κ := p.asIdeal.ResidueField
  let q : PrimeSpectrum κ := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : q.comap (algebraMap R κ) = p := by
    ext1
    change Ideal.comap (algebraMap R κ) ⊥ = p.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  have h := Module.rankAtStalk_baseChange (R := R) (M := H) (S := κ) q
  rw [hq] at h
  rw [← h]
  simp only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id]
  exact ((ModuleCat.extendScalarsAlgebraObjIso R κ H).symm ≪≫ e).toLinearEquiv.finrank_eq

end Module
