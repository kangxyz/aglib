/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.SimplexFieldFaces
public import Aglib.RingTheory.Length.PrimeQuotient

/-!
# SimplexFunctoriality for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `SimplexFunctoriality.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`0cd6dc588dfc1a17ff935a6893a59ba74f513cb743627e326f22df3f6f5d1c25`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped AlgebraMonoidAlgebra TensorProduct
namespace AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
universe u

theorem quotientFor_id {R : Type u} [CommRing R] [IsNoetherianRing R] :
    quotientFibreCycleMapFor (RingHom.id R) =
      AddMonoidHom.id (FreeAbelianGroup (FiniteDominantPrime R)) := by
  classical
  apply FreeAbelianGroup.lift_ext
  intro p
  apply (FreeAbelianGroup.equivFinsupp _).injective
  ext q
  let := (RingHom.id R).toAlgebra
  change FreeAbelianGroup.coeff q (quotientFibreCycleMap (FreeAbelianGroup.of p)) =
    FreeAbelianGroup.coeff q (FreeAbelianGroup.of p)
  rw [quotientFibreCycleMap_of_coeff]
  have hmap : coefficientMap (RingHom.id R) = RingHom.id (Laurent R) :=
    MonoidAlgebra.mapRingHom_id
  by_cases h : p = q
  · subst q
    have hl : quotientFibreLength (S := R) p p = 1 := by
      change Module.length (Localization.AtPrime p.val)
        (Localization.AtPrime p.val ⊗[Laurent R]
          (Laurent R ⧸ p.val.map (coefficientMap (RingHom.id R)))) = 1
      rw [hmap, Ideal.map_id]
      exact Module.primeQuotient_local_length p.val
    simp [quotientFibreMultiplicity, hl, FreeAbelianGroup.coeff]
  · have hz : quotientFibreLength (S := R) p q = 0 := by
      by_contra hn
      have hle := (quotientFibreLength_ne_zero_iff p q).mp hn
      change p.val.map (coefficientMap (RingHom.id R)) ≤ q.val at hle
      rw [hmap, Ideal.map_id] at hle
      have hm := minimal_of_finite_quotient_le p.val q.val q.under_eq_bot hle
      rw [Ideal.minimalPrimes_eq_subsingleton_self] at hm
      exact h (Subtype.ext (Set.mem_singleton_iff.mp hm).symm)
    simp [quotientFibreMultiplicity, hz, FreeAbelianGroup.coeff, h]

variable {K L M : Type u} [Field K] [Field L] [Field M]

theorem simplexFieldPullback_id (d : ℕ) :
    simplexFieldPullback (RingHom.id K) d =
      AddMonoidHom.id (FreeAbelianGroup (FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K
        d))) := by
  rw [simplexFieldPullback_eq_quotientFor, AlgebraicSimplex.coefficientMap_id]
  exact quotientFor_id

theorem simplexFieldPullback_of_coeff (f : K →+* L) (d : ℕ)
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing K d))
    (q : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing L d)) :
    FreeAbelianGroup.coeff q (simplexFieldPullback f d (FreeAbelianGroup.of p)) =
      ((Module.length (Localization.AtPrime q.val)
        (Localization.AtPrime q.val ⊗[Laurent (AlgebraicSimplex.CoordinateRing L d)]
          (Laurent (AlgebraicSimplex.CoordinateRing L d) ⧸
            p.val.map (coefficientMap (AlgebraicSimplex.coefficientMap f d))))).toNat : ℤ) := by
  rw [simplexFieldPullback_eq_quotientFor]
  let := (AlgebraicSimplex.coefficientMap f d).toAlgebra
  exact quotientFibreCycleMap_of_coeff p q

theorem simplexFieldPullback_comp (f : K →+* L) (g : L →+* M) (d : ℕ) :
    (simplexFieldPullback g d).comp (simplexFieldPullback f d) =
      simplexFieldPullback (g.comp f) d := by
  apply FreeAbelianGroup.lift_ext
  intro p
  apply (FreeAbelianGroup.equivFinsupp _).injective
  ext q
  simp only [AddMonoidHom.comp_apply, simplexFieldPullback_eq_quotientFor]
  change FreeAbelianGroup.coeff q
      (quotientFibreCycleMapFor (AlgebraicSimplex.coefficientMap g d)
        (quotientFibreCycleMapFor (AlgebraicSimplex.coefficientMap f d) (FreeAbelianGroup.of p))) =
    FreeAbelianGroup.coeff q
      (quotientFibreCycleMapFor (AlgebraicSimplex.coefficientMap (g.comp f) d)
        (FreeAbelianGroup.of p))
  let := (AlgebraicSimplex.coefficientMap f d).toAlgebra
  let : Module.Flat (AlgebraicSimplex.CoordinateRing K d)
      (AlgebraicSimplex.CoordinateRing L d) := AlgebraicSimplex.coefficientMap_flat f d
  have hdom : ∀ Q ∈ (p.val.map
      (coefficientMap (AlgebraicSimplex.coefficientMap f d))).minimalPrimes,
      Q.under (AlgebraicSimplex.CoordinateRing L d) = ⊥ := by
    exact fun Q hQ => minimalFibre_dominant p Q hQ
  rw [flat_second_coeffFor _ _ (AlgebraicSimplex.coefficientMap_flat g d) p hdom q]
  let := (AlgebraicSimplex.coefficientMap (g.comp f) d).toAlgebra
  change ((compositeLength (AlgebraicSimplex.coefficientMap f d)
    (AlgebraicSimplex.coefficientMap g d) p q).toNat : ℤ) =
      FreeAbelianGroup.coeff q (quotientFibreCycleMap (FreeAbelianGroup.of p))
  rw [quotientFibreCycleMap_of_coeff]
  change ((compositeLength (AlgebraicSimplex.coefficientMap f d)
    (AlgebraicSimplex.coefficientMap g d) p q).toNat : ℤ) =
      ((quotientFibreLength p q).toNat : ℤ)
  congr 2
  unfold compositeLength quotientFibreLength
  rw [mappedIdeal_comp, AlgebraicSimplex.coefficientMap_comp]
  rfl

end AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange
