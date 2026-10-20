/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.AlgebraicSimplex.FieldBaseChange
public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportPoints
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.SimplexFunctoriality
public import Aglib.AlgebraicGeometry.AlgebraicSimplex.CoefficientEquiv
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# ScalarTransport for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `ScalarTransport.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`a331afe1ad9a607965773aa8c0717adea095009cc12636d4aa063c309d9c8085`.

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
namespace AlgebraicGeometry.Torus.FiniteCorrespondence.ScalarTransport
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport
open CategoryTheory
universe u
variable {L : Type u} [Field L]

/-- The semilinear quotient map induced by applying `e` to simplex coefficients and Laurent
coefficients. -/
def quotientTransportSemilinear (e : L ≃+* L) (d : ℕ)
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing L d)) :
    (Laurent (AlgebraicSimplex.CoordinateRing L d) ⧸ p.val)
      →ₛₗ[(AlgebraicSimplex.coefficientEquiv e d).toRingHom]
      (Laurent (AlgebraicSimplex.CoordinateRing L d) ⧸ p.val.map
        (AlgebraicSimplex.laurentCoefficientEquiv e d)) := by
  let f : Laurent (AlgebraicSimplex.CoordinateRing L d)
      →ₛₗ[(AlgebraicSimplex.coefficientEquiv e d).toRingHom]
        Laurent (AlgebraicSimplex.CoordinateRing L d) :=
    { toFun := AlgebraicSimplex.laurentCoefficientEquiv e d
      map_add' := (AlgebraicSimplex.laurentCoefficientEquiv e d).map_add
      map_smul' := by
        intro r x
        exact AlgebraicSimplex.laurentCoefficientEquiv_smul e d r x }
  exact (p.val.restrictScalars (AlgebraicSimplex.CoordinateRing L d)).mapQ
    ((p.val.map (AlgebraicSimplex.laurentCoefficientEquiv e d)).restrictScalars
      (AlgebraicSimplex.CoordinateRing L d)) f
    (by intro x hx; exact Ideal.mem_map_of_mem (AlgebraicSimplex.laurentCoefficientEquiv e d) hx)

/-- The finite dominant prime label transported by the simplex Laurent coefficient equivalence
induced by `e`. -/
def pointTransport (e : L ≃+* L) (d : ℕ)
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing L d)) :
    FiniteDominantPrime (AlgebraicSimplex.CoordinateRing L d) := by
  let I : Ideal (Laurent (AlgebraicSimplex.CoordinateRing L d)) :=
    p.val.map (AlgebraicSimplex.laurentCoefficientEquiv e d)
  let : I.IsPrime := Ideal.map_isPrime_of_equiv _
  refine ⟨I, inferInstance, ?_, ?_⟩
  · apply Module.Finite.of_surjective (quotientTransportSemilinear e d p)
    intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective I y
    refine ⟨Submodule.Quotient.mk ((AlgebraicSimplex.laurentCoefficientEquiv e d).symm a), ?_⟩
    change Submodule.Quotient.mk ((AlgebraicSimplex.laurentCoefficientEquiv e d)
      ((AlgebraicSimplex.laurentCoefficientEquiv e d).symm a)) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  · ext r
    rw [Ideal.mem_bot]
    change algebraMap _ _ r ∈ I ↔ r = 0
    constructor
    · intro hr
      have he : AlgebraicSimplex.laurentCoefficientEquiv e d (algebraMap _ _
        ((AlgebraicSimplex.coefficientEquiv e d).symm r)) =
          algebraMap _ _ r := by
        rw [AlgebraicSimplex.laurentCoefficientEquiv_algebraMap,
          RingEquiv.apply_symm_apply]
      have hm : algebraMap _ _ ((AlgebraicSimplex.coefficientEquiv e d).symm r)
        ∈ p.val :=
        Ideal.apply_mem_of_equiv_iff.mp (he.symm ▸ hr)
      change (AlgebraicSimplex.coefficientEquiv e d).symm r ∈ p.val.under
        (AlgebraicSimplex.CoordinateRing L d) at hm
      rw [MonoidAlgebra.FiniteDominantPrime.under_eq_bot, Ideal.mem_bot] at hm
      simpa using congrArg (AlgebraicSimplex.coefficientEquiv e d) hm
    · rintro rfl
      simp

@[simp] theorem pointTransport_val (e : L ≃+* L) (d : ℕ)
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing L d)) :
    (pointTransport e d p).val =
      p.val.map (coefficientMap (AlgebraicSimplex.coefficientMap e.toRingHom d)) := rfl

open AlgebraicGeometry.Torus.FiniteCorrespondence.BaseChange

theorem simplexFieldPullback_of_automorphism (e : L ≃+* L) (d : ℕ)
    (p : FiniteDominantPrime (AlgebraicSimplex.CoordinateRing L d)) :
    simplexFieldPullback e.toRingHom d (FreeAbelianGroup.of p) =
      FreeAbelianGroup.of (pointTransport e d p) := by
  classical
  apply (FreeAbelianGroup.equivFinsupp _).injective
  ext q
  change FreeAbelianGroup.coeff q
    (simplexFieldPullback e.toRingHom d (FreeAbelianGroup.of p)) =
      FreeAbelianGroup.coeff q (FreeAbelianGroup.of (pointTransport e d p))
  rw [simplexFieldPullback_of_coeff]
  by_cases h : q = pointTransport e d p
  · subst q
    have hl : Module.length (Localization.AtPrime (pointTransport e d p).val)
        (Localization.AtPrime (pointTransport e d p).val ⊗[Laurent
          (AlgebraicSimplex.CoordinateRing L d)]
          (Laurent (AlgebraicSimplex.CoordinateRing L d) ⧸
            p.val.map (coefficientMap (AlgebraicSimplex.coefficientMap e.toRingHom d)))) = 1 := by
      change Module.length (Localization.AtPrime (pointTransport e d p).val)
        (Localization.AtPrime (pointTransport e d p).val ⊗[Laurent
          (AlgebraicSimplex.CoordinateRing L d)]
          (Laurent (AlgebraicSimplex.CoordinateRing L d) ⧸ (pointTransport e d p).val)) = 1
      exact Module.primeQuotient_local_length _
    rw [hl]
    simp [FreeAbelianGroup.coeff]
  · have hnot : ¬ p.val.map
        (coefficientMap (AlgebraicSimplex.coefficientMap e.toRingHom d)) ≤ q.val := by
      intro hle
      rw [← pointTransport_val] at hle
      have hm := minimal_of_finite_quotient_le (pointTransport e d p).val q.val
        q.under_eq_bot hle
      rw [Ideal.minimalPrimes_eq_subsingleton_self] at hm
      exact h (Subtype.ext (Set.mem_singleton_iff.mp hm))
    rw [localizedQuotientLength_zero_of_not_le _ q hnot]
    simp [FreeAbelianGroup.coeff, h]

end AlgebraicGeometry.Torus.FiniteCorrespondence.ScalarTransport
