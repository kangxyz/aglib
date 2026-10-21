/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.PrincipalMultiplicity
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.ModuleCycle
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.SimplexFaces

/-!
# ModulePrincipalNaturality for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `ModulePrincipalNaturality.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`71517f5237517da8f4c84c98257544a24acb5bc20e4eeb6a4aa0aca10f9e76c9`.

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
open Module
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

theorem objectCycle_mem_support_iff_minimal [IsNoetherianRing R]
    (X : Object R) (p : FiniteDominantPrime R) :
    p ∈ (objectCycle X).support ↔ p.val ∈ (supportIdeal X).minimalPrimes := by
  constructor
  · exact objectCycle_support X p
  · intro hp
    rw [FreeAbelianGroup.mem_support_iff, objectCycle_coeff]
    exact_mod_cast (coefficient_ne_zero_iff X p).mpr hp.le

-- Retain the source-Noetherian guard of the original principal-face coefficient interface.
@[nolint unusedArguments]
theorem originalPrincipalFaceTerm_eq_point_term [IsNoetherianRing R]
    (X : Object R) (p : FiniteDominantPrime R) (q : FiniteDominantPrime S)
    (hp : p.val ∈ (supportIdeal X).minimalPrimes) :
    originalPrincipalFaceTerm (S := S) X q.val p.val =
      (coefficient X p : ℤ) * (quotientFibreMultiplicity (S := S) p q : ℤ) := by
  simp only [originalPrincipalFaceTerm, dite_eq_left hp]
  rfl

/-- Coefficients of the existing quotient-fibre map on the existing object cycle. -/
theorem quotientFibreCycleMap_objectCycle_coeff
    [IsNoetherianRing R] [IsNoetherianRing S] (X : Object R) (q : FiniteDominantPrime S) :
    FreeAbelianGroup.coeff q (quotientFibreCycleMap (S := S) (objectCycle X)) =
      ∑ p ∈ (objectCycle X).support,
        (coefficient X p : ℤ) * (quotientFibreMultiplicity (S := S) p q : ℤ) := by
  conv_lhs => rw [objectCycle_eq_finiteSum X]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [map_zsmul, map_zsmul, quotientFibreCycleMap_of_coeff]
  exact smul_eq_mul _ _

/-- The original support-prime sum is the literal coefficient of the maintained cycle map. -/
theorem originalPrincipalFaceSum_eq_cycleMap_coeff
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R]
    (X : Object R) (q : FiniteDominantPrime S) :
    (∑ P ∈ originalMinimalSupportBelow X (q.val.under (Laurent R)),
      originalPrincipalFaceTerm (S := S) X q.val P) =
        FreeAbelianGroup.coeff q (quotientFibreCycleMap (S := S) (objectCycle X)) := by
  classical
  let s := (objectCycle X).support.filter (fun p => p.val ≤ q.val.under (Laurent R))
  have hb : (∑ p ∈ s,
      (coefficient X p : ℤ) * (quotientFibreMultiplicity (S := S) p q : ℤ)) =
      ∑ P ∈ originalMinimalSupportBelow X (q.val.under (Laurent R)),
        originalPrincipalFaceTerm (S := S) X q.val P := by
    apply Finset.sum_bij (fun p _ => p.val)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hs, hle⟩
      exact (mem_originalMinimalSupportBelow X _ _).mpr
        ⟨objectCycle_support X p hs, hle⟩
    · intro p₁ _ p₂ _ he
      exact Subtype.val_injective he
    · intro P hP
      rcases (mem_originalMinimalSupportBelow X _ _).mp hP with ⟨hp, hle⟩
      let p := minimalPoint X P hp
      have hs : p ∈ (objectCycle X).support :=
        (objectCycle_mem_support_iff_minimal X p).mpr hp
      exact ⟨p, Finset.mem_filter.mpr ⟨hs, hle⟩, rfl⟩
    · intro p hp
      have hm := objectCycle_support X p (Finset.mem_filter.mp hp).1
      exact (originalPrincipalFaceTerm_eq_point_term X p q hm).symm
  have hz : (∑ p ∈ s,
      (coefficient X p : ℤ) * (quotientFibreMultiplicity (S := S) p q : ℤ)) =
      ∑ p ∈ (objectCycle X).support,
        (coefficient X p : ℤ) * (quotientFibreMultiplicity (S := S) p q : ℤ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hnot : ¬ p.val ≤ q.val.under (Laurent R) :=
      fun hle => hn (Finset.mem_filter.mpr ⟨hp, hle⟩)
    have hm : ¬ p.val.map (coefficientMap (algebraMap R S)) ≤ q.val := by
      intro hmap
      apply hnot
      exact Ideal.map_le_iff_le_comap.mp hmap
    have hzero : quotientFibreMultiplicity (S := S) p q = 0 := by
      by_contra hne
      exact hm ((quotientFibreMultiplicity_ne_zero_iff p q).mp hne)
    simp only [hzero, Nat.cast_zero, mul_zero]
  rw [quotientFibreCycleMap_objectCycle_coeff]
  exact hb.symm.trans hz

/-- Naturality for the actual surjective regular principal coefficient map. -/
theorem objectCycle_principal_baseChange
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R]
    (X : Object R) (t : R) (h : Function.Surjective (algebraMap R S))
    (ht : RingHom.ker (algebraMap R S) = Ideal.span ({t} : Set R)) (hr : IsRegular t) :
    objectCycle (X.baseChange S) = quotientFibreCycleMap (S := S) (objectCycle X) := by
  apply (FreeAbelianGroup.equivFinsupp (FiniteDominantPrime S)).injective
  ext q
  change FreeAbelianGroup.coeff q (objectCycle (X.baseChange S)) =
    FreeAbelianGroup.coeff q (quotientFibreCycleMap (S := S) (objectCycle X))
  rw [objectCycle_coeff]
  exact (principalFace_original_point_coefficient X t h ht hr q).trans
    (originalPrincipalFaceSum_eq_cycleMap_coeff X q)

/-- Original object-cycle face equality in every actual simplex degree. -/
theorem simplexFace_objectCycle (K : Type u) [Field K] (n : ℕ) (i : Fin (n + 2))
    (X : Object (AlgebraicSimplex.CoordinateRing K (n + 1))) :
    let := (AlgebraicSimplex.face K i).toAlgebra
    objectCycle (X.baseChange (AlgebraicSimplex.CoordinateRing K n)) =
      simplexFaceCycle K n i (objectCycle X) := by
  let := (AlgebraicSimplex.face K i).toAlgebra
  exact objectCycle_principal_baseChange X _
    (AlgebraicSimplex.face_surjective K i) (AlgebraicSimplex.ker_face K i)
    (AlgebraicSimplex.coordinate_isRegular K (n + 1) i)

end AlgebraicGeometry.Torus.FiniteCorrespondence
