/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselization
public import Aglib.RingTheory.Henselian.PolynomialLocalTriangular

/-!
# Actual triangular automorphisms of polynomial local henselizations

The original local-ring automorphism and its inverse extend by the proved local
universal property. Their compositions are the identity because they restrict
to the original identity map, not because bijectivity is assumed.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v

namespace PolynomialLocalHenselization

variable (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)

/-- The local universal property with the original coefficient-ring algebra maps retained. -/
theorem existsUnique_local_extension
    (T : Type v) [CommRing T] [HenselianLocalRing T] [Algebra R T]
    (φ : PolynomialLocalRing R n →ₐ[R] T) [IsLocalHom φ.toRingHom] :
    ∃! f : PolynomialLocalHenselization R n →ₐ[R] T,
      IsLocalHom f.toRingHom ∧
        f.comp (IsScalarTower.toAlgHom R (PolynomialLocalRing R n)
          (PolynomialLocalHenselization R n)) = φ := by
  let A := PolynomialLocalRing R n
  let : Algebra A T := φ.toRingHom.toAlgebra
  let : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  let : IsLocalHom (algebraMap A T) := inferInstanceAs (IsLocalHom φ.toRingHom)
  let h := Henselization.existsUnique_local_algHom A T
  let g : Henselization A →ₐ[A] T := h.choose
  have hg : IsLocalHom g.toRingHom := h.choose_spec.1
  refine ⟨g.restrictScalars R, ⟨hg, ?_⟩, ?_⟩
  · apply AlgHom.ext
    intro a
    exact g.commutes a
  · intro f hf
    let f' : Henselization A →ₐ[A] T :=
      { f.toRingHom with commutes' := fun a => AlgHom.congr_fun hf.2 a }
    have he : f' = g := h.choose_spec.2 f' hf.1
    apply AlgHom.ext
    intro x
    exact AlgHom.congr_fun he x

/-- The actual local-ring coordinate map followed by the original henselization map. -/
def coordinateBaseMap (a : PolynomialLocalRing R n ≃ₐ[R] PolynomialLocalRing R n) :
    PolynomialLocalRing R n →ₐ[R] PolynomialLocalHenselization R n :=
  (IsScalarTower.toAlgHom R (PolynomialLocalRing R n)
    (PolynomialLocalHenselization R n)).comp a.toAlgHom

instance coordinateBaseMap_isLocalHom
    (a : PolynomialLocalRing R n ≃ₐ[R] PolynomialLocalRing R n) :
    IsLocalHom (coordinateBaseMap R n a).toRingHom := by
  constructor
  intro x hx
  have h : IsUnit (a x) := IsLocalHom.map_nonunit
    (f := algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n)) (a x) hx
  have h' := h.map a.symm.toRingHom
  change IsUnit (a.symm (a x)) at h'
  simpa only [AlgEquiv.symm_apply_apply] using h'

/-- The genuine local universal extension of an actual coordinate automorphism. -/
def coordinateLift (a : PolynomialLocalRing R n ≃ₐ[R] PolynomialLocalRing R n) :
    PolynomialLocalHenselization R n →ₐ[R] PolynomialLocalHenselization R n :=
  (existsUnique_local_extension R n (PolynomialLocalHenselization R n)
    (coordinateBaseMap R n a)).choose

instance coordinateLift_isLocalHom
    (a : PolynomialLocalRing R n ≃ₐ[R] PolynomialLocalRing R n) :
    IsLocalHom (coordinateLift R n a).toRingHom :=
  (existsUnique_local_extension R n (PolynomialLocalHenselization R n)
    (coordinateBaseMap R n a)).choose_spec.1.1

/-- The lift has its literal prescribed restriction to the original local ring. -/
theorem coordinateLift_algebraMap
    (a : PolynomialLocalRing R n ≃ₐ[R] PolynomialLocalRing R n)
    (x : PolynomialLocalRing R n) :
    coordinateLift R n a
      (algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n) x) =
      algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n) (a x) :=
  AlgHom.congr_fun (existsUnique_local_extension R n (PolynomialLocalHenselization R n)
    (coordinateBaseMap R n a)).choose_spec.1.2 x

/-- The forward lift composed with the inverse lift is the actual identity algebra map. -/
theorem coordinateLift_comp_symm
    (a : PolynomialLocalRing R n ≃ₐ[R] PolynomialLocalRing R n) :
    (coordinateLift R n a).comp (coordinateLift R n a.symm) =
      AlgHom.id R (PolynomialLocalHenselization R n) := by
  let ι := IsScalarTower.toAlgHom R (PolynomialLocalRing R n) (PolynomialLocalHenselization R n)
  let : IsLocalHom ι.toRingHom := inferInstanceAs
    (IsLocalHom (algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n)))
  have h := existsUnique_local_extension R n (PolynomialLocalHenselization R n) ι
  have hcomp : ((coordinateLift R n a).comp (coordinateLift R n a.symm)).comp ι = ι := by
    apply AlgHom.ext
    intro x
    change coordinateLift R n a (coordinateLift R n a.symm
      (algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n) x)) =
      algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n) x
    rw [coordinateLift_algebraMap, coordinateLift_algebraMap, AlgEquiv.apply_symm_apply]
  have hlocal : IsLocalHom
      ((coordinateLift R n a).comp (coordinateLift R n a.symm)).toRingHom := by
    change IsLocalHom ((coordinateLift R n a).toRingHom.comp
      (coordinateLift R n a.symm).toRingHom)
    infer_instance
  have hid : IsLocalHom (AlgHom.id R (PolynomialLocalHenselization R n)).toRingHom := by
    change IsLocalHom (RingHom.id (PolynomialLocalHenselization R n))
    infer_instance
  exact (h.choose_spec.2 _ ⟨hlocal, hcomp⟩).trans
    (h.choose_spec.2 (AlgHom.id R _) ⟨hid, rfl⟩).symm

/-- The actual triangular henselization equivalence, with its genuinely constructed inverse. -/
def triangularAlgEquiv (p : Fin n) (e : Fin n → ℕ) (he : ∀ i, i ≠ p → 0 < e i) :
    PolynomialLocalHenselization R n ≃ₐ[R] PolynomialLocalHenselization R n :=
  let a := PolynomialLocalRing.triangularAlgEquiv R n p e he
  AlgEquiv.ofAlgHom (coordinateLift R n a) (coordinateLift R n a.symm)
    (coordinateLift_comp_symm R n a) (coordinateLift_comp_symm R n a.symm)

/-- Forward triangular change agrees with the original local-ring coordinate change. -/
theorem triangularAlgEquiv_algebraMap (p : Fin n) (e : Fin n → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) (x : PolynomialLocalRing R n) :
    triangularAlgEquiv R n p e he
      (algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n) x) =
      algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n)
        (PolynomialLocalRing.triangularAlgEquiv R n p e he x) :=
  coordinateLift_algebraMap R n _ x

/-- Inverse triangular change agrees with the actual inverse local-ring coordinate change. -/
theorem triangularAlgEquiv_symm_algebraMap (p : Fin n) (e : Fin n → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) (x : PolynomialLocalRing R n) :
    (triangularAlgEquiv R n p e he).symm
      (algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n) x) =
      algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n)
        ((PolynomialLocalRing.triangularAlgEquiv R n p e he).symm x) :=
  coordinateLift_algebraMap R n _ x

/-- The actual triangular henselization map preserves all maximal-ideal powers. -/
theorem triangularAlgEquiv_mem_maximalIdeal_pow_iff (p : Fin n) (e : Fin n → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) (c : ℕ) (x : PolynomialLocalHenselization R n) :
    triangularAlgEquiv R n p e he x ∈ maximalIdeal (PolynomialLocalHenselization R n) ^ c ↔
      x ∈ maximalIdeal (PolynomialLocalHenselization R n) ^ c := by
  have hm : (maximalIdeal (PolynomialLocalHenselization R n) ^ c).map
      (triangularAlgEquiv R n p e he).toRingEquiv =
        maximalIdeal (PolynomialLocalHenselization R n) ^ c := by
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
  have h := Ideal.apply_mem_of_equiv_iff
    (I := maximalIdeal (PolynomialLocalHenselization R n) ^ c)
    (f := (triangularAlgEquiv R n p e he).toRingEquiv) (x := x)
  rw [hm] at h
  exact h

/-- Pulling back normalized source elements preserves the actual requested ideal-adic precision. -/
theorem triangularAlgEquiv_symm_mem_maximalIdeal_pow_iff (p : Fin n) (e : Fin n → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) (c : ℕ)
    (x : PolynomialLocalHenselization R n) :
    (triangularAlgEquiv R n p e he).symm x ∈
        maximalIdeal (PolynomialLocalHenselization R n) ^ c ↔
      x ∈ maximalIdeal (PolynomialLocalHenselization R n) ^ c := by
  have h := triangularAlgEquiv_mem_maximalIdeal_pow_iff R n p e he c
    ((triangularAlgEquiv R n p e he).symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

end PolynomialLocalHenselization
