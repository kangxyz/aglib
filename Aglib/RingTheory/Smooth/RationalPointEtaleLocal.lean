/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Etale-local lifting of an actual rational point of a smooth algebra

The construction uses the original standard-etale polynomial chart, lifts its
coordinate values through the original residue map, and takes the localization
of the actual tensor slice at the kernel of its residue map. The output retains
the original rational map, with no normality, excellence, or Henselian premise.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace Algebra.Smooth.RationalPointEtaleLocal

section Slice

variable (R P B : Type u) [CommRing R] [CommRing P] [CommRing B] [IsLocalRing R]
  [Algebra R P] [Algebra P R] [Algebra R B] [Algebra P B]
  [IsScalarTower R P R] [IsScalarTower R P B]
  [Algebra P (ResidueField R)] [IsScalarTower P R (ResidueField R)]

/-- The actual residue map of the original tensor slice. -/
def sliceResidue (ψ : B →ₐ[P] ResidueField R) :
    R ⊗[P] B →ₐ[R] ResidueField R :=
  Algebra.TensorProduct.lift (Algebra.ofId R (ResidueField R)) ψ
    (fun _ _ => .all _ _)

/-- The centre is exactly the kernel of that residue map, not an arbitrary
prime lying over the coefficient closed point. -/
def slicePrime (ψ : B →ₐ[P] ResidueField R) : Ideal (R ⊗[P] B) :=
  RingHom.ker (sliceResidue R P B ψ).toRingHom

instance slicePrime_isPrime (ψ : B →ₐ[P] ResidueField R) :
    (slicePrime R P B ψ).IsPrime := RingHom.ker_isPrime _

/-- The one selected local ring of the actual tensor slice. -/
abbrev SliceLocalRing (ψ : B →ₐ[P] ResidueField R) :=
  Localization.AtPrime (slicePrime R P B ψ)

/-- The original residue map extends to the same local ring. -/
def localResidue (ψ : B →ₐ[P] ResidueField R) :
    SliceLocalRing R P B ψ →ₐ[R] ResidueField R :=
  IsLocalization.liftAlgHom (S := SliceLocalRing R P B ψ)
    (f := sliceResidue R P B ψ)
    (fun y : (slicePrime R P B ψ).primeCompl => isUnit_iff_ne_zero.mpr y.property)

/-- The original chart map into the one selected local tensor slice. -/
def chartToLocal (ψ : B →ₐ[P] ResidueField R) : B →ₐ[R] SliceLocalRing R P B ψ :=
  (IsScalarTower.toAlgHom R (R ⊗[P] B) (SliceLocalRing R P B ψ)).comp
    ((Algebra.TensorProduct.includeRight : B →ₐ[P] R ⊗[P] B).restrictScalars R)

/-- The same local residue map recovers the original chart rational point. -/
theorem localResidue_chartToLocal (ψ : B →ₐ[P] ResidueField R) (b : B) :
    localResidue R P B ψ (chartToLocal R P B ψ b) = ψ b := by
  change IsLocalization.lift _
    (algebraMap (R ⊗[P] B) (SliceLocalRing R P B ψ) (1 ⊗ₜ[P] b)) = ψ b
  rw [IsLocalization.lift_eq]
  change sliceResidue R P B ψ (1 ⊗ₜ[P] b) = ψ b
  rw [sliceResidue, Algebra.TensorProduct.lift_tmul]
  simp

omit [Algebra R P] [Algebra R B] [IsScalarTower R P R] [IsScalarTower R P B] in
/-- Surjectivity is supplied by the original coefficient residue map. -/
theorem localResidue_surjective (ψ : B →ₐ[P] ResidueField R) :
    Function.Surjective (localResidue R P B ψ) := by
  intro a
  obtain ⟨r, rfl⟩ := residue_surjective a
  exact ⟨algebraMap R (SliceLocalRing R P B ψ) r, (localResidue R P B ψ).commutes r⟩

/-- The structural coefficient map into the actual local slice is local. -/
instance coefficient_isLocalHom (ψ : B →ₐ[P] ResidueField R) :
    IsLocalHom (algebraMap R (SliceLocalRing R P B ψ)) := by
  let : IsLocalHom ((localResidue R P B ψ).toRingHom.comp
      (algebraMap R (SliceLocalRing R P B ψ))) := by
    have he : (localResidue R P B ψ).toRingHom.comp
        (algebraMap R (SliceLocalRing R P B ψ)) = residue R := by
      ext r
      exact (localResidue R P B ψ).commutes r
    rw [he]
    infer_instance
  exact isLocalHom_of_comp (algebraMap R (SliceLocalRing R P B ψ))
    (localResidue R P B ψ).toRingHom

instance localResidue_isLocalHom (ψ : B →ₐ[P] ResidueField R) :
    IsLocalHom (localResidue R P B ψ).toRingHom :=
  IsLocalHom.of_surjective _ (localResidue_surjective R P B ψ)

variable [Algebra.Etale P B]

/-- The slice is essentially etale over the coefficients: first actual
etale base change, then the original prime localization. -/
instance local_formallyEtale (ψ : B →ₐ[P] ResidueField R) :
    Algebra.FormallyEtale R (SliceLocalRing R P B ψ) := by
  let : Algebra.Etale R (R ⊗[P] B) := inferInstance
  infer_instance

instance local_essFiniteType (ψ : B →ₐ[P] ResidueField R) :
    Algebra.EssFiniteType R (SliceLocalRing R P B ψ) := by
  let : Algebra.Etale R (R ⊗[P] B) := inferInstance
  exact Algebra.EssFiniteType.comp R (R ⊗[P] B) _

instance local_flat (ψ : B →ₐ[P] ResidueField R) :
    Module.Flat R (SliceLocalRing R P B ψ) := by
  let : Algebra.Etale R (R ⊗[P] B) := inferInstance
  exact Module.Flat.trans R (R ⊗[P] B) _

end Slice

/-- A rational residue point of an actual smooth algebra lifts over an
essentially etale local coefficient algebra. The point and its reduction map
are retained by the displayed composition equation. -/
theorem exists_local_lift
    (R B : Type u) [CommRing R] [CommRing B] [IsLocalRing R]
    [Algebra R B] [Algebra.Smooth R B] (ψ : B →ₐ[R] ResidueField R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : IsLocalRing S),
      Algebra.FormallyEtale R S ∧ Algebra.EssFiniteType R S ∧ Module.Flat R S ∧
        IsLocalHom (algebraMap R S) ∧
          ∃ (ε : B →ₐ[R] S) (l : S →ₐ[R] ResidueField R),
            Function.Surjective l ∧ IsLocalHom l.toRingHom ∧ l.comp ε = ψ := by
  let p := RingHom.ker ψ.toRingHom
  let : p.IsPrime := RingHom.ker_isPrime _
  obtain ⟨r, hr, n, hpoly, htower, hstd⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  let P := MvPolynomial (Fin n) R
  let B' := Localization.Away r
  let : Algebra P B' := hpoly
  let : IsScalarTower R P B' := htower
  let : Algebra.IsStandardEtale P B' := hstd
  have hrψ : IsUnit (ψ r) := isUnit_iff_ne_zero.mpr hr
  let ψ' : B' →ₐ[R] ResidueField R := IsLocalization.Away.liftAlgHom r hrψ
  choose a ha using fun i : Fin n =>
    residue_surjective (ψ' (algebraMap P B' (MvPolynomial.X i)))
  let ρ : P →ₐ[R] R := MvPolynomial.aeval a
  let : Algebra P R := ρ.toRingHom.toAlgebra
  let : IsScalarTower R P R := .of_algebraMap_eq' ρ.comp_algebraMap.symm
  let : Algebra P (ResidueField R) := ((residue R).comp ρ.toRingHom).toAlgebra
  let : IsScalarTower P R (ResidueField R) := .of_algebraMap_eq' rfl
  have hcomp : ψ'.comp (IsScalarTower.toAlgHom R P B') =
      (Algebra.ofId R (ResidueField R)).comp ρ := by
    ext i
    change ψ' (algebraMap P B' (MvPolynomial.X i)) =
      residue R (MvPolynomial.aeval a (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X]
    exact (ha i).symm
  let ψP : B' →ₐ[P] ResidueField R :=
    { __ := ψ'.toRingHom
      commutes' t := DFunLike.congr_fun hcomp t }
  let S := SliceLocalRing R P B' ψP
  let ε : B →ₐ[R] S := (chartToLocal R P B' ψP).comp
    (IsScalarTower.toAlgHom R B B')
  let l : S →ₐ[R] ResidueField R := localResidue R P B' ψP
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ε, l,
    localResidue_surjective R P B' ψP, inferInstance, ?_⟩
  ext b
  change localResidue R P B' ψP
    (chartToLocal R P B' ψP (algebraMap B B' b)) = ψ b
  rw [localResidue_chartToLocal]
  exact IsLocalization.Away.lift_eq r hrψ b

end Algebra.Smooth.RationalPointEtaleLocal
