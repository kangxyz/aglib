/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.SeparablyGenerated.EmbeddedField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Smooth.Field

/-!
# The actual evaluation component in a separable ambient fraction field

The residue field is that of the literal polynomial-evaluation kernel. Its
embedding into the ambient fraction field extends the original evaluation
map. Injectivity on coefficients is used to construct the coefficient
fraction-field action, and uniqueness of fraction extensions proves that the
embedding respects the same action already used on the ambient field.

Ambient transcendental separability is an explicit input of this bridge. In
power-series applications it must be supplied by a separate theorem.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {A C L σ : Type*} [CommRing A] [CommRing C] [IsDomain C]
  [Field L] [Algebra A C] [Algebra C L] [IsFractionRing C L]
  [Algebra A L] [IsScalarTower A C L]

local instance (y : σ → C) :
    (RingHom.ker (aeval (R := A) y)).IsPrime := RingHom.ker_isPrime _

/-- The fraction field of the original evaluation component embeds in the
ambient fraction field by extension of the original polynomial evaluation. -/
def evaluationResidueFieldHom (y : σ → C) :
    (RingHom.ker (aeval (R := A) y)).ResidueField →ₐ[A] L := by
  let q := RingHom.ker (aeval (R := A) y)
  let g : (MvPolynomial σ A ⧸ q) →ₐ[A] L :=
    (IsScalarTower.toAlgHom A C L).comp (Ideal.kerLiftAlg (aeval (R := A) y))
  have hg : Function.Injective g := by
    intro x z hx
    apply Ideal.kerLiftAlg_injective (aeval (R := A) y)
    apply IsFractionRing.injective C L
    exact hx
  exact IsFractionRing.liftAlgHom (R := A) (A := MvPolynomial σ A ⧸ q)
    (K := q.ResidueField) (g := g) hg

/-- The residue-field embedding agrees literally with the original evaluation
on every original polynomial. -/
theorem evaluationResidueFieldHom_algebraMap (y : σ → C) (p : MvPolynomial σ A) :
    evaluationResidueFieldHom (L := L) y
      (algebraMap (MvPolynomial σ A) (RingHom.ker (aeval (R := A) y)).ResidueField p) =
      algebraMap C L (aeval y p) := by
  let q := RingHom.ker (aeval (R := A) y)
  change evaluationResidueFieldHom (L := L) y
    (algebraMap (MvPolynomial σ A) q.ResidueField p) = _
  rw [IsScalarTower.algebraMap_apply (MvPolynomial σ A) (MvPolynomial σ A ⧸ q)]
  let g : (MvPolynomial σ A ⧸ q) →ₐ[A] L :=
    (IsScalarTower.toAlgHom A C L).comp (Ideal.kerLiftAlg (aeval (R := A) y))
  have hg : Function.Injective g := by
    intro x z hx
    apply Ideal.kerLiftAlg_injective (aeval (R := A) y)
    apply IsFractionRing.injective C L
    exact hx
  change IsFractionRing.lift (K := q.ResidueField) (g := g.toRingHom) hg
    (algebraMap (MvPolynomial σ A ⧸ q) q.ResidueField (Ideal.Quotient.mk q p)) = _
  rw [IsFractionRing.lift_algebraMap]
  rfl

omit [IsDomain C] in
/-- Injectivity of the original coefficient map proves that the evaluation
prime has zero contraction to the coefficient ring. -/
theorem comap_evaluation_ker_C_eq_bot (y : σ → C)
    (hAC : Function.Injective (algebraMap A C)) :
    (RingHom.ker (aeval (R := A) y)).comap (MvPolynomial.C : A →+* MvPolynomial σ A) = ⊥ := by
  ext a
  change aeval y (MvPolynomial.C a) = 0 ↔ a = 0
  rw [aeval_C]
  exact map_eq_zero_iff _ hAC

/-- The actual coefficient map into the evaluation component's fraction field
is injective, because the original coefficient map into the target is. -/
theorem algebraMap_evaluation_residueField_injective (y : σ → C)
    (hAC : Function.Injective (algebraMap A C)) :
    Function.Injective (algebraMap A (RingHom.ker (aeval (R := A) y)).ResidueField) := by
  rw [RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq A (MvPolynomial σ A)
      (RingHom.ker (aeval (R := A) y)).ResidueField,
    ← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
  exact comap_evaluation_ker_C_eq_bot y hAC

variable {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra F L] [IsScalarTower A F L]

/-- General separability of the ambient fraction field makes the actual
finite-type evaluation component formally smooth over the original base.
All fraction-field actions extend the given original coefficient maps. -/
theorem formallySmooth_evaluation_residueField_of_transcendentalSeparable
    [Finite σ] [Algebra.IsTranscendentalSeparable F L]
    (y : σ → C) (hAC : Function.Injective (algebraMap A C)) :
    Algebra.FormallySmooth A (RingHom.ker (aeval (R := A) y)).ResidueField := by
  let q := RingHom.ker (aeval (R := A) y)
  let B := MvPolynomial σ A ⧸ q
  let E := q.ResidueField
  let e : E →ₐ[A] L := evaluationResidueFieldHom y
  have hAE : Function.Injective (algebraMap A E) :=
    algebraMap_evaluation_residueField_injective y hAC
  let f : F →+* E := IsFractionRing.lift hAE
  let : Algebra F E := f.toAlgebra
  let : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap hAE a).symm
  have heF : e.toRingHom.comp (algebraMap F E) = algebraMap F L := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro a
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A F E,
      ← IsScalarTower.algebraMap_apply A F L]
    exact e.commutes a
  let eF : E →ₐ[F] L :=
    { e.toRingHom with commutes' := RingHom.congr_fun heF }
  let : Algebra.EssFiniteType A B := inferInstance
  let : Algebra.EssFiniteType B E :=
    Algebra.EssFiniteType.of_isLocalization E (nonZeroDivisors B)
  let : Algebra.EssFiniteType A E := Algebra.EssFiniteType.comp A B E
  let : Algebra.EssFiniteType F E := Algebra.EssFiniteType.of_comp A F E
  let : Algebra.IsSeparablyGenerated F E := Algebra.isSeparablyGenerated_of_algHom eF
  obtain ⟨s, hs, hsep⟩ := ‹Algebra.IsSeparablyGenerated F E›
  let : Algebra.IsSeparable (IntermediateField.adjoin F
      (Set.range ((↑) : s → E))) E := by
    rw [Subtype.range_coe]
    exact hsep
  let : Algebra.FormallySmooth F E :=
    Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  let : Algebra.FormallySmooth A F :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors A)
  exact Algebra.FormallySmooth.comp A F E

end MvPolynomial
