/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

/-!
Polynomial foundations for the universal smooth-field dimension targets.
All finite variable types and all fields are allowed. Maximal ideals need not
have separable residue field extensions.

## Extraction basis

Transferred from `R5Lab.RingTheory.KrullDimension.PolynomialField` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`1e52eb14146f6331c2031b69148f91644027ce2daca41a3111d644be80c0e435`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

open Ideal

namespace MvPolynomial

universe u v

/-- Every maximal ideal of a finite polynomial algebra over a field has height
exactly the number of variables, including zero variables. -/
theorem mvPolynomial_height_eq_card_of_isMaximal (K : Type u) [Field K]
    (ι : Type v) [Finite ι] :
    ∀ (p : Ideal (MvPolynomial ι K)) [p.IsMaximal], p.height = Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    intro p hp
    let e' := (MvPolynomial.renameEquiv K e).toRingEquiv
    have : (p.comap e').IsMaximal := Ideal.comap_isMaximal_of_equiv e'
    rw [← e'.height_comap p, H (p.comap e'), Nat.card_congr e]
  | h_empty =>
    intro p hp
    let e := MvPolynomial.isEmptyRingEquiv K PEmpty
    have : (p.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hb : p.map e = ⊥ :=
      (IsSimpleOrder.eq_bot_or_eq_top (p.map e)).resolve_right Ideal.IsPrime.ne_top'
    rw [← e.height_map p, hb, Ideal.height_bot]
    simp
  | @h_option ι _ H =>
    intro p hp
    let e := (MvPolynomial.optionEquivLeft K ι).toRingEquiv
    let q := p.map e
    have : q.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have : (q.comap Polynomial.C).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing q
    have : q.LiesOver (q.comap Polynomial.C) := ⟨rfl⟩
    rw [← e.height_map p, Polynomial.height_eq_height_add_one (q.comap Polynomial.C) q,
      H (q.comap Polynomial.C)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one]

/-- The local ring at every maximal polynomial prime has dimension equal to
its number of variables. -/
theorem mvPolynomial_localizationAtPrime_dimension_of_isMaximal
    (K : Type u) [Field K] (ι : Type v) [Finite ι]
    (p : Ideal (MvPolynomial ι K)) [p.IsMaximal] :
    ringKrullDim (Localization.AtPrime p) = Nat.card ι := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    mvPolynomial_height_eq_card_of_isMaximal K ι p]
  simp

/-- Arbitrary polynomial stalks have the required upper bound; exact dimension
is reserved for maximal points. -/
theorem mvPolynomial_localizationAtPrime_dimension_le
    (K : Type u) [Field K] (ι : Type v) [Finite ι]
    (p : Ideal (MvPolynomial ι K)) [p.IsPrime] :
    ringKrullDim (Localization.AtPrime p) ≤ Nat.card ι := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
  have h := p.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  simpa using h

/-- Polynomial local rings over fields are regular, without perfectness or
characteristic restrictions. -/
theorem mvPolynomial_localizationAtPrime_isRegularLocalRing
    (K : Type u) [Field K] (ι : Type v) [Finite ι]
    (p : Ideal (MvPolynomial ι K)) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  inferInstance

/-- A maximal point of a finite-type field algebra contracts to a maximal
point under every compatible field-algebra map. Zariski's lemma supplies
integrality of the residue field; separability is unnecessary. -/
theorem _root_.Ideal.isMaximal_comap_of_finiteType_field
    (K : Type u) [Field K] {A B : Type v} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra.FiniteType K B]
    (g : A →ₐ[K] B) (q : Ideal B) [q.IsMaximal] :
    (q.comap g.toRingHom).IsMaximal := by
  let : Field (B ⧸ q) := Ideal.Quotient.field q
  have : Module.Finite K (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ q)
  have hK : ((Ideal.Quotient.mk q).comp (algebraMap K B)).IsIntegral :=
    Algebra.isIntegral_def.mp (inferInstance : Algebra.IsIntegral K (B ⧸ q))
  have hg : ((Ideal.Quotient.mk q).comp g.toRingHom).IsIntegral := by
    apply RingHom.IsIntegral.tower_top (algebraMap K A)
    convert hK using 1
    ext k
    exact congrArg (Ideal.Quotient.mk q) (g.commutes k)
  have : (⊥ : Ideal (B ⧸ q)).IsMaximal := Ideal.bot_isMaximal
  have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ hg (⊥ : Ideal (B ⧸ q))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hm

end MvPolynomial
