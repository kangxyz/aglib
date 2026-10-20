/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Polynomial.Laurent.ModuleCech
public import Aglib.Algebra.Homology.ModuleCat.LinearMapConeIso
public import Aglib.Algebra.Homology.ModuleCat.LaurentProjectorCech

/-! # Finite-projective models of original Laurent module Cech complexes

For finite-projective polynomial chart modules and a specified isomorphism between their
distinct Laurent scalar extensions, the original signed adjunction-unit complex has an
actual finite-projective model in degrees zero and one. Genuine finite-free retractions
produce the matrix data, and an actual cone/shift isomorphism retains the original maps.
Constructing this module datum from a geometric sheaf and comparing its restrictions are
separate obligations; no geometric generation statement is asserted here.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Homology/ModuleCat/LaurentModuleCech.lean` from
the supplied frozen Quillen snapshot.
SHA-256: `1dbad28ce87b1256bcd291a082ad5b8b08cfd70c7f965f3227b2f4201eeea5b1`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Polynomial LaurentPolynomial
open scoped TensorProduct Matrix ChangeOfRings LaurentPolynomial
universe u v
open LaurentPolynomial.Projector

namespace ModuleCat.LaurentCech
open ModuleCat Module.Projective ModuleCat
variable {R : Type u} [CommRing R]
variable (M N : ModuleCat.{u} R[X]) {m n : ℕ}
variable (i : M →ₗ[R[X]] Fin m → R[X]) (r : (Fin m → R[X]) →ₗ[R[X]] M)
variable (j : N →ₗ[R[X]] Fin n → R[X]) (s : (Fin n → R[X]) →ₗ[R[X]] N)
variable (hr : r.comp i = LinearMap.id) (hs : s.comp j = LinearMap.id)
variable (e : (extendScalars (negativeScalarMap R)).obj N ≅
  (extendScalars (Polynomial.toLaurent (R := R))).obj M)

local notation "p" => retractMatrix i r
local notation "q" => retractMatrix j s
local notation "g" => extensionTransitionMatrix (Polynomial.toLaurent (R := R))
  (negativeScalarMap R) i s e
local notation "h" => extensionTransitionMatrix (negativeScalarMap R)
  (Polynomial.toLaurent (R := R)) j r e.symm

include hr in
/-- The actual positive chart projector fixes the original overlap matrix. -/
theorem chartProjector_transition : plusMatrix p * g = g :=
  mappedProjector_mul_extensionTransition (Polynomial.toLaurent (R := R))
    (negativeScalarMap R) i r s hr e

include hs in
/-- The two actual overlap matrices compose to the original positive chart projector. -/
theorem chartTransition_inverse : g * h = plusMatrix p :=
  extensionTransitionMatrix_mul_inverse (Polynomial.toLaurent (R := R))
    (negativeScalarMap R) i r j s hs e

include hr in
/-- The opposite composite is the original negative chart projector with its inverted scalar
map. -/
theorem chartTransition_inverse_rev : h * g = minusMatrix q :=
  extensionTransitionMatrix_mul_inverse (negativeScalarMap R)
    (Polynomial.toLaurent (R := R)) j s i r hr e.symm

include hs in
/-- The original overlap matrix factors through the negative chart projector. -/
theorem chartTransition_projector : g * minusMatrix q = g :=
  extensionTransition_mul_mappedProjector (Polynomial.toLaurent (R := R))
    (negativeScalarMap R) i j s hs e

/-- The original signed module complex is isomorphic to its actual projector-coordinate
complex. -/
def coordinateCechIso :
    linearMapCechComplex (moduleDifference (R := R) M N e) ≅
      linearMapCechComplex (rangeDifference p q g (retractMatrix_idempotent i r hr)
        (chartProjector_transition M N i r s hr e)) := by
  let a := (polynomialRetractImageIso M i r hr).toLinearEquiv.prodCongr
    (polynomialRetractImageIso N j s hs).toLinearEquiv
  let b := (laurentRetractImageIso M i r hr).toLinearEquiv
  apply linearMapCechIsoOfEquivs _ _ a b
  apply LinearMap.ext
  rintro ⟨x,y⟩
  apply Subtype.ext
  change extendScalarsInclusion (Polynomial.toLaurent (R := R)) i
      (moduleDifference (R := R) M N e (x,y)) =
    LaurentPolynomial.Cutoff.plusEmbedding (i x) -
      action g (LaurentPolynomial.Cutoff.minusEmbedding (j y))
  exact moduleDifference_coordinates M N i j s hs e x y

include i r j s hr hs in
/-- Specified chart retractions produce a finite-projective model of the unchanged module
differential. -/
theorem exists_moduleDifference_model :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite R (P.X k) ∧ Module.Projective R (P.X k)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex (moduleDifference (R := R) M N e)) P) := by
  obtain ⟨P, hP, hfin, ⟨f⟩⟩ := exists_projector_cech_model p q g h
    (retractMatrix_idempotent i r hr) (retractMatrix_idempotent j s hs)
    (chartProjector_transition M N i r s hr e) (chartTransition_inverse M N i r j s hs e)
    (chartTransition_inverse_rev M N i r j s hr e) (chartTransition_projector M N i j s hs e)
  exact ⟨P, hP, hfin, ⟨(HomotopyEquiv.ofIso (coordinateCechIso M N i r j s hr hs e)).trans f⟩⟩

end ModuleCat.LaurentCech

namespace ModuleCat.LaurentCech
open ModuleCat Module.Projective ModuleCat
variable {R : Type u} [CommRing R]

/-- Finite-projective polynomial chart modules give a finite-projective model of the original
signed Cech complex. -/
theorem exists_moduleDifference_model_of_finite_projective
    (M N : ModuleCat.{u} R[X]) [Module.Finite R[X] M] [Module.Projective R[X] M]
    [Module.Finite R[X] N] [Module.Projective R[X] N]
    (e : (extendScalars (negativeScalarMap R)).obj N ≅
      (extendScalars (Polynomial.toLaurent (R := R))).obj M) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite R (P.X k) ∧ Module.Projective R (P.X k)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex (moduleDifference (R := R) M N e)) P) := by
  obtain ⟨m, r, i, _, _, hr⟩ := Module.Finite.exists_comp_eq_id_of_projective R[X] M
  obtain ⟨n, s, j, _, _, hs⟩ := Module.Finite.exists_comp_eq_id_of_projective R[X] N
  exact exists_moduleDifference_model M N i r j s hr hs e

end ModuleCat.LaurentCech
