/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.FiniteMatrixBaseChange
public import Aglib.Algebra.Category.ModuleCat.ScalarExtensionUnit
public import Aglib.Algebra.Polynomial.Laurent.ProjectorCech

/-! # Original Laurent module Cech maps and their projector coordinates

Positive and negative scalar extensions are kept distinct by their explicit ring maps.
The original adjunction units define the signed module differential. Actual chart and
Laurent image isomorphisms retain the given finite-free retractions, and the resulting
coordinate square preserves both restrictions and the minus sign.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Polynomial/Laurent/ModuleCech.lean` from the
supplied frozen Quillen snapshot.
SHA-256: `af60650fa777b54953ecc6737ce2e3fee46edee0204cd0c8d20beac51209bdbb`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open Polynomial LaurentPolynomial
open scoped TensorProduct Matrix ChangeOfRings LaurentPolynomial
universe u v
open LaurentPolynomial.Projector

namespace ModuleCat.LaurentCech
open ModuleCat Module.Projective
variable {R : Type u} [CommRing R]

/-- The actual polynomial chart module is its projector image over the original base ring. -/
def polynomialRetractImageIso (M : ModuleCat.{u} R[X]) {n : ℕ}
    (i : M →ₗ[R[X]] Fin n → R[X]) (r : (Fin n → R[X]) →ₗ[R[X]] M)
    (h : r.comp i = LinearMap.id) :
    (restrictScalars (Polynomial.C : R →+* R[X])).obj M ≅
      ModuleCat.of R (LinearMap.range (polynomialAction (retractMatrix i r))) := by
  letI : Module R M := Module.compHom M (Polynomial.C : R →+* R[X])
  letI : IsScalarTower R R[X] M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact ((retractMatrixImageIso i r h).restrictScalars R).toModuleIso

end ModuleCat.LaurentCech

namespace ModuleCat.LaurentCech
open ModuleCat Module.Projective
variable {R : Type u} [CommRing R]

/-- The actual positive Laurent extension is its mapped projector image over the base ring. -/
def laurentRetractImageIso (M : ModuleCat.{u} R[X]) {n : ℕ}
    (i : M →ₗ[R[X]] Fin n → R[X]) (r : (Fin n → R[X]) →ₗ[R[X]] M)
    (h : r.comp i = LinearMap.id) :
    (restrictScalars (LaurentPolynomial.C : R →+* R[T;T⁻¹])).obj
      ((extendScalars (Polynomial.toLaurent (R := R))).obj M) ≅
        ModuleCat.of R (LinearMap.range (action (plusMatrix (retractMatrix i r)))) := by
  let T := (extendScalars (Polynomial.toLaurent (R := R))).obj M
  letI : Module R T := Module.compHom T (LaurentPolynomial.C : R →+* R[T;T⁻¹])
  letI : IsScalarTower R R[T;T⁻¹] T := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e := (extendScalarsRetractImageIso (Polynomial.toLaurent (R := R)) M i r h).toLinearEquiv
  exact (e.restrictScalars R).toModuleIso

end ModuleCat.LaurentCech

namespace ModuleCat.LaurentCech
open ModuleCat Module.Projective
variable (R : Type u) [CommRing R]

/-- The literal negative chart scalar map, including Laurent variable inversion. -/
def negativeScalarMap : R[X] →+* R[T;T⁻¹] :=
  (LaurentPolynomial.invert : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]).toAlgHom.toRingHom.comp
    Polynomial.toLaurent

/-- The original positive scalar map preserves the base-ring coefficient inclusion. -/
theorem positive_constants : (LaurentPolynomial.C : R →+* R[T;T⁻¹]) =
    Polynomial.toLaurent.comp Polynomial.C := by
  ext x
  simp

/-- The original negative scalar map preserves the same base-ring coefficient inclusion. -/
theorem negative_constants : (LaurentPolynomial.C : R →+* R[T;T⁻¹]) =
    (negativeScalarMap R).comp Polynomial.C := by
  ext x
  simp [negativeScalarMap]

variable {R} (M N : ModuleCat.{u} R[X])

/-- The signed two-chart differential formed from the actual scalar-extension adjunction
units. -/
def moduleDifference
    (e : (extendScalars (negativeScalarMap R)).obj N ≅
      (extendScalars (Polynomial.toLaurent (R := R))).obj M) :
    ((restrictScalars (Polynomial.C : R →+* R[X])).obj M ×
      (restrictScalars (Polynomial.C : R →+* R[X])).obj N) →ₗ[R]
        (restrictScalars (LaurentPolynomial.C : R →+* R[T;T⁻¹])).obj
          ((extendScalars (Polynomial.toLaurent (R := R))).obj M) :=
  (restrictedExtensionUnit Polynomial.C Polynomial.toLaurent LaurentPolynomial.C
      (positive_constants R) M).hom.comp (LinearMap.fst R _ _) -
    ((restrictedExtensionUnit Polynomial.C (negativeScalarMap R) LaurentPolynomial.C
        (negative_constants R) N ≫
      (restrictScalars (LaurentPolynomial.C : R →+* R[T;T⁻¹])).map e.hom).hom).comp
        (LinearMap.snd R _ _)

/-- The original differential is the positive unit tensor minus the transported negative unit
tensor. -/
theorem moduleDifference_apply
    (e : (extendScalars (negativeScalarMap R)).obj N ≅
      (extendScalars (Polynomial.toLaurent (R := R))).obj M)
    (a : (restrictScalars (Polynomial.C : R →+* R[X])).obj M)
    (b : (restrictScalars (Polynomial.C : R →+* R[X])).obj N) :
    moduleDifference (R := R) M N e (a,b) =
      @Sub.sub ((extendScalars (Polynomial.toLaurent (R := R))).obj M) inferInstance
        ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],Polynomial.toLaurent] (a : M))
        (e.hom ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],negativeScalarMap R] (b : N))) := rfl


end ModuleCat.LaurentCech

namespace ModuleCat.LaurentCech
open ModuleCat Module.Projective LaurentPolynomial.Cutoff
variable {R : Type u} [CommRing R]
variable (M N : ModuleCat.{u} R[X]) {m n : ℕ}

/-- The actual positive unit tensor becomes the original positive polynomial restriction. -/
theorem positive_inclusion_unit (i : M →ₗ[R[X]] Fin m → R[X]) (x : M) :
    extendScalarsInclusion (Polynomial.toLaurent (R := R)) i
      ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],Polynomial.toLaurent] x :
        (extendScalars (Polynomial.toLaurent (R := R))).obj M) = plusEmbedding (i x) := by
  funext k
  change (extendScalarsPiIso (Polynomial.toLaurent (R := R)) m).hom
    ((extendScalars (Polynomial.toLaurent (R := R))).map (ModuleCat.ofHom i)
      ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],Polynomial.toLaurent] x)) k = toLaurent (i x k)
  rw [ModuleCat.ExtendScalars.map_tmul, extendScalarsPiIso_tmul, mul_one]
  rfl

/-- The actual negative unit tensor becomes the original inverse-coordinate restriction. -/
theorem negative_inclusion_unit (j : N →ₗ[R[X]] Fin n → R[X]) (x : N) :
    extendScalarsInclusion (negativeScalarMap R) j
      ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],negativeScalarMap R] x :
        (extendScalars (negativeScalarMap R)).obj N) = minusEmbedding (j x) := by
  funext k
  change (extendScalarsPiIso (negativeScalarMap R) n).hom
    ((extendScalars (negativeScalarMap R)).map (ModuleCat.ofHom j)
      ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],negativeScalarMap R] x)) k = invert (toLaurent (j x k))
  rw [ModuleCat.ExtendScalars.map_tmul, extendScalarsPiIso_tmul, mul_one]
  rfl

/-- The original signed module differential retains its literal two-chart matrix coordinate
square. -/
theorem moduleDifference_coordinates
    (i : M →ₗ[R[X]] Fin m → R[X]) (j : N →ₗ[R[X]] Fin n → R[X])
    (s : (Fin n → R[X]) →ₗ[R[X]] N) (hs : s.comp j = LinearMap.id)
    (e : (extendScalars (negativeScalarMap R)).obj N ≅
      (extendScalars (Polynomial.toLaurent (R := R))).obj M)
    (a : (restrictScalars (Polynomial.C : R →+* R[X])).obj M)
    (b : (restrictScalars (Polynomial.C : R →+* R[X])).obj N) :
    extendScalarsInclusion (Polynomial.toLaurent (R := R)) i
        (moduleDifference (R := R) M N e (a,b)) =
      plusEmbedding (i a) - action
        (extensionTransitionMatrix (Polynomial.toLaurent (R := R)) (negativeScalarMap R) i s e)
        (minusEmbedding (j b)) := by
  rw [moduleDifference_apply]
  erw [map_sub]
  rw [positive_inclusion_unit]
  have ht := extensionTransitionMatrix_inclusion (Polynomial.toLaurent (R := R))
    (negativeScalarMap R) i j s hs e
      ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],negativeScalarMap R] (b : N) :
        (extendScalars (negativeScalarMap R)).obj N)
  rw [negative_inclusion_unit] at ht
  exact congrArg (fun x => plusEmbedding (i a) - x) ht.symm

end ModuleCat.LaurentCech
