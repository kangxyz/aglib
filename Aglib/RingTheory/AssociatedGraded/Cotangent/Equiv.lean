/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.ReesAlgebra.Equiv
public import Aglib.RingTheory.AssociatedGraded.Cotangent.Graded
public import Aglib.RingTheory.AssociatedGraded.NativeRing
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Original cotangent-polynomial kernels under ring equivalences

The original Rees map induces the native quotient equivalence. Its complete
polynomial square retains the original coefficient quotient and degree-one
symbols, and hence transports the entire canonical kernel.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w

namespace Ideal

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

private theorem reesMapEquiv_coefficient (e : A ≃+* B) (I : Ideal A) :
    (reesAlgebra.mapEquiv e I).toRingHom.comp (algebraMap A (reesAlgebra I)) =
      (algebraMap B (reesAlgebra (I.map e.toRingHom))).comp e.toRingHom := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change (Polynomial.C a).map e.toRingHom = Polynomial.C (e a)
  exact Polynomial.map_C e.toRingHom

/-- The original defining ideal maps to the defining ideal of the original image ideal. -/
theorem associatedGradedIdeal_map_equiv (e : A ≃+* B) (I : Ideal A) :
    I.associatedGradedIdeal.map (reesAlgebra.mapEquiv e I).toRingHom =
      (I.map e.toRingHom).associatedGradedIdeal := by
  rw [associatedGradedIdeal, Ideal.map_map, reesMapEquiv_coefficient,
    ← Ideal.map_map]
  rfl

/-- The native associated graded quotient of the original coefficientwise Rees equivalence. -/
def associatedGradedEquiv (e : A ≃+* B) (I : Ideal A) :
    I.associatedGraded ≃+* (I.map e.toRingHom).associatedGraded :=
  Ideal.quotientEquiv I.associatedGradedIdeal (I.map e.toRingHom).associatedGradedIdeal
    (reesAlgebra.mapEquiv e I) (associatedGradedIdeal_map_equiv e I).symm

/-- Original Rees classes are transported by the same original Rees map. -/
theorem associatedGradedEquiv_mk (e : A ≃+* B) (I : Ideal A) (p : reesAlgebra I) :
    associatedGradedEquiv e I (Ideal.Quotient.mk I.associatedGradedIdeal p) =
      Ideal.Quotient.mk (I.map e.toRingHom).associatedGradedIdeal
        (reesAlgebra.map e.toRingHom I p) := rfl

variable {ι : Type w}

/-- Naturality of the entire original canonical polynomial map, including
its original quotient-coefficient map and actual degree-one Rees symbols. -/
theorem cotangentPolynomialMap_equiv_square (e : A ≃+* B) (I : Ideal A) (g : ι → I) :
    (associatedGradedEquiv e I).toRingHom.comp (cotangentPolynomialMap I g).toRingHom =
      (cotangentPolynomialMap (I.map e.toRingHom)
        (fun i => ⟨e.toRingHom (g i),
          Ideal.mem_map_of_mem e.toRingHom (g i).property⟩)).toRingHom.comp
          (MvPolynomial.mapEquiv ι (Ideal.quotientEquiv I (I.map e.toRingHom) e
            (congrArg (fun f : A →+* B => I.map f) e.toRingHom_eq_coe))).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change associatedGradedEquiv e I
      (cotangentPolynomialMap I g (MvPolynomial.C (Ideal.Quotient.mk I a))) =
      cotangentPolynomialMap (I.map e.toRingHom)
        (fun i => ⟨e.toRingHom (g i), Ideal.mem_map_of_mem e.toRingHom (g i).property⟩)
          (MvPolynomial.mapEquiv ι (Ideal.quotientEquiv I (I.map e.toRingHom) e
            (congrArg (fun f : A →+* B => I.map f) e.toRingHom_eq_coe))
            (MvPolynomial.C (Ideal.Quotient.mk I a)))
    rw [MvPolynomial.mapEquiv_apply, MvPolynomial.map_C]
    change associatedGradedEquiv e I
      (cotangentPolynomialMap I g (MvPolynomial.C (Ideal.Quotient.mk I a))) =
      cotangentPolynomialMap (I.map e.toRingHom)
        (fun i => ⟨e.toRingHom (g i), Ideal.mem_map_of_mem e.toRingHom (g i).property⟩)
          (MvPolynomial.C ((Ideal.quotientEquiv I (I.map e.toRingHom) e
            (congrArg (fun f : A →+* B => I.map f) e.toRingHom_eq_coe))
            (Ideal.Quotient.mk I a)))
    rw [Ideal.quotientEquiv_mk, cotangentPolynomialMap_C_mk, cotangentPolynomialMap_C_mk]
    change associatedGradedEquiv e I
      (Ideal.Quotient.mk I.associatedGradedIdeal (algebraMap A (reesAlgebra I) a)) =
      Ideal.Quotient.mk (I.map e.toRingHom).associatedGradedIdeal
        (algebraMap B (reesAlgebra (I.map e.toRingHom)) (e a))
    rw [associatedGradedEquiv_mk]
    congr 1
    exact RingHom.congr_fun (reesMapEquiv_coefficient e I) a
  · intro i
    change associatedGradedEquiv e I (cotangentPolynomialMap I g (MvPolynomial.X i)) =
      cotangentPolynomialMap (I.map e.toRingHom)
        (fun i => ⟨e.toRingHom (g i), Ideal.mem_map_of_mem e.toRingHom (g i).property⟩)
          (MvPolynomial.mapEquiv ι (Ideal.quotientEquiv I (I.map e.toRingHom) e
            (congrArg (fun f : A →+* B => I.map f) e.toRingHom_eq_coe))
            (MvPolynomial.X i))
    rw [MvPolynomial.mapEquiv_apply, MvPolynomial.map_X,
      cotangentPolynomialMap_X, cotangentPolynomialMap_X, associatedGradedEquiv_mk]
    congr 1
    apply Subtype.ext
    change (Polynomial.monomial 1 (g i : A)).map e.toRingHom =
      Polynomial.monomial 1 (e (g i))
    exact Polynomial.map_monomial e.toRingHom

/-- Transport the entire canonical kernel, not only a selected quadratic relation. -/
theorem cotangentPolynomialMap_kernel_equiv (e : A ≃+* B) (I : Ideal A) (g : ι → I) :
    RingHom.ker (cotangentPolynomialMap (I.map e.toRingHom)
        (fun i => ⟨e.toRingHom (g i), Ideal.mem_map_of_mem e.toRingHom (g i).property⟩)).toRingHom =
      (RingHom.ker (cotangentPolynomialMap I g).toRingHom).map
        (MvPolynomial.mapEquiv ι (Ideal.quotientEquiv I (I.map e.toRingHom) e
            (congrArg (fun f : A →+* B => I.map f) e.toRingHom_eq_coe))).toRingHom := by
  let σ := MvPolynomial.mapEquiv ι (Ideal.quotientEquiv I (I.map e.toRingHom) e
            (congrArg (fun f : A →+* B => I.map f) e.toRingHom_eq_coe))
  have h := congrArg RingHom.ker (cotangentPolynomialMap_equiv_square e I g)
  have hinj : Function.Injective (associatedGradedEquiv e I).toRingHom :=
    (associatedGradedEquiv e I).injective
  rw [RingHom.ker_comp_of_injective (f := (associatedGradedEquiv e I).toRingHom)
    (cotangentPolynomialMap I g).toRingHom hinj, ← RingHom.comap_ker] at h
  rw [h, Ideal.map_comap_of_surjective σ.toRingHom σ.surjective]

/-- The same full-kernel law with an explicitly identified original image ideal. -/
theorem cotangentPolynomialMap_kernel_equiv_of_eq (e : A ≃+* B)
    (I : Ideal A) (J : Ideal B) (hJ : I.map e.toRingHom = J) (g : ι → I) :
    RingHom.ker (cotangentPolynomialMap J
        (fun i => ⟨e.toRingHom (g i),
          hJ ▸ Ideal.mem_map_of_mem e.toRingHom (g i).property⟩)).toRingHom =
      (RingHom.ker (cotangentPolynomialMap I g).toRingHom).map
        (MvPolynomial.mapEquiv ι (Ideal.quotientEquiv I J e
          (hJ.symm.trans
            (congrArg (fun f : A →+* B => I.map f) e.toRingHom_eq_coe)))).toRingHom := by
  subst J
  exact cotangentPolynomialMap_kernel_equiv e I g

end Ideal
