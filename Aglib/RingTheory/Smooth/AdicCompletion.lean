/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.AdicCompletion.FiniteModule
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Lifting closed-fibre maps into finite algebras

Over a Noetherian ideal-adically complete ring, formal smoothness lifts quotient-valued maps
into a finite algebra. The actual quotient tensor-base-change map on algebra homomorphisms
is consequently surjective. Neither a local-ring nor an etaleness hypothesis is needed.

## Extraction basis

Transferred existing declarations from
`R5Lab/AlgebraicGeometry/LocalRing/FiniteComplete.lean` at revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, source SHA-256
`db6c0a91383357bf2289b3077c6664e9ae31eb82068ab5add2be5702ba24726f`, lines 44–50.
Transferred existing declarations from
`R5Lab/AlgebraicGeometry/LocalRing/ResidueLift.lean` at revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, source SHA-256
`bb3feea43f8c1adf7e1468e22759fadcc67cdec9ba0c26e566b6e7686b448243`, lines 16–31.
The stated hypotheses and chosen maps are retained; declarations use native mathematical
namespaces and canonical carriers. Source correspondence is separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open TensorProduct

namespace Algebra.FormallySmooth

variable (R : Type*) [CommRing R] [IsNoetherianRing R]
  (I : Ideal R) [IsAdicComplete I R]

/-- Formal smoothness lifts algebra maps to a finite algebra from its closed fibre. -/
theorem exists_mkₐ_comp_eq_of_finite {A B : Type*} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.FormallySmooth R A]
    (f : A →ₐ[R] B ⧸ I.map (algebraMap R B)) :
    ∃ g : A →ₐ[R] B,
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R B))).comp g = f := by
  have := IsAdicComplete.map_algebraMap_of_finite R I B
  exact Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete f

variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [Module.Finite R B] [Algebra.FormallySmooth R A]

/-- Actual residue tensor-base-change maps of algebras lift to the complete base. -/
theorem tensorProduct_map_surjective_of_finite :
    Function.Surjective
      (fun g : A →ₐ[R] B =>
        (Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I)) g :
          (R ⧸ I) ⊗[R] A →ₐ[R ⧸ I] (R ⧸ I) ⊗[R] B)) := by
  intro f
  let eB := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  let f' : A →ₐ[R] B ⧸ I.map (algebraMap R B) :=
    (eB.symm.toAlgHom.restrictScalars R).comp
      ((f.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  obtain ⟨g, hg⟩ := exists_mkₐ_comp_eq_of_finite R I f'
  refine ⟨g, ?_⟩
  apply Algebra.TensorProduct.ext_ring
  ext a
  have h := congrArg eB (AlgHom.congr_fun hg a)
  simpa [f', eB] using h

end Algebra.FormallySmooth
