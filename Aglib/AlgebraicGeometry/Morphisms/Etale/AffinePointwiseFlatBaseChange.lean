/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.AffinePointwise
public import Aglib.RingTheory.Etale.PointwiseFlatBaseChange

/-! # Actual affine pointwise etale descent under flat base change

The specified point of the native tensor-product spectrum detects etaleness
at its actual original image. Flatness of the original source algebra is not
assumed. The ring-theoretic descent retains its Noetherian base hypothesis.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

local instance : Algebra S (T ⊗[R] S) := Algebra.TensorProduct.rightAlgebra

/-- Etaleness at the original chosen tensor-product point descends to its actual image. -/
theorem specAlgebraMap_etaleAt_of_flat_baseChange
    [IsNoetherianRing R] [Algebra.FinitePresentation R S] [Module.Flat R T]
    (Q : PrimeSpectrum (T ⊗[R] S))
    (h : (Spec.algebraMap T (T ⊗[R] S)).etaleAt Q) :
    (Spec.algebraMap R S).etaleAt ((Spec.algebraMap S (T ⊗[R] S)) Q) := by
  let p := PrimeSpectrum.comap (algebraMap S (T ⊗[R] S)) Q
  let : Q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let : Algebra.IsEtaleAt T Q.asIdeal := (specAlgebraMap_etaleAt_iff Q).mp h
  exact (specAlgebraMap_etaleAt_iff p).mpr
    (Algebra.isEtaleAt_of_flat_baseChange_of_noetherian R S T p.asIdeal Q.asIdeal)

end AlgebraicGeometry.Scheme.Hom
