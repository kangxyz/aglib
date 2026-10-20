/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

import Aglib.RingTheory.Etale.Reduction.PointBijection
import Aglib.RingTheory.FiniteEtale.CoefficientInertia
import Aglib.RingTheory.FiniteEtale.TensorHopf
import Aglib.RingTheory.FiniteEtale.TorsorCoordinates
import Aglib.RingTheory.IntegralClosure.Inertia.FixesPoints
import Aglib.RingTheory.IntegralClosure.Inertia.HorizontalModel
import Aglib.RingTheory.IntegralClosure.Inertia.Inseparable
import Aglib.RingTheory.Valuation.ResidualInertia

/-!
Checks the intended native interfaces at their actual hypothesis boundaries:
restriction does not require fields or finite algebras, the algebraic-closure
inertia criterion does not require a perfect fraction field, and the coefficient
point supplier keeps its actual transporter premise.
-/

open scoped TensorProduct

section Restriction

variable (R K A B : Type*) [CommRing R] [CommRing K] [Algebra R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [CommRing B] [Algebra K B] [Algebra R B] [IsScalarTower R K B]

example (f : A →ₐ[K] B) (x : integralClosure R A) :
    (integralClosure.restrictHom R K f x : B) = f x := rfl

end Restriction

section ArbitraryResidue

universe u
variable (R K A : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Algebra.Etale K A]

example (Q : Ideal (integralClosure R (AlgebraicClosure K))) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)]
    (h : ∀ σ ∈ Q.inertia (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      ∀ f : A →ₐ[K] AlgebraicClosure K, σ.toAlgHom.comp f = f) :
    Algebra.Etale R (integralClosure R A) :=
  integralClosure.Inertia.Inseparable.model_etale_of_algebraicClosure_inertia_trivial R K A Q h

end ArbitraryResidue

section CoefficientPoint

universe u
variable (K Ω A C : Type u) [CommRing K] [CommRing Ω] [Algebra K Ω]
  [CommRing A] [Algebra K A] [CommRing C] [Algebra K C]

example (δ : A →ₐ[K] A ⊗[K] C)
    (hδ : Function.Bijective (Algebra.FiniteEtale.GenericMaps.transporter K A C δ))
    (f g : A →ₐ[K] Ω) :
    ∃ h : C →ₐ[K] Ω,
      (Algebra.TensorProduct.lift f h (fun _ _ => .all _ _)).comp δ = g :=
  Algebra.FiniteEtale.TorsorExtension.exists_coefficient_point K Ω A C δ hδ f g

end CoefficientPoint
