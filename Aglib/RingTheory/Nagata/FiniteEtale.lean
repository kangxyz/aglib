/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Basic

/-! # Integral closures of etale generic algebras over Japanese domains -/

@[expose] public noncomputable section

universe u

namespace integralClosure

/-- Japanese finiteness applies to every field factor of the actual etale
generic algebra. The original base need not be normal, and the algebra may
be split or zero. -/
theorem finite_of_etale_of_isJapaneseRing
    (R K A : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [Algebra.Etale K A] (hR : IsJapaneseRing.{u, 0} R) :
    Module.Finite R (integralClosure R A) := by
  obtain ⟨ι, hι, L, hL, hKL, e, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  let := hι
  let := hL
  let := hKL
  let (i : ι) : Algebra R (L i) :=
    ((algebraMap K (L i)).comp (algebraMap R K)).toAlgebra
  let (i : ι) : IsScalarTower R K (L i) := IsScalarTower.of_algebraMap_eq' rfl
  let (i : ι) : Module.Finite K (L i) := (hfin i).1
  let (i : ι) : Module.Finite R (integralClosure R (L i)) :=
    hR.finite_integralClosure_of_isFractionRing K (L i)
  let φ : integralClosure R A →ₐ[R] (∀ i, integralClosure R (L i)) :=
    AlgHom.pi fun i =>
      (((Pi.evalAlgHom K L i).comp e.toAlgHom).restrictScalars R).mapIntegralClosure
  apply Module.Finite.of_injective φ.toLinearMap
  intro x y h
  apply Subtype.ext
  apply e.injective
  funext i
  exact congrArg Subtype.val (congrFun h i)

end integralClosure
