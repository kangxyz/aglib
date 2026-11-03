/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.ExteriorPower.ScalarExtension
public import Aglib.RingTheory.Kaehler.Exterior.Map
public import Mathlib.RingTheory.Kaehler.TensorProduct


/-!
# RingTheory / Kaehler / Exterior / BaseChange

Source: `IntegralTrace/RawImageBound.lean`.
Incoming SHA256: `cb04954aedb63ec4a5105adff32da7b556b8d14eaada1dbceb2ba93a787cda12`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open scoped TensorProduct

universe u v w

namespace KaehlerDifferential

variable (Λ : Type w) (R : Type u) (S : Type v)
  [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]

/-- The sole native raw map agrees with the actual tensor/exterior composite.
This is an equation, not a second implementation of the raw arrow. -/
theorem mapExteriorBaseChange_eq_tensorComposite (n : ℕ) :
    mapExteriorBaseChange Λ R S n =
      (exteriorPower.map n (mapBaseChange Λ R S)).comp
        (exteriorPower.tensorBaseChangeEquiv (R := R) S
          (KaehlerDifferential Λ R) n).symm.toLinearMap := by
  apply (TensorProduct.isBaseChange R (⋀[R]^n (KaehlerDifferential Λ R)) S).algHom_ext'
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change mapExteriorBaseChange Λ R S n ((1 : S) ⊗ₜ[R] exteriorPower.ιMulti R n v) =
    exteriorPower.map n (mapBaseChange Λ R S)
      (exteriorPower.tensorBaseChangeBackward S (KaehlerDifferential Λ R) n
        ((1 : S) ⊗ₜ[R] exteriorPower.ιMulti R n v))
  rw [mapExteriorBaseChange_tmul, one_smul, mapExterior_ιMulti,
    exteriorPower.tensorBaseChangeBackward_tmul, one_smul,
    exteriorPower.mapAlgebra_ιMulti, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact ((mapBaseChange_tmul Λ R S 1 (v i)).trans (one_smul S _)).symm
/-- Original raw scalar extension changes the source presentation, not the image. -/
theorem mapExteriorBaseChange_range (n : ℕ) :
    LinearMap.range (mapExteriorBaseChange Λ R S n) =
      LinearMap.range (exteriorPower.map n (mapBaseChange Λ R S)) := by
  rw [mapExteriorBaseChange_eq_tensorComposite]
  let e := exteriorPower.tensorBaseChangeEquiv (R := R) S (KaehlerDifferential Λ R) n
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨e.symm v, rfl⟩
  · rintro ⟨v, hv⟩
    refine ⟨e v, ?_⟩
    change exteriorPower.map n (mapBaseChange Λ R S) (e.symm (e v)) = z
    exact (congrArg (exteriorPower.map n (mapBaseChange Λ R S))
      (e.symm_apply_apply v)).trans hv

end KaehlerDifferential
