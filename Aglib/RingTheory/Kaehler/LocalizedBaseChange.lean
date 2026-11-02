/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Differential comparison after original source localizations

For a pushout square, formally etale extensions of the original source and
of its base change have the same base-changed differential module. This is
applied to the literal localizations at corresponding prime ideals.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace KaehlerDifferential

variable (R S T B U L : Type*)
  [CommRing R] [CommRing S] [CommRing T] [CommRing B] [CommRing U] [CommRing L]
  [Algebra R S] [Algebra R T] [Algebra R B] [Algebra R U]
  [Algebra S B] [Algebra T B] [IsScalarTower R S B] [IsScalarTower R T B]
  [Algebra S U] [IsScalarTower R S U]
  [Algebra S L] [Algebra U L] [IsScalarTower S U L]
  [Algebra B L] [IsScalarTower S B L]
  [Algebra T L] [IsScalarTower T B L]
  [Algebra.IsPushout R T S B]
  [Algebra.FormallyEtale S U] [Algebra.FormallyEtale B L]

/-- The comparison keeps all original differential modules and algebra actions. -/
def localizedBaseChangeEquiv : L ⊗[U] Ω[U⁄R] ≃ₗ[L] Ω[L⁄T] :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
      (tensorKaehlerEquivOfFormallyEtale R S U).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange S U L L Ω[S⁄R] ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S B L L Ω[S⁄R]).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
      (tensorKaehlerEquiv R T S B) ≪≫ₗ
    tensorKaehlerEquivOfFormallyEtale T B L

include S B in
/-- Faithfully flat detection on the original localized source descends
formal unramifiedness from the localized base change. -/
theorem formallyUnramified_of_localizedBaseChange
    [Module.FaithfullyFlat U L] [Algebra.FormallyUnramified T L] :
    Algebra.FormallyUnramified R U := by
  let : Subsingleton (L ⊗[U] Ω[U⁄R]) := (localizedBaseChangeEquiv R S T B U L).subsingleton
  let : Subsingleton Ω[U⁄R] := Module.FaithfullyFlat.lTensor_reflects_triviality U L _
  exact ⟨inferInstance⟩

end KaehlerDifferential
