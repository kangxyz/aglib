/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.LocalFlat
public import Aglib.RingTheory.Kaehler.LocalizedBaseChange
public import Mathlib.RingTheory.Smooth.Flat

/-! # Pointwise etale descent through a flat base change

The original source is not assumed flat. The chosen local map above a point
is faithfully flat and detects both flatness and the original differential
module. The current formal-etale conclusion is guarded by a Noetherian base.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

universe u

/-- The original prime localization of a finitely presented algebra is flat
whenever that algebra is etale at the specified prime. -/
theorem IsEtaleAt.flat_localization
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [FinitePresentation R S] (q : Ideal S) [q.IsPrime] [IsEtaleAt R q] :
    Module.Flat R (Localization.AtPrime q) := by
  obtain ⟨f, hf, h⟩ := exists_etale_of_isEtaleAt (R := R) q
  let A := Localization.Away f
  let L := Localization.AtPrime q
  let : Etale R A := h
  have hle : Submonoid.powers f ≤ q.primeCompl := Submonoid.powers_le.mpr hf
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A L
    (Submonoid.powers f) q.primeCompl hle
  let : IsScalarTower S A L := IsLocalization.localization_isScalarTower_of_submonoid_le
    A L (Submonoid.powers f) q.primeCompl hle
  let : IsScalarTower R A L := IsScalarTower.to₁₃₄ R S A L
  let : IsLocalization (algebraMapSubmonoid A q.primeCompl) L :=
    IsLocalization.isLocalization_of_submonoid_le A L (Submonoid.powers f) q.primeCompl
      hle
  let : Module.Flat A L := IsLocalization.flat L (algebraMapSubmonoid A q.primeCompl)
  exact Module.Flat.trans R A L

section BaseChange

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- The right-factor `S`-algebra structure on the original tensor product. -/
local instance pointwiseTensorRightAlgebra : Algebra S (T ⊗[R] S) := TensorProduct.rightAlgebra

/-- Etaleness at one specified point after flat base change descends to the
original point. The base is Noetherian; no flatness of the original source,
preimmersion condition, or normality of the base change is assumed. -/
theorem isEtaleAt_of_flat_baseChange_of_noetherian
    [IsNoetherianRing R] [FinitePresentation R S] [Module.Flat R T]
    (p : Ideal S) [p.IsPrime] (Q : Ideal (T ⊗[R] S)) [Q.IsPrime]
    [Q.LiesOver p] [IsEtaleAt T Q] : IsEtaleAt R p := by
  let B := T ⊗[R] S
  let U := Localization.AtPrime p
  let L := Localization.AtPrime Q
  let := Localization.AtPrime.algebraOfLiesOver p Q
  let : IsScalarTower R U L := IsScalarTower.to₁₃₄ R S U L
  let e : S ⊗[R] T ≃ₐ[S] B :=
    { __ := TensorProduct.comm R S T, commutes' _ := rfl }
  let : Module.Flat S B := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let : IsLocalHom (algebraMap U L) := by
    rw [Localization.AtPrime.algebraMap_eq p Q]
    infer_instance
  let : Module.FaithfullyFlat U L := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Module.Flat T L := IsEtaleAt.flat_localization T B Q
  let : Module.Flat R L := Module.Flat.trans R T L
  let : Module.Flat R U := Module.Flat.of_faithfullyFlat_target R U L
  let : FormallyUnramified R U :=
    KaehlerDifferential.formallyUnramified_of_localizedBaseChange R S T B U L
  exact IsEtaleAt.of_flat_localization_of_noetherian R S p

end BaseChange

end Algebra
