/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction

/-! # Strict models on open neighborhoods

A strict model is witnessed by an actual derived isomorphism. Two local
models can be shrunk to a common neighborhood, and arbitrary open-immersion
witnesses yield literal open-neighborhood witnesses.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/LocalModels.lean`,
archive SHA-256
`16c127c5b7a5874cb4d841e1161b436190c35aeb08802b89cb19fd8c76ad1d48`,
source SHA-256 `4a5c9fc79cdf45e0b7cf020745bf4199b8b4de78876f7c3ff25987883c6a8330`.
Admitted subset: HasStrictModel, transport/restriction/shrinking, common-neighborhood and
  open-immersion witnesses.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open scoped ZeroObject

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Complex

attribute [local instance] Scheme.Modules.standardHasDerivedCategory

/-- A complex admits a strict representative globally in the actual
quasi-isomorphism localization. This is stronger than local perfectness. -/
def HasStrictModel {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) : Prop :=
  ∃ P : StrictPerfect X, Nonempty ((DerivedCategory.Q (C := X.Modules)).obj K ≅ (DerivedCategory.Q
    (C := X.Modules)).obj P.obj)

/-- An actual chain isomorphism transports a strict derived model. -/
theorem HasStrictModel.of_iso {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    (hK : HasStrictModel K) (e : K ≅ L) : HasStrictModel L := by
  obtain ⟨P, ⟨hP⟩⟩ := hK
  exact ⟨P, ⟨(DerivedCategory.Q (C := X.Modules)).mapIso e.symm ≪≫ hP⟩⟩

/-- Strict representatives restrict along actual open immersions. -/
theorem HasStrictModel.restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K : CochainComplex X.Modules ℤ} (hK : HasStrictModel K) : HasStrictModel
      ((Scheme.Modules.Complex.restrict
      j).obj K) := by
  obtain ⟨P, ⟨e⟩⟩ := hK
  exact ⟨⟨(Scheme.Modules.Complex.restrict j).obj P.obj, strictPerfect_restrict j P.property⟩,
    ⟨restrictDerivedIso j e⟩⟩

/-- A strict local model remains available after shrinking the open. -/
theorem HasStrictModel.restrict_of_le {X : Scheme.{u}} {U V : X.Opens}
    (h : V ≤ U) {K : CochainComplex X.Modules ℤ} (hK : HasStrictModel
      ((Scheme.Modules.Complex.restrict U.ι).obj
      K)) :
    HasStrictModel ((Scheme.Modules.Complex.restrict V.ι).obj K) := by
  let j := X.homOfLE h
  let e : Scheme.Modules.Complex.restrict U.ι ⋙ Scheme.Modules.Complex.restrict j ≅
    Scheme.Modules.Complex.restrict V.ι :=
    restrictCompIso j U.ι ≪≫ eqToIso (restrict_congr (by simp [j]))
  exact (hK.restrict j).of_iso (e.app K)

/-- Two locally perfect complexes have strict derived representatives on
one common neighborhood of a chosen point. -/
theorem exists_common_strictModels {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    (hK : locallyPerfect X K) (hL : locallyPerfect X L) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      HasStrictModel ((Scheme.Modules.Complex.restrict U.ι).obj K) ∧ HasStrictModel
        ((Scheme.Modules.Complex.restrict U.ι).obj L) := by
  obtain ⟨U, hxU, P, eP⟩ := hK x
  obtain ⟨V, hxV, Q, eQ⟩ := hL x
  exact ⟨U ⊓ V, ⟨hxU, hxV⟩,
    HasStrictModel.restrict_of_le inf_le_left ⟨P, eP⟩,
    HasStrictModel.restrict_of_le inf_le_right ⟨Q, eQ⟩⟩

/-- Open-immersion strict-model witnesses give genuine local perfectness.
This allows finite successive shrinkings to be kept as a composite immersion. -/
theorem locallyPerfect_of_openImmersion_models {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (hK : ∀ x : X, ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y),
      j y = x ∧ HasStrictModel ((@Scheme.Modules.Complex.restrict Y X j hj).obj K)) :
        locallyPerfect X K := by
  intro x
  obtain ⟨Y, j, hj, y, hy, h⟩ := hK x
  let := hj
  let U : X.Opens := j.opensRange
  let t : U.toScheme ⟶ Y := j.isoOpensRange.inv
  let e : Scheme.Modules.Complex.restrict j ⋙ Scheme.Modules.Complex.restrict t ≅
    Scheme.Modules.Complex.restrict U.ι :=
    restrictCompIso t j ≪≫ eqToIso (restrict_congr j.isoOpensRange_inv_comp)
  obtain ⟨P, eP⟩ := (h.restrict t).of_iso (e.app K)
  refine ⟨U, ?_, P, eP⟩
  exact ⟨y, hy⟩

end AlgebraicGeometry.Scheme.Modules.Complex
