/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteSubalgebraModel
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ModelBaseFactor
public import Aglib.RingTheory.Localization.FiniteSubalgebra

/-! # Actual finite generic models over a dense principal open -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FinitePresentationDescent

universe u

/-- A finite scheme over the fraction field of a Noetherian domain has an actual
finite model over a nonempty principal localization of that same domain. The model
retains the original generic scheme and its canonical cartesian comparison. -/
theorem exists_finiteModel_over_principalLocalization
    (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsFinite f] :
    ∃ r : R, r ≠ 0 ∧ ∃ v : Localization.Away r →ₐ[R] K,
      Function.Injective v ∧
      ∃ M : Model (Spec.map (CommRingCat.ofHom v.toRingHom)) f, IsFinite M.f := by
  obtain ⟨s, M, hM⟩ :=
    FiniteTypeSubalgebraLimit.exists_finiteModel_over_finiteTypeSubalgebra_of_noetherian R K f
  have : IsFinite M.f := hM
  obtain ⟨r, hr, v, i, hv, hi⟩ :=
    IsFractionRing.exists_principal_localization_of_fg_subalgebra R K
      (Algebra.FiniteTypeSubalgebraLimit.stage R K s) ⟨s, rfl⟩
  have hbase : Spec.map (CommRingCat.ofHom v.toRingHom) ≫
      Spec.map (CommRingCat.ofHom i.toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.FiniteTypeSubalgebraLimit.stage R K s).val.toRingHom) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom hi
  let N := M.factorBase (Spec.map (CommRingCat.ofHom v.toRingHom))
    (Spec.map (CommRingCat.ofHom i.toRingHom)) hbase
  refine ⟨r, hr, v, hv, N, ?_⟩
  change IsFinite (pullback.snd M.f (Spec.map (CommRingCat.ofHom i.toRingHom)))
  infer_instance

end AlgebraicGeometry.Scheme.FinitePresentationDescent
