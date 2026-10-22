/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenIdealPullback
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-! # Detection of original annihilation on open covers

Annihilation is detected by invertibility of the original quotient unit.
This avoids any replacement of the original affine ideals or section actions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u v
variable {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
  (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]

/-- Original ideal annihilation is local for an open cover, using actual pullbacks. -/
theorem killedByIdealSheaf_of_pullback_openCover
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    (J : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∀ i, killedByIdealSheaf (J.comap (a i)) ((pullback (a i)).obj M)) :
    killedByIdealSheaf J M := by
  have hu : IsIso ((idealSheafQuotientUnit X J).app M) := by
    apply isIso_of_restrict_openCover Y a hcover
    intro i
    have hv : IsIso ((idealSheafQuotientUnit (Y i) (J.comap (a i))).app
        ((pullback (a i)).obj M)) :=
      (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf
        (J.comap (a i)).subschemeι ((pullback (a i)).obj M)).mpr
        (by simpa only [IdealSheafData.ker_subschemeι] using hM i)
    have hw : IsIso ((pullback (a i)).map ((idealSheafQuotientUnit X J).app M) ≫
        (idealSheafPullbackQuotientIso (a i) J M).hom) := by
      rw [idealSheafPullbackQuotientIso_unit]
      exact hv
    let := hw
    have hp : IsIso ((pullback (a i)).map ((idealSheafQuotientUnit X J).app M)) :=
      IsIso.of_isIso_comp_right _ (idealSheafPullbackQuotientIso (a i) J M).hom
    exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback (a i)) _).mpr hp
  have hh := (pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf
    J.subschemeι M).mp hu
  simpa only [IdealSheafData.ker_subschemeι] using hh

end AlgebraicGeometry.Scheme.Modules.Coherent
