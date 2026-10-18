/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec

/-! # Original scalar base change under a coefficient isomorphism

The actual pullback unit is natural in the coefficient. Its original scalar
cohomology mate therefore transports invertibility and surjectivity through
the original cohomology maps of a coefficient isomorphism.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (σ : R →+* S)
  {M N : X.Modules} (e : M ≅ N) (n : ℕ)

include e in
/-- The original scalar cohomology comparison is invertible for one coefficient exactly
when it is invertible for an actually isomorphic coefficient. -/
theorem moduleCohomologyBaseChangeMap_isIso_iff_of_coefficientIso :
    IsIso (moduleCohomologyBaseChangeMap f σ M n) ↔
      IsIso (moduleCohomologyBaseChangeMap f σ N n) := by
  let p := Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let b := Limits.pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let Y := Limits.pullback f (Spec.map (CommRingCat.ofHom σ))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let A := moduleCohomologyFunctorOfHom X α n
  let B := moduleCohomologyFunctorOfHom Y β n
  let E := (ModuleCat.extendScalars σ).mapIso (A.mapIso e)
  let F := B.mapIso ((Scheme.Modules.pullback p).mapIso e)
  have h := moduleCohomologyTensorMap_naturality p σ α β
    (moduleSectionsBaseChangeScalars p b f σ Limits.pullback.condition)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N)
    e.hom ((Scheme.Modules.pullback p).map e.hom)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality e.hom) n
  change E.hom ≫ moduleCohomologyBaseChangeMap f σ N n =
    moduleCohomologyBaseChangeMap f σ M n ≫ F.hom at h
  rw [← isIso_comp_right_iff (moduleCohomologyBaseChangeMap f σ M n) F.hom, ← h,
    isIso_comp_left_iff]

include e in
/-- Surjectivity of the original scalar cohomology comparison is invariant under an
actual source coefficient isomorphism. -/
theorem moduleCohomologyBaseChangeMap_epi_iff_of_coefficientIso :
    Epi (moduleCohomologyBaseChangeMap f σ M n) ↔
      Epi (moduleCohomologyBaseChangeMap f σ N n) := by
  let p := Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let b := Limits.pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let Y := Limits.pullback f (Spec.map (CommRingCat.ofHom σ))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let A := moduleCohomologyFunctorOfHom X α n
  let B := moduleCohomologyFunctorOfHom Y β n
  let E := (ModuleCat.extendScalars σ).mapIso (A.mapIso e)
  let F := B.mapIso ((Scheme.Modules.pullback p).mapIso e)
  have h := moduleCohomologyTensorMap_naturality p σ α β
    (moduleSectionsBaseChangeScalars p b f σ Limits.pullback.condition)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N)
    e.hom ((Scheme.Modules.pullback p).map e.hom)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality e.hom) n
  change E.hom ≫ moduleCohomologyBaseChangeMap f σ N n =
    moduleCohomologyBaseChangeMap f σ M n ≫ F.hom at h
  rw [← epi_comp_iff_of_isIso (moduleCohomologyBaseChangeMap f σ M n) F.hom, ← h,
    epi_comp_iff_of_epi]

end AlgebraicGeometry.Scheme.Cohomology
