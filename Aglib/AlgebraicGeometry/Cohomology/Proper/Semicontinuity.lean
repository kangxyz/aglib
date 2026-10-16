/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Semicontinuity
public import Aglib.AlgebraicGeometry.Cohomology.Fibers.Affine
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Locality
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Upper semicontinuity of original proper fibre cohomology

Proper finiteness and relative flatness internally construct the same
finite-cover model. Its original ordinary fibre comparison transports native
finite-complex semicontinuity to the unchanged fibre-cohomology dimension.
No projective embedding, model family or reducedness assumption is input.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Original ordinary fibre-cohomology dimension is upper semicontinuous for a coherent
relatively flat coefficient under a proper morphism over a Noetherian affine base. -/
theorem upperSemicontinuous_moduleFiberCohomologyDimension_of_proper
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ) :
    UpperSemicontinuous (moduleFiberCohomologyDimension f M q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact D.upperSemicontinuous_fiberCohomologyDimension hU hcover Equiv.ulift hflat q

/-- Intrinsic ordinary fibre-cohomology dimension is upper semicontinuous over every
locally Noetherian target for a proper coherent relatively flat coefficient. -/
theorem upperSemicontinuous_modulePointFiberCohomologyDimension_of_proper
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ) :
    UpperSemicontinuous (modulePointFiberCohomologyDimension f M q) := by
  let D := modulePointFiberCohomologyDimension f M q
  let U := Y.affineOpenCover
  have hlocal (i : U.I₀) : UpperSemicontinuous (D ∘ U.f i) := by
    let A := U.X i
    let j := U.f i
    let : IsLocallyNoetherian (Spec A) := isLocallyNoetherian_of_isOpenImmersion j
    let : IsNoetherianRing A := isLocallyNoetherian_Spec.mp inferInstance
    let a := pullback.fst f j
    let b := pullback.snd f j
    let W := pullback f j
    let N := (Scheme.Modules.pullback a).obj M
    have hN : affineLocallyFiniteType W N :=
      (affineLocallyFiniteType W).prop_of_iso ((Scheme.Modules.restrictFunctorIsoPullback a).app M)
        (affineLocallyFiniteType_restrict a hM)
    have hflatN : Scheme.Modules.relativeFlat b N :=
      Scheme.Modules.relativeFlat_pullback_of_isOpenImmersion f j hflat
    have he : D ∘ j = moduleFiberCohomologyDimension b N q := by
      funext p
      exact modulePointFiberCohomologyDimension_eq_moduleFiberCohomologyDimension f j p M q
    rw [he]
    exact upperSemicontinuous_moduleFiberCohomologyDimension_of_proper
      (R := A) b N hN hflatN q
  apply upperSemicontinuous_iff_isOpen_preimage.mpr
  intro n
  have he : D ⁻¹' Set.Iio n =
      ⋃ i, U.f i '' ((D ∘ U.f i) ⁻¹' Set.Iio n) := by
    ext y
    constructor
    · intro hy
      obtain ⟨p, hp⟩ := U.covers y
      refine Set.mem_iUnion.mpr ⟨U.idx y, p, ?_, hp⟩
      simpa only [Set.mem_preimage, Set.mem_Iio, Function.comp_apply, hp] using hy
    · intro hy
      rcases Set.mem_iUnion.mp hy with ⟨i, p, hp, rfl⟩
      exact hp
  rw [he]
  exact isOpen_iUnion fun i =>
    (U.f i).isOpenEmbedding.isOpenMap _ ((hlocal i).isOpen_preimage n)

end AlgebraicGeometry.Scheme.Cohomology
