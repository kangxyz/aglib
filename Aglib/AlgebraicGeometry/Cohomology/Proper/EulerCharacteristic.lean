/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Cohomology.Fibers.Affine
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Locality

/-!
# Locally constant original proper fibre Euler characteristics

The proper supplier constructs the same actual bounded finite-projective
model. Its original ordinary fibre comparison identifies the unchanged
intrinsic alternating sum with the native homological Euler characteristic.
Finite-projective terms make it locally constant without reducedness.
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

/-- The intrinsic alternating sum of original proper ordinary fibre-cohomology dimensions
is locally constant for a coherent relatively flat coefficient over a Noetherian affine base. -/
theorem isLocallyConstant_moduleFiberEulerChar_of_proper
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) :
    IsLocallyConstant (moduleFiberEulerChar f M) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact D.isLocallyConstant_moduleFiberEulerChar hU hcover Equiv.ulift hflat

/-- The honest intrinsic ordinary point-fibre Euler characteristic is locally constant
over every locally Noetherian target for a proper coherent relatively flat coefficient.
The finite cohomological bounds used on target affine opens need not be globally uniform. -/
theorem isLocallyConstant_modulePointFiberEulerChar_of_proper
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) :
    IsLocallyConstant (modulePointFiberEulerChar f M) := by
  let χ := modulePointFiberEulerChar f M
  let U := Y.affineOpenCover
  have hlocal (i : U.I₀) : IsLocallyConstant (χ ∘ U.f i) := by
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
    have he : χ ∘ j = moduleFiberEulerChar b N := by
      funext p
      exact modulePointFiberEulerChar_eq_moduleFiberEulerChar f j p M
    rw [he]
    exact isLocallyConstant_moduleFiberEulerChar_of_proper (R := A) b N hN hflatN
  intro s
  have he : χ ⁻¹' s = ⋃ i, U.f i '' ((χ ∘ U.f i) ⁻¹' s) := by
    ext y
    constructor
    · intro hy
      obtain ⟨p, hp⟩ := U.covers y
      refine Set.mem_iUnion.mpr ⟨U.idx y, p, ?_, hp⟩
      simpa only [Set.mem_preimage, Function.comp_apply, hp] using hy
    · intro hy
      rcases Set.mem_iUnion.mp hy with ⟨i, p, hp, rfl⟩
      exact hp
  rw [he]
  exact isOpen_iUnion fun i => (U.f i).isOpenEmbedding.isOpenMap _ (hlocal i s)

end AlgebraicGeometry.Scheme.Cohomology
