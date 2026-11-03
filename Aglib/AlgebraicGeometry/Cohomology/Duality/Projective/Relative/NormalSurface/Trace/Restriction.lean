/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.BaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.DegreeZero
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Stalk

/-!
# Original inverse-trace pullback on an isomorphism open

The actual restriction square, original ordinary base-change mate and native
geometric counit identify the restricted inverse-trace adjoint as an iso.
The existing proof is extracted once from PointBlowupGeneration. No canonical
coefficient, projective embedding, normality or surface hypothesis is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- On an original target open where the morphism is an isomorphism, the
actual inverse-trace adjoint is invertible after the SAME open pullback.
Only the original qcqs map, quasicoherent source coefficient and trace iso
are required; the target coefficient need not be quasicoherent. -/
theorem ordinaryTracePullback_isIso_of_isIso_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {M : X.Modules} [M.IsQuasicoherent] {N : Y.Modules}
    (τ : (pushforward f).obj M ⟶ N) [IsIso τ]
    (U : Y.Opens) [IsIso (f ∣_ U)] :
    IsIso ((pullback (f ⁻¹ᵁ U).ι).map (ordinaryTracePullback f τ)) := by
  let aU := (f ⁻¹ᵁ U).ι
  let fU := f ∣_ U
  let HU : IsPullback aU fU f U.ι := (isPullback_morphismRestrict f U).flip
  let : IsIso ((cartesianBaseChangeMap aU fU f U.ι HU).app M) :=
    canonicalTraceOrdinaryBaseChange_isIso aU fU f U.ι HU M
  let : IsIso ((pullbackPushforwardAdjunction fU).counit.app
      ((pullback aU).obj M)) :=
    pullbackPushforwardCounit_isIso_of_closedImmersion fU ((pullback aU).obj M)
  change IsIso ((pullback aU).map (ordinaryTracePullback f τ))
  rw [ordinaryTracePullback_baseChange aU fU f U.ι HU τ]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
