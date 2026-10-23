/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Modules.Objects
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeBaseChangeLimit
public import Aglib.AlgebraicGeometry.Modules.Invertible.FinitePresentation

/-!
# Finite coefficient data for an actual line bundle

The native finite-generated-subalgebra limit descends the actual module.
Eventual local rank one makes an original later model a line bundle. The
recovering isomorphism retains the original native cone projection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- A line bundle on an actual algebra base change descends to a line bundle
over one original finite-generated coefficient subalgebra. -/
theorem exists_lineBundle_finiteType_model
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f]
    (L : LineBundle (Limits.pullback (Spec.algebraMap R A) f)) :
    ∃ (s : Finset A)
      (N : LineBundle ((Scheme.FiniteTypeSubalgebraLimit.schemeDiagram R A f).obj (op s))),
      Nonempty ((pullback ((Scheme.FiniteTypeSubalgebraLimit.schemeCone R A f).π.app
        (op s))).obj N.val ≅ L.val) := by
  let D := Scheme.FiniteTypeSubalgebraLimit.schemeDiagram R A f
  let c := Scheme.FiniteTypeSubalgebraLimit.schemeCone R A f
  let hc := Scheme.FiniteTypeSubalgebraLimit.schemeConeIsLimit R A f
  have : L.val.IsFinitePresentation := lineBundle_isFinitePresentation _ L
  obtain ⟨i, _, M, hM, ⟨e⟩⟩ := exists_model_above_of_isLimit D c hc (op ∅) L.val
  have : M.IsFinitePresentation := hM
  have hL : IsLocallyRankOne c.pt ((pullback (c.π.app i)).obj M) :=
    isLocallyRankOne_of_iso _ e.symm L.property
  obtain ⟨j, q, hj⟩ := exists_isLocallyRankOne_pullback_above_of_isLimit D c hc i M hL
  refine ⟨j.unop, ⟨(pullback (D.map q)).obj M, hj⟩, ⟨?_⟩⟩
  exact ((pullbackConeCompIso D c q).app M).symm ≪≫ e

end AlgebraicGeometry.Scheme.Modules.Invertible
