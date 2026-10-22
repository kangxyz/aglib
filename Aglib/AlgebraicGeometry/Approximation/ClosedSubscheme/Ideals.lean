/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.FiniteTypeApproximation

/-!
# Finite-type subideals for closed-subscheme approximation

The native ideal-sheaf owner supplies finite generation, the filtered index,
and equality with the supremum of finite-type subideals. The approximation
names below are compatibility aliases and consequences of that construction.
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The approximation spelling of native affine-local finite generation. -/
abbrev IsFiniteType {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  I.AffineLocallyFG

/-- The native finite-type subideal index, with its original ideal inclusions. -/
abbrev FiniteSubideal {X : Scheme.{u}} (I : X.IdealSheafData) : Type u :=
  I.FiniteTypeSubideal

/-- Every affine section of an ideal belongs to an actual finite-type subideal. -/
theorem exists_finiteSubideal_mem {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (U : X.affineOpens) {x : Γ(X, U)} (hx : x ∈ I.ideal U) :
    ∃ J : I.FiniteSubideal, x ∈ J.val.ideal U := by
  obtain ⟨J, hJI, hJ, hxJ⟩ := exists_affineLocallyFG_le_of_mem I U x hx
  exact ⟨⟨J, hJI, hJ⟩, hxJ⟩

/-- The actual ideal is the supremum of the native finite-type subideals. -/
theorem iSup_finiteSubideal {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) : (⨆ J : I.FiniteSubideal, J.val) = I :=
  iSup_finiteTypeSubideal I

end AlgebraicGeometry.Scheme.IdealSheafData
