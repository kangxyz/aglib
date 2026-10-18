/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Basic

/-! A separate package consumes the characteristic-zero field comparison through
its original forward action on actual finite-etale point lifts. Source provenance:
local R5 checkpoint c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5, not published by this migration. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.EtaleFundamentalGroups
open Scheme.FiniteEtale (Fiber)
open Scheme.FiniteEtale.FieldGalois

universe u

example (F : Type u) [Field F] [CharZero F] :
    Field.absoluteGaloisGroup F ≃ₜ* FieldFundamentalGroup F :=
  fundamentalGroupContinuousEquiv F

example (F : Type u) [Field F] [CharZero F] (σ : Field.absoluteGaloisGroup F)
    (Y : Scheme.FiniteEtale (Spec (CommRingCat.of F))) (p : Fiber (geometricPoint F) Y) :
    (fundamentalGroupContinuousEquiv F σ).hom.app Y p = act F σ Y p :=
  fundamentalGroupContinuousEquiv_apply F σ Y p
