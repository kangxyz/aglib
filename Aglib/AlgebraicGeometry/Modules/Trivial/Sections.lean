/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.FunctionField
public import Aglib.AlgebraicGeometry.Points.Closed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Trivial.Sections` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`c053ce6518409eb20f06626afa361ef390590c9cd7555dc5796a40c993da07e1`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.Modules.Trivial
universe u
variable (X : Scheme.{u}) [hIntegral : IsIntegral X] [hNoeth : AlgebraicGeometry.IsNoetherian X]
variable [hDVR : ∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

/-- The linear equivalence on sections induced by the specified trivialization of the
module sheaf. -/
def isoSectionEquiv (N : SheafOfModules.{u} X.ringCatSheaf)
    (a : N ≅ SheafOfModules.unit X.ringCatSheaf) (V : X.Opens) :
    N.val.obj (op V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)).mapIso
    ((SheafOfModules.forget _).mapIso a)).toLinearEquiv

/-- The global generator that corresponds to the unit section under the given trivialization. -/
def globalGenerator (N : SheafOfModules.{u} X.ringCatSheaf)
    (a : N ≅ SheafOfModules.unit X.ringCatSheaf) : N.val.obj (op ⊤) :=
  (isoSectionEquiv X N a ⊤).symm 1

omit [hIntegral : IsIntegral X] [hNoeth : AlgebraicGeometry.IsNoetherian X]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
-- Retain the integral-scheme guard of the original rational-trivialization section API.
@[nolint unusedArguments]
theorem globalGenerator_restrict [IsIntegral X] (N : SheafOfModules.{u} X.ringCatSheaf)
    (a : N ≅ SheafOfModules.unit X.ringCatSheaf) (V : X.Opens) :
    N.val.map (homOfLE le_top : V ⟶ ⊤).op (globalGenerator X N a) =
      (isoSectionEquiv X N a V).symm 1 := by
  have hn := PresheafOfModules.naturality_apply a.inv.val
    (homOfLE le_top : V ⟶ ⊤).op (1 : Γ(X, ⊤))
  change (isoSectionEquiv X N a V).symm (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op 1) =
    N.val.map (homOfLE le_top : V ⟶ ⊤).op (globalGenerator X N a) at hn
  rw [map_one] at hn
  exact hn.symm

omit hIntegral hNoeth hDVR in
-- Retain the original Noetherian and closed-stalk DVR section-coordinate guards.
@[nolint unusedArguments]
theorem section_as_smul_generator [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (N : SheafOfModules.{u} X.ringCatSheaf)
    (a : N ≅ SheafOfModules.unit X.ringCatSheaf) (V : X.Opens) (s : N.val.obj (op V)) :
    s = isoSectionEquiv X N a V s •
      N.val.map (homOfLE le_top : V ⟶ ⊤).op (globalGenerator X N a) := by
  rw [globalGenerator_restrict]
  apply (isoSectionEquiv X N a V).injective
  rw [(isoSectionEquiv X N a V).map_smul, LinearEquiv.apply_symm_apply]
  exact (mul_one _).symm

end AlgebraicGeometry.Scheme.Modules.Trivial
