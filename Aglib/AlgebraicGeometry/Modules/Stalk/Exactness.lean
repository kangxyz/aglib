/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/SheafStalkShortExact.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 55]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

theorem exact_of_moduleStalk {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : ∀ x, (S.map (moduleStalk X x)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology]
  apply (isZero_iff_stalks _).mpr
  intro x
  have hz := (S.map (moduleStalk X x)).exact_iff_isZero_homology.mp (hS x)
  have hObj : IsZero ((moduleStalk X x).obj S.homology) :=
    hz.of_iso (S.mapHomologyIso (moduleStalk X x)).symm
  exact ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero hObj).of_iso
    ((moduleStalkForgetIso X x).app S.homology).symm

theorem shortExact_of_moduleStalk {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : ∀ x, (S.map (moduleStalk X x)).ShortExact) : S.ShortExact where
  exact := exact_of_moduleStalk S (fun x => (hS x).exact)
  mono_f := mono_of_moduleStalk S.f (fun x => (hS x).mono_f)
  epi_g := epi_of_moduleStalk S.g (fun x => (hS x).epi_g)

end AlgebraicGeometry.Scheme.Modules
