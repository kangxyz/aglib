/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

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
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat

theorem shortExact_of_restrictScalars {A B : Type u} [Ring A] [Ring B]
    (α : A →+* B) (S : ShortComplex (ModuleCat.{u} B))
    (hS : (S.map (ModuleCat.restrictScalars α)).ShortExact) : S.ShortExact := by
  let F := ModuleCat.restrictScalars α
  have hm : Mono (F.map S.f) := hS.mono_f
  have he : Epi (F.map S.g) := hS.epi_g
  exact
    { exact := F.reflects_exact_of_faithful S hS.exact
      mono_f := F.mono_of_mono_map hm
      epi_g := F.epi_of_epi_map he }

end ModuleCat
