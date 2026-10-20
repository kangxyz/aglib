/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Open restriction of kernels and finite ideal intersections

Source: `R5Lab.Aglib.AlgebraicGeometry.IdealSheaf.OpenRestriction`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `713af6f12f43140fff678a03f18babca23d39db551867df376463ed47a019995`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Scheme.IdealSheafData

/-- Native ideal-sheaf kernels commute with the proved open base change. -/
theorem kernel_comap_open_pullback {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [QuasiCompact f]
    (H : IsPullback f' iU iV f) : f.ker.comap iV = f'.ker := by
  ext W : 2
  rw [ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f f' iU iV H W).symm

/-- Finite closed unions restrict to their actual finite affine union. -/
theorem comap_finite_iInf {X Y : Scheme.{u}} {ι : Type*} [Finite ι]
    (I : ι → Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (⨅ j, I j).comap f = ⨅ j, (I j).comap f := by
  ext U : 2
  simp only [ideal_comap_of_isOpenImmersion, ideal_iInf, iInf_apply, Ideal.comap_iInf]

end AlgebraicGeometry.Scheme.IdealSheafData
