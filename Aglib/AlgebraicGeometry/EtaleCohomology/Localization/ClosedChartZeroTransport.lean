/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Original classes on a reconstructed closed chart

A cartesian chart returns original cohomological zero to the literal pullback
of the constructed ambient neighborhood. This does not promote closed-fibre
zero to zero on the whole ambient neighborhood. The neighborhood is produced
independently; these are its original-class transport laws.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u e
attribute [local instance] hasSheafifyLarge HasExt.standard

/-- An actual cartesian reconstruction carries the same original zero class
back to the literal closed base change, by its canonical comparison iso. -/
theorem original_class_zero_on_pullback_of_chart
    {Z U S T : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} S)]
    (g : Z ⟶ U) (b : Z ⟶ S) (f : U ⟶ T) (i : S ⟶ T)
    (H : IsPullback g b f i) (M : AbelianSheaf.{u, u + 1} S)
    (q : ℕ) (c : Sheaf.H.{e} M q)
    (hc : cohomologyPullback.{u, e, u + 2} b M q c = 0) :
    cohomologyPullback.{u, e, u + 2} (pullback.snd f i) M q c = 0 :=
  TwoFieldEffacement.original_class_zero_of_map_law H.isoPullback.inv b
    (pullback.snd f i) H.isoPullback_inv_snd M q c hc

/-- Restrict the original annihilating neighborhood to its chosen chart and
return zero through the actual cartesian reconstruction. No new class is chosen. -/
theorem original_class_zero_on_pullback_of_chart_refinement
    {W Z U S T : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} S)]
    (g : Z ⟶ U) (b : Z ⟶ S) (f : U ⟶ T) (i : S ⟶ T)
    (H : IsPullback g b f i) (r : Z ⟶ W) (k : W ⟶ S) (hr : r ≫ k = b)
    (M : AbelianSheaf.{u, u + 1} S) (q : ℕ) (c : Sheaf.H.{e} M q)
    (hc : cohomologyPullback.{u, e, u + 2} k M q c = 0) :
    cohomologyPullback.{u, e, u + 2} (pullback.snd f i) M q c = 0 :=
  original_class_zero_on_pullback_of_chart g b f i H M q c
    (TwoFieldEffacement.original_class_zero_of_map_law r k b hr M q c hc)

end AlgebraicGeometry.Scheme.EtaleCohomology
