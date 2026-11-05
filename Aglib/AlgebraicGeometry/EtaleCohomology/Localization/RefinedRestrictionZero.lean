/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Preservation of original restriction zero under refinement

A commuting square preserves the actual iterated pullback zero, not only zero
for a composite arrow. The complete construction also applies the original
coefficient map. In particular the canonical inverse-image composition gives
exactly the coefficient carrier needed by open/closed class detection after
a target refinement. No cartesian, smooth, or etale hypothesis is needed for
this stability law.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u e
attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Original restriction zero persists for the actual pulled-back class along
any commuting refinement square. -/
theorem restriction_zero_after_refinement
    {Y V Y' V' : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    (j : V ⟶ Y) (v : Y' ⟶ Y) (j' : V' ⟶ Y') (vU : V' ⟶ V)
    (h : vU ≫ j = j' ≫ v)
    (F : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (c : Sheaf.H.{e} F q)
    (hc : cohomologyPullback.{u, e, u + 2} j F q c = 0) :
    cohomologyPullback j' ((inverseImage v).obj F) q
      (cohomologyPullback.{u, e, u + 2} v F q c) = 0 := by
  have hz := TwoFieldEffacement.original_class_zero_of_map_law
    vU j (j' ≫ v) h F q c hc
  have hcomp := cohomologyPullback_comp.{u, e, u + 2, u + 2} v j' F q c
  rw [hz, map_zero] at hcomp
  exact hcomp.symm

/-- The same actual zero survives any original coefficient arrow, including
the canonical comparison used by the refined detector. -/
theorem restriction_zero_after_refinement_map
    {Y V Y' V' : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    (j : V ⟶ Y) (v : Y' ⟶ Y) (j' : V' ⟶ Y') (vU : V' ⟶ V)
    (h : vU ≫ j = j' ≫ v)
    (F : AbelianSheaf.{u, u + 1} Y) (G : AbelianSheaf.{u, u + 1} Y')
    (m : (inverseImage v).obj F ⟶ G) (q : ℕ) (c : Sheaf.H.{e} F q)
    (hc : cohomologyPullback.{u, e, u + 2} j F q c = 0) :
    cohomologyPullback j' G q
      (Sheaf.H.map m q (cohomologyPullback.{u, e, u + 2} v F q c)) = 0 := by
  rw [cohomologyPullback_coefficientMap]
  rw [restriction_zero_after_refinement j v j' vU h F q c hc, map_zero]

/-- For an original coefficient pulled from a fixed base, the refinement uses
the actual composite structural map. This is the open-zero input on the exact
carrier of the refined H1 detector, not a replacement class certificate. -/
theorem restriction_zero_after_refinement_composite_coefficient
    {X Y V Y' V' : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    (b : Y ⟶ X) (j : V ⟶ Y) (v : Y' ⟶ Y) (j' : V' ⟶ Y') (vU : V' ⟶ V)
    (h : vU ≫ j = j' ≫ v) (I : AbelianSheaf.{u, u + 1} X)
    (q : ℕ) (c : Sheaf.H.{e} ((inverseImage b).obj I) q)
    (hc : cohomologyPullback.{u, e, u + 2} j _ q c = 0) :
    cohomologyPullback j' ((inverseImage (v ≫ b)).obj I) q
      (Sheaf.H.map ((inverseImageComp b v).inv.app I) q
        (cohomologyPullback.{u, e, u + 2} v _ q c)) = 0 :=
  restriction_zero_after_refinement_map j v j' vU h _ _
    ((inverseImageComp b v).inv.app I) q c hc

/-- On the literal pullback of the original open restriction, the refined
canonical coefficient class satisfies exactly the detector's open-zero input. -/
theorem restriction_zero_on_pullback_composite_coefficient
    {X Y V Y' : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    (b : Y ⟶ X) (j : V ⟶ Y) (v : Y' ⟶ Y)
    (I : AbelianSheaf.{u, u + 1} X)
    (q : ℕ) (c : Sheaf.H.{e} ((inverseImage b).obj I) q)
    (hc : cohomologyPullback.{u, e, u + 2} j _ q c = 0) :
    cohomologyPullback (pullback.snd j v) ((inverseImage (v ≫ b)).obj I) q
      (Sheaf.H.map ((inverseImageComp b v).inv.app I) q
        (cohomologyPullback.{u, e, u + 2} v _ q c)) = 0 :=
  restriction_zero_after_refinement_composite_coefficient b j v
    (pullback.snd j v) (pullback.fst j v) pullback.condition I q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology
