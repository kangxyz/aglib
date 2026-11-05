/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryFaces
public import Aglib.CategoryTheory.Adjunction.Mates.ChartComponent

/-! # Actual restricted ordinary chart component

This isolates the native bounded coefficient instance from the face/mate
coherence layer, retaining the same original comparison.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g)

/-- The original restricted coefficient retains its given annihilator. -/
theorem sourceEtaleRestricted_killed (U : X.Etale) (F : AbelianSheaf.{u, u + 1} X)
    (n : ℕ) (hF : n • 𝟙 F = 0) :
    n • 𝟙 ((inverseImage U.hom).obj F) = 0 :=
  Functor.map_nsmul_id_eq_zero (inverseImage U.hom) F n hF

/-- The actual composite-chart middle component after original restriction. -/
theorem sourceEtaleRestrictedChart_isIso [Smooth g] (U : X.Etale)
    (n : ℕ) (hn : 0 < n) (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) : type_of% (
  sourceChartOrdinaryExchange_isIso f f' g g' H U.hom
    ((inverseImage U.hom).obj F) n hn (sourceEtaleRestricted_killed U F n hF)
    ) :=
  sourceChartOrdinaryExchange_isIso f f' g g' H U.hom
    ((inverseImage U.hom).obj F) n hn (sourceEtaleRestricted_killed U F n hF)


end AlgebraicGeometry.Scheme.EtaleCohomology
