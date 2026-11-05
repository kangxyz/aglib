/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryChartComponent
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.ChartOrdinaryEpimorphism

/-! # Epimorphy of the actual ordinary source-chart comparison

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

set_option diagnostics true in
/-- The original source-chart comparison is epi by raw-chart ordinary exchange. -/
theorem sourceEtaleOrdinaryComparison_epi [Smooth g] (U : X.Etale)
    (n : ℕ) (hn : 0 < n) (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) : type_of% (
  sourceChartOrdinaryTransport_epi f f' g g' H U.hom
    ((inverseImage U.hom).obj F) n hn (sourceEtaleRestricted_killed U F n hF)
    ((sourceEtaleOrdinarySourceIso f g U).app F)
    ((sourceEtaleOrdinaryTargetIso f' g' U).app F)
    ) :=
  sourceChartOrdinaryTransport_epi f f' g g' H U.hom
    ((inverseImage U.hom).obj F) n hn (sourceEtaleRestricted_killed U F n hF)
    ((sourceEtaleOrdinarySourceIso f g U).app F)
    ((sourceEtaleOrdinaryTargetIso f' g' U).app F)

end AlgebraicGeometry.Scheme.EtaleCohomology
