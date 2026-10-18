/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.PrincipalChart
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Principal.Quotient

/-!
# Original quotient-chart sources under principal refinement

The actual principal ambient square and the original closed immersion
uniquely determine the quotient-normalized source. Its refinement arrow
is the same literal quotient-localization map used by the native model law.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ}
  [IsClosedImmersion i] {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)
  (r : C.A) (hr : C.σ r ∉ C.point.asIdeal)

omit [IsClosedImmersion i] in
/-- The actual principal quotient chart has the original localized ordered list. -/
theorem canonicalPrincipalChart_regularList :
    (C.principalChart r hr).quotientChart.regularList = regularListPrincipalList C.regularList r :=
  rfl

omit [IsClosedImmersion i] in
/-- The actual principal ambient source is the original localization followed by the old open. -/
theorem canonicalPrincipalChart_ambient :
    (C.principalChart r hr).quotientChart.jP =
      Spec.map (CommRingCat.ofHom (algebraMap C.A (Localization.Away r))) ≫
        C.quotientChart.jP := rfl

omit [IsClosedImmersion i] in
/-- The same base ring and original base open remain in the ambient principal refinement. -/
theorem canonicalPrincipalChart_base :
    (C.principalChart r hr).quotientChart.jY = C.quotientChart.jY := rfl

/-- The original closed square identifies the actual quotient-chart source refinement. -/
theorem canonicalPrincipalChart_source :
    (C.principalChart r hr).quotientChart.jX =
      Spec.map (regularListPrincipalLiteralQuotientMap C.regularList r) ≫
        C.quotientChart.jX := by
  apply (cancel_mono i).mp
  rw [← (C.principalChart r hr).quotientChart.closedSquare,
    Category.assoc, ← C.quotientChart.closedSquare, canonicalPrincipalChart_ambient]
  change Spec.map (regularListQuotientMap
      (A := CommRingCat.of (Localization.Away r)) (regularListPrincipalList C.regularList r)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap C.A (Localization.Away r))) ≫ C.jP) =
    Spec.map (regularListPrincipalLiteralQuotientMap C.regularList r) ≫
      (Spec.map (regularListQuotientMap C.regularList) ≫ C.jP)
  rw [← Category.assoc, ← Spec.map_comp, regularListPrincipalLiteralQuotientMap_square,
    Spec.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme.Modules
