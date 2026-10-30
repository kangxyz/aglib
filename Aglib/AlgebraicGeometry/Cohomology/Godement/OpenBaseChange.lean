/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.FirstSquare
public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.SecondSquare
public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange.Span

/-! # Descent of the canonical unit through cartesian open base change

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5PositiveUnitOpen.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`5c431ecd8bb08af3ce18cc4d638cada3b8b8d1cde05b6044df1ecd8add2d3446`.
Selected declarations: totalTermsFlasque, pushPlus_quasiIso_flasque, quasiIso_of_QPlus_map_isIso,
  openPushPlusIso, openPullPlusIso, open_geometric_unit, openTotalBridge, openTotalBridge_quasiIso,
  restrictedTotal_flasque, restrictedPositive, localPositive, restrictedTotal, openSpanTarget,
  restrictedPositiveUnit, openPositiveComparison, globalSpanLeg, localSpanLeg,
  restrictedPositiveUnit_factor, quasiIso_of_plus_span, globalSpanLeg_quasiIso,
  localSpanLeg_quasiIso, augmentation_component_naturality, openTotalBridge_f,
  local_total_unit_component, open_component_first_square, open_component_second_square,
  open_positive_unit_span_component, open_positive_unit_span_factorized, open_positive_unit_span,
  positivePlusUnit_restrict_quasiIso.
-/

/-! This compatibility facade preserves the original public declaration names.
Stable data and independent proof branches live in the `OpenBaseChange` family. -/
