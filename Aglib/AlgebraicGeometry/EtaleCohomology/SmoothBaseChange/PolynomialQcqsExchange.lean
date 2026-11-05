/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.Polynomial
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.ModuleVanishingExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Reduction

/-! # Proposed original uniform polynomial exchange

This source endpoint consumes the full original qcqs source-cover producer.
It is not accepted until that dependency chain and this leaf compile.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasDerivedCategory.standard

/-- The original polynomial projection has the full qcqs comparison family. -/
theorem uniformHigherBaseChange_polynomial (n : ℕ) (hn : 0 < n) (R : CommRingCat.{u}) :
    SmoothReduction.UniformHigherBaseChange n (PolynomialLaurent.polynomialProjection R) := by
  intro X X' f f' g' H hqc hqs hunit
  let : QuasiCompact f := hqc
  let : QuasiSeparated f := hqs
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hunitR : IsUnit (n : R) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso R).hom.hom
  let : Smooth (Spec.algebraMap R (Polynomial R)) :=
    inferInstanceAs (Smooth (PolynomialLaurent.polynomialProjection R))
  intro F hF q
  exact higherBaseChangeMap_smooth_isIso_of_ringed_injective_vanishing
    f f' (Spec.algebraMap R (Polynomial R)) g' H n hn
    (fun r I _ => higherDirectImage_polynomial_qcqs_injective_positive_isZero
      f f' g' H (r + 1) (Nat.zero_lt_succ r) n hn hunitR I) F hF q

end AlgebraicGeometry.Scheme.EtaleCohomology
