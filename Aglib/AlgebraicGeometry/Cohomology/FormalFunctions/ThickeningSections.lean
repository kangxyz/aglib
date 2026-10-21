/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.Thickening

/-!
# Native compatible families on proper ideal thickenings

The comparison uses literally the native sections submodule of the original
geometric tower. Structural instances are compared at variable schemes and rings.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable (R : CommRingCat.{u}) {X : Scheme.{u}}
  (f : X ⟶ Spec R) [IsProper f] (F : X.Modules)
  (hF : affineLocallyFiniteType X F) (I : Ideal R) (p : ℕ)

/-- The original coordinatewise quotient-to-thickening comparison, with its
native proper compatible-family target over the specified ring. -/
def properIdealQuotientThickeningSectionsEquiv :
    ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) F I p) ≃ₗ[R]
        ModuleCat.sectionsSubmodule
          (properIdealThickeningCohomologyTower (A := R) f F hF I p) := by
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  letI : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  exact idealQuotientThickeningSectionsEquiv f F I p

/-- The proper-target comparison uses the original stagewise cohomology map. -/
theorem properIdealQuotientThickeningSectionsEquiv_apply
    (s : ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) F I p)) (n : ℕ) :
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
    letI : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
    (properIdealQuotientThickeningSectionsEquiv R f F hF I p s).val (op n) =
      idealQuotientThickeningCohomologyEquiv f F (I ^ n) p (s.val (op n)) := by
  rfl

end AlgebraicGeometry.Scheme.Cohomology
