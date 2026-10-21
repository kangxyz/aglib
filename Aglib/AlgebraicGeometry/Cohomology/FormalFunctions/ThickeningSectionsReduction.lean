/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ThickeningSections

/-!
# Original reduction coordinates on proper ideal thickenings

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


/-- A compatible family with an original reduction coordinate maps to the
original geometric pullback coordinate. All structural comparisons occur here
at variable schemes, before specialization to a local-spectrum base change. -/
theorem properIdealQuotientThickeningSectionsEquiv_reduction
    (s : ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) F I p))
    (x : (moduleCohomologyFunctorOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) p).obj F) (n : ℕ)
    (hs : s.val (op n) = moduleCohomologyMapOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
      (Modules.idealQuotientπ X (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
        F (I ^ n)) p x) :
    (properIdealQuotientThickeningSectionsEquiv R f F hF I p s).val (op n) =
      moduleCohomologyPullback (Modules.idealThickeningι f (I ^ n)) F p x := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  rw [properIdealQuotientThickeningSectionsEquiv_apply, hs]
  exact idealQuotientThickeningCohomologyEquiv_reduction f F (I ^ n) p x

end AlgebraicGeometry.Scheme.Cohomology
