/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.Affine
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ThickeningTower

/-!
# Formal functions on the actual infinitesimal thickenings

The affine formal-functions equivalence is followed by the original natural
comparison with cohomology on the actual schemes `X × Spec (A/I^n)`. The forward
map on original classes is geometric pullback to each actual thickening.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (F : X.Modules)
  (hF : affineLocallyFiniteType X F) (I : Ideal A) (p : ℕ)

local notation "α" => Modules.idealThickeningBaseScalar f

/-- The actual thickening cohomology tower of a proper coherent coefficient.
Compactness, separatedness and quasicoherence are derived, not extra premises. -/
abbrev properIdealThickeningCohomologyTower : ℕᵒᵖ ⥤ ModuleCat.{u + 1} A := by
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  letI : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  exact idealThickeningCohomologyTower f F I p

variable [IsNoetherianRing A]

/-- Formal functions with the actual infinitesimal-thickening cohomology tower. -/
def moduleCohomologyFormalFunctionsThickeningEquiv :
    AdicCompletion I ((moduleCohomologyFunctorOfHom X α p).obj F) ≃ₗ[A]
      ModuleCat.sectionsSubmodule (properIdealThickeningCohomologyTower f F hF I p) := by
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  letI : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  exact (moduleCohomologyFormalFunctionsEquiv I f F hF p).trans
    (idealQuotientThickeningSectionsEquiv f F I p)

/-- On every original class, each coordinate is its genuine geometric
pullback to the actual ideal-power thickening. -/
theorem moduleCohomologyFormalFunctionsThickeningEquiv_of
    (x : (moduleCohomologyFunctorOfHom X α p).obj F) (n : ℕ) :
    (moduleCohomologyFormalFunctionsThickeningEquiv f F hF I p
      (AdicCompletion.of I _ x)).val (op n) =
        moduleCohomologyPullback (Modules.idealThickeningι f (I ^ n)) F p x := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  change idealQuotientThickeningCohomologyEquiv f F (I ^ n) p
    ((moduleCohomologyFormalFunctionsEquiv I f F hF p
      (AdicCompletion.of I _ x)).val (op n)) = _
  rw [moduleCohomologyFormalFunctionsEquiv_of]
  exact idealQuotientThickeningCohomologyEquiv_reduction f F (I ^ n) p x

end AlgebraicGeometry.Scheme.Cohomology
