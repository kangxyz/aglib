/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.VectorBundleFullness
public import Aglib.CategoryTheory.Limits.Shapes.UnitConeLifting

/-! # Original completion maps for finite locally free coefficients

Only the original scalar section cone is required. The original vector-bundle
Hom cone supplies lifting and detection through any specified diagram iso;
no full-faithfulness assertion for all coherent sheaves is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) [X.IsQuasiAffine] (K : X.IdealSheafData)
  (hunit : IsLimit (idealSheafSectionCone X K (SheafOfModules.unit X.ringCatSheaf)))
  (M N : X.Modules) [IsFiniteLocallyFree X M] [IsFiniteLocallyFree X N]
  {F : ℕᵒᵖ ⥤ X.Modules} (e : idealSheafQuotientTower X K N ≅ F)

/-- Lift a whole original compatible family into the specified completion diagram. -/
def vectorBundleCompletionLiftData (p : (Functor.const ℕᵒᵖ).obj M ⟶ F) :
    { a : M ⟶ N //
      (Functor.const ℕᵒᵖ).map a ≫ idealSheafQuotientTowerUnit X K N ≫ e.hom = p } := by
  let hN := Classical.choice (idealSheafSectionCone_finiteLocallyFree_isLimit X K hunit N)
  let hHom := Classical.choice (idealSheafHomCone_isLimit X K M N hN)
  exact homConeLiftData (idealSheafQuotientTowerUnit X K N) hHom e p

include hunit in
/-- All original components jointly detect maps from a vector bundle. -/
theorem vectorBundleCompletionMaps_injective {a b : M ⟶ N}
    (hab : ∀ n, a ≫ (idealSheafQuotientTowerUnit X K N ≫ e.hom).app n =
      b ≫ (idealSheafQuotientTowerUnit X K N ≫ e.hom).app n) : a = b := by
  obtain ⟨hN⟩ := idealSheafSectionCone_finiteLocallyFree_isLimit X K hunit N
  obtain ⟨hHom⟩ := idealSheafHomCone_isLimit X K M N hN
  exact homCone_maps_injective (idealSheafQuotientTowerUnit X K N) hHom e hab

end AlgebraicGeometry.Scheme.Modules.Coherent
