/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Completion
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Functor

/-! # Original coefficient naturality of the native completion comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- The quotient/thickening comparison commutes with every original coefficient map. -/
@[reassoc]
theorem idealPowerQuotientIdealSheafIso_naturality (g : F ⟶ G) (n : ℕ) :
    idealQuotientHom X (idealThickeningBaseScalar f) (I ^ n) g ≫
      (idealPowerQuotientIdealSheafIso f I G n).hom =
    (idealPowerQuotientIdealSheafIso f I F n).hom ≫
      (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).map g := by
  apply (cancel_epi (idealQuotientπ X (idealThickeningBaseScalar f) F (I ^ n))).mp
  simp only [idealQuotientπ_hom_assoc, idealQuotientπ_idealSheafIso_hom,
    idealQuotientπ_idealSheafIso_hom_assoc]
  exact (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).naturality g

end AlgebraicGeometry.Scheme.Cohomology
