/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteTupleStalkExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineExtendedCoordinates

/-! # The original affine finite direct-image stalk as the common-field tuple -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

open CoefficientStalkBaseChange

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsAlgClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]

/-- Actual finite stalk decomposition followed by original component field
extensions. All target coordinates use the same geometric field. -/
def finiteAffineExtendedStalkIso (F : AbelianSheaf.{u, u + 1} X) :
    coefficientFiber (Spec.algebraMap R Ω) ((directImage f).obj F) ≅
      AddCommGrpCat.of (∀ m : MaximalSpectrum Γ(finiteAffineSource R Ω f, ⊤),
        coefficientFiber (finiteAffineExtendedPoint R Ω f m) F) := by
  let B := GeometricEtaleColimit R Ω
  let Y := finiteAffineSource R Ω f
  let p : Y ⟶ Spec (.of B) := finiteAffineProjection R Ω f
  let : IsFinite p := inferInstanceAs (IsFinite
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))
  let : IsAffine Y := isAffine_of_isAffineHom p
  let := finiteSourceAlgebra B p
  let := finiteSource_moduleFinite B p
  let : Algebra (ResidueField B) Ω := (GeometricEtaleColimit.residueFieldEmbedding R Ω).toAlgebra
  exact finiteAffineDirectImageStalkIso R Ω f F ≪≫
    finiteSourceStalkTupleExtensionIso Γ(Y, ⊤) B Ω (baseChangedEtaleDiagram R Ω f)
      (baseChangedEtaleCone R Ω f) Y.isoSpec.symm F

/-- The isomorphism's literal coordinate is the already constructed original
common-field coordinate map, with no replacement of the coefficient sheaf. -/
theorem finiteAffineExtendedStalkIso_apply (F : AbelianSheaf.{u, u + 1} X)
    (a : coefficientFiber (Spec.algebraMap R Ω) ((directImage f).obj F))
    (m : MaximalSpectrum Γ(finiteAffineSource R Ω f, ⊤)) :
    (finiteAffineExtendedStalkIso R Ω f F).hom a m =
      finiteAffineExtendedCoordinate R Ω f F m a := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
