/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Naturality
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.IdentityBranches

/-! # Identity-source normalization of the original derived Cartesian comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wY wX

section IdentitySource

variable {U Y X : Scheme.{u}} (i : U ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback (𝟙 U) i j f)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- Identity-source normalization is exactly the derived ordinary identity-source
comparison used by the original compactification refinement construction. -/
theorem moduleDerivedLowerShriekCartesianBaseChangeIso_identity_source :
    moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 U) i j f h Λ ≪≫
        Functor.isoWhiskerRight (moduleDerivedInverseImageIdIso Λ U)
          (moduleDerivedLowerShriek i Λ) ≪≫
        Functor.leftUnitor (moduleDerivedLowerShriek i Λ) =
      (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
        (moduleLowerShriek j Λ) (moduleInverseImage f Λ)).symm ≪≫
      (moduleLowerShriek j Λ ⋙ moduleInverseImage f Λ).rightDerivedFunctorPlusIso
        (moduleLowerShriekCartesianIdentityIso i j f h Λ) := by
  have hn := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_left
    (moduleLowerShriek i Λ) (moduleInverseImageIdIso Λ U)
  have hu := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_leftUnitor
    (moduleLowerShriek i Λ)
  simp only [moduleDerivedLowerShriekCartesianBaseChangeIso,
    moduleDerivedInverseImageIdIso, moduleLowerShriekCartesianIdentityIso,
    Functor.isoWhiskerRight_trans, Functor.rightDerivedFunctorPlusIso_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
    (moduleInverseImage (𝟙 U) Λ) (moduleLowerShriek i Λ)), ← hn]
  simp only [Iso.trans_assoc]
  rw [hu]

end IdentitySource

end AlgebraicGeometry.Scheme.EtaleCohomology
