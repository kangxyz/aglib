/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineSystem
public import Aglib.RingTheory.AdicCompletion.CompatibleSystemExtended

/-! # The completed module of an original affine formal system

This constructs a finite module over the completed affine coordinate ring,
not an algebraization over the original ring. Its reductions retain the
original global sections and every original transition, including index zero.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} (F : AdicSystem (Spec B) K)

/-- The underlying module is the actual compatible family of original sections. -/
abbrev affineFormalSections := ModuleCat.sectionsSubmodule F.affineSectionsTower

/-- Canonical completed scalar action on the original compatible families. -/
abbrev affineFormalSectionsModule :
    Module (AdicCompletion (affineIdeal B K) B) F.affineFormalSections :=
  F.affineSections_isCompatibleSystem.sectionsCompletionModule

/-- Original affine formal sections are finite over the completed ring. -/
theorem affineFormalSections_finite :
    let := F.affineFormalSectionsModule
    Module.Finite (AdicCompletion (affineIdeal B K) B) F.affineFormalSections :=
  F.affineSections_isCompatibleSystem.sections_finite

/-- The kernel of an original projection is the original ideal-power filtration. -/
theorem affineFormalSections_ker (n : ℕ) :
    (ModuleCat.sectionsEval F.affineSectionsTower n).ker =
      affineIdeal B K ^ n • (⊤ : Submodule B F.affineFormalSections) :=
  F.affineSections_isCompatibleSystem.sectionsEval_ker_eq
    (IsNoetherian.noetherian _) n

/-- Canonical reduction to the original global sections at every order. -/
def affineFormalSectionsReduction (n : ℕ) :
    (F.affineFormalSections ⧸
      (affineIdeal B K ^ n • (⊤ : Submodule B F.affineFormalSections))) ≃ₗ[B]
        F.affineSectionsTower.obj (op n) :=
  F.affineSections_isCompatibleSystem.sectionsReductionEquiv
    (IsNoetherian.noetherian _) n

theorem affineFormalSectionsReduction_mk (n : ℕ) (x : F.affineFormalSections) :
    F.affineFormalSectionsReduction n (Submodule.Quotient.mk x) = x.val (op n) :=
  F.affineSections_isCompatibleSystem.sectionsReductionEquiv_mk
    (IsNoetherian.noetherian _) n x

/-- All-order transition compatibility uses the original formal-system maps. -/
theorem affineFormalSectionsReduction_transition {n m : ℕ} (h : n ≤ m)
    (x : F.affineFormalSections ⧸
      (affineIdeal B K ^ m • (⊤ : Submodule B F.affineFormalSections))) :
    F.affineSectionsTower.map (homOfLE h).op (F.affineFormalSectionsReduction m x) =
      F.affineFormalSectionsReduction n
        (Submodule.factorPow (affineIdeal B K) F.affineFormalSections h x) :=
  F.affineSections_isCompatibleSystem.sectionsReductionEquiv_transition
    (IsNoetherian.noetherian _) h x

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
