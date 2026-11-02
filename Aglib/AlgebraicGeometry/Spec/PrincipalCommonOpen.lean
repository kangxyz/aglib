/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.OverBaseCommonOpen
public import Aglib.AlgebraicGeometry.Spec.PrincipalNeighborhoodSpreading

/-! # An original common open over one principal stage

This is the thin instance of common-open descent at the original principal
localization cone. It retains the supplied localization, the original base
schemes, the sole descended common model, and both actual comparison maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open IsLocalization.PrincipalDiagram

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

universe u

open FinitePresentationDescent

/-- A common quasi-compact open of the two original localization base
changes descends to a single original principal stage, with both original
comparison equations. No replacement localization or chart is chosen. -/
theorem exists_common_open_with_comparison
    {R : Type u} [CommRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
    (X : Bool → Scheme.{u}) (f : ∀ b, X b ⟶ Spec (.of R))
    [∀ b, LocallyOfFinitePresentation (f b)] [∀ b, QuasiCompact (f b)]
    [∀ b, QuasiSeparated (f b)]
    {W : Scheme.{u}} [CompactSpace W] (w : W ⟶ Spec (.of S))
    (m : ∀ b, Over.mk w ⟶ (Over.pullback (Spec.algebraMap R S)).obj (Over.mk (f b)))
    [hm : ∀ b, IsOpenImmersion (m b).left] :
    ∃ j : Over (op (∅ : Finset M)), ∃ N : Model ((specCone M S).π.app j.left) w,
      ∀ b, ∃ a : Over.mk N.f ⟶
        (Over.pullback ((baseStructure M).app j.left)).obj (Over.mk (f b)),
        IsOpenImmersion a.left ∧
        N.p ≫ a.left = (m b).left ≫ comparison M S (f b) j := by
  have (j : (Finset M)ᵒᵖ) : CompactSpace ((specDiagram M).obj j) := by
    change CompactSpace (Spec (.of (stage M j.unop)))
    infer_instance
  have (j : (Finset M)ᵒᵖ) : QuasiSeparatedSpace ((specDiagram M).obj j) := by
    change QuasiSeparatedSpace (Spec (.of (stage M j.unop)))
    infer_instance
  exact @OverBaseSpreading.exists_common_open_with_comparison
    _ _ (specDiagram M) (specCone M S) (Spec (.of R))
    (baseStructure M) (Spec.algebraMap R S) (baseStructure_fac M S) (op ∅)
    _ _ _ _ (specConeIsLimit M S) X f _ _ _ W _ w m hm

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
