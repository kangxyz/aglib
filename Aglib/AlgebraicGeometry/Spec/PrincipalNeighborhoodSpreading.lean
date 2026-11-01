/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PrincipalNeighborhoodLimit
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.OverBaseGluing

/-!
# Spreading an original local isomorphism to a principal neighborhood

This is the thin principal-localization instance of descent over an unchanged
base. The original localization need not be finitely presented over its base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

universe u

open IsLocalization.PrincipalDiagram

variable {R : Type u} [CommRing R] (M : Submonoid R)
variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
variable {X Y : Scheme.{u}}

/-- The actual comparison induced by the original localization cone. -/
abbrev comparison (f : X ⟶ Spec (.of R)) (j : Over (op (∅ : Finset M))) :=
  OverBaseSpreading.comparison (specDiagram M) (specCone M S) (baseStructure M)
    (Spec.algebraMap R S) (baseStructure_fac M S) (op ∅) f j

/-- The comparison retains the projection to the original model. -/
@[reassoc (attr := simp)]
theorem comparison_fst (f : X ⟶ Spec (.of R)) (j : Over (op (∅ : Finset M))) :
    comparison M S f j ≫ pullback.fst f ((baseStructure M).app j.left) =
      pullback.fst f (Spec.algebraMap R S) :=
  OverBaseSpreading.comparison_fst (specDiagram M) (specCone M S) (baseStructure M)
    (Spec.algebraMap R S) (baseStructure_fac M S) (op ∅) f j

/-- The comparison retains the original coefficient-spectrum cone projection. -/
@[reassoc (attr := simp)]
theorem comparison_snd (f : X ⟶ Spec (.of R)) (j : Over (op (∅ : Finset M))) :
    comparison M S f j ≫ pullback.snd f ((baseStructure M).app j.left) =
      pullback.snd f (Spec.algebraMap R S) ≫ (specCone M S).π.app j.left :=
  OverBaseSpreading.comparison_snd (specDiagram M) (specCone M S) (baseStructure M)
    (Spec.algebraMap R S) (baseStructure_fac M S) (op ∅) f j

/-- An isomorphism over the original localization descends to a genuine principal
stage, retaining both comparison directions against the supplied original iso. -/
theorem exists_iso_with_comparison
    (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (e : (Over.pullback (Spec.algebraMap R S)).obj (Over.mk f) ≅
      (Over.pullback (Spec.algebraMap R S)).obj (Over.mk g)) :
    ∃ (j : Over (op (∅ : Finset M)))
      (e' : (Over.pullback ((baseStructure M).app j.left)).obj (Over.mk f) ≅
        (Over.pullback ((baseStructure M).app j.left)).obj (Over.mk g)),
      comparison M S f j ≫ e'.hom.left = e.hom.left ≫ comparison M S g j ∧
      comparison M S g j ≫ e'.inv.left = e.inv.left ≫ comparison M S f j := by
  have (j : (Finset M)ᵒᵖ) : CompactSpace ((specDiagram M).obj j) := by
    change CompactSpace (Spec (.of (stage M j.unop)))
    infer_instance
  have (j : (Finset M)ᵒᵖ) : QuasiSeparatedSpace ((specDiagram M).obj j) := by
    change QuasiSeparatedSpace (Spec (.of (stage M j.unop)))
    infer_instance
  exact OverBaseSpreading.exists_iso_with_comparison (specDiagram M) (specCone M S)
    (baseStructure M) (Spec.algebraMap R S) (baseStructure_fac M S) (op ∅)
    (specConeIsLimit M S) f g e

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
