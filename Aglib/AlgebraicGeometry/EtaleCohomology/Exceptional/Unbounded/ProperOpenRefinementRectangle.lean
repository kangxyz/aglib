/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenCongruence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenMateCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementDirectImage
public import Aglib.CategoryTheory.Adjunction.NaturalPastedRectangle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenVerticalPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenRefinementTarget

/-! # The original vertical proper/open refinement rectangle

Two actual Cartesian pastings and equality transport of their original mixed
mates yield the middle refinement rectangle. The normalizations are the original
over-base direct-image comparison, identity and composition maps. No tower
geometry or desired refinement equation is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wY wAC wAD wBC wBD wTC wTD

variable (Λ : Type (u + 1)) [Ring Λ]

variable {Y AC AD BC BD TC TD : Scheme.{u}}
  (iC : Y ⟶ TC) (iD : Y ⟶ TD) (mC : AC ⟶ BC) (mD : AD ⟶ BD)
  (qC : AC ⟶ Y) (qD : AD ⟶ Y) (rC : BC ⟶ TC) (rD : BD ⟶ TD)
  (hA : AC ⟶ AD) (hB : BC ⟶ BD) (hT : TC ⟶ TD)
  [Etale iC] [Etale iD] [Etale mC] [Etale mD]
  (sqC : IsPullback mC qC rC iC) (sqD : IsPullback mD qD rD iD)
  (sqMid : IsPullback mC hA hB mD) (sqTarget : IsPullback iC (𝟙 Y) hT iD)
  (hq : hA ≫ qD = qC) (hr : hB ≫ rD = rC ≫ hT)
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wAC} (ModuleSheaf AC Λ)]
  [HasDerivedCategory.{wAD} (ModuleSheaf AD Λ)]
  [HasDerivedCategory.{wBC} (ModuleSheaf BC Λ)]
  [HasDerivedCategory.{wBD} (ModuleSheaf BD Λ)]
  [HasDerivedCategory.{wTC} (ModuleSheaf TC Λ)]
  [HasDerivedCategory.{wTD} (ModuleSheaf TD Λ)]

/-- The actual middle vertical mixed-mate rectangle, normalized by the original
identity, over-base and commuting-proper-side comparisons. -/
theorem moduleUnboundedProperOpenMate_refinement_rectangle :
    NaturalPastedRectangleEquation
      (moduleUnboundedProperOpenMate qD mD iD rD sqD.flip Λ)
      (moduleUnboundedProperOpenMate hA mC mD hB sqMid.flip Λ)
      (moduleUnboundedProperOpenMate (𝟙 Y) iC iD hT sqTarget.flip Λ)
      (moduleUnboundedProperOpenMate qC mC iC rC sqC.flip Λ)
      (moduleUnboundedDerivedDirectImageOverIso Λ qC qD hA hq)
      (moduleUnboundedDerivedDirectImageIdIso Λ Y)
      (moduleUnboundedProperOpenRefinementTargetIso Λ rC rD hB hT hr) := by
  let sq₁ := sqMid.flip.paste_horiz sqD.flip
  let sq₂ := sqC.flip.paste_horiz sqTarget.flip
  let eg := hq.trans (Category.comp_id qC).symm
  exact naturalPastedRectangle_of_vertical
    (moduleUnboundedProperOpenMate qD mD iD rD sqD.flip Λ)
    (moduleUnboundedProperOpenMate hA mC mD hB sqMid.flip Λ)
    (moduleUnboundedProperOpenMate (𝟙 Y) iC iD hT sqTarget.flip Λ)
    (moduleUnboundedProperOpenMate qC mC iC rC sqC.flip Λ)
    (moduleUnboundedProperOpenMate (hA ≫ qD) mC iD (hB ≫ rD) sq₁ Λ)
    (moduleUnboundedProperOpenMate (qC ≫ 𝟙 Y) mC iD (rC ≫ hT) sq₂ Λ)
    (moduleUnboundedDerivedDirectImageCompIso Λ qD hA)
    (moduleUnboundedDerivedDirectImageCompIso Λ (𝟙 Y) qC)
    (moduleUnboundedDerivedDirectImageCompIso Λ rD hB)
    (moduleUnboundedDerivedDirectImageCompIso Λ hT rC)
    (eqToIso (congrArg (fun f : AC ⟶ Y => moduleUnboundedDerivedDirectImage Λ f) hq))
    (eqToIso (congrArg (fun f : AC ⟶ Y => moduleUnboundedDerivedDirectImage Λ f)
      (Category.comp_id qC)))
    (eqToIso (congrArg (fun f : AC ⟶ Y => moduleUnboundedDerivedDirectImage Λ f) eg))
    (eqToIso (congrArg (fun f : BC ⟶ TD => moduleUnboundedDerivedDirectImage Λ f) hr))
    (moduleUnboundedDerivedDirectImageOverIso Λ qC qD hA hq)
    (moduleUnboundedDerivedDirectImageIdIso Λ Y)
    (moduleUnboundedProperOpenRefinementTargetIso Λ rC rD hB hT hr)
    (moduleUnboundedProperOpenMate_vComp_actual Λ iD mD mC qD hA rD hB
      sqD.flip sqMid.flip sq₁)
    (moduleUnboundedProperOpenMate_vComp_actual Λ iD iC mC (𝟙 Y) qC hT rC
      sqTarget.flip sqC.flip sq₂)
    (eqToIso_triangle _ _ _)
    (moduleUnboundedProperOpenMate_congr Λ iD mC eg hr sq₁ sq₂)
    rfl (moduleUnboundedDerivedDirectImageCompIso_id_comp Λ qC) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
