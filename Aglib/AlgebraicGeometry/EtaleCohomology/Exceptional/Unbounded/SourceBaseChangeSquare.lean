/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons
public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceBaseChange

/-! # The actual unbounded inverse-image square for source-isomorphism base change -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX wX' wL wL'
variable {X X' S T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  (e : X' ≅ X) (he : e.hom ≫ f = f') (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wL'} (ModuleSheaf (pullback b f') Λ)]

/-- The actual universal projection equality followed by the original native compositor. -/
def moduleUnboundedRawSourceBaseChangeSourceIso :
    moduleUnboundedDerivedInverseImage Λ (pullback.snd b f' ≫ e.hom) ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd b f) ⋙
        moduleUnboundedDerivedInverseImage Λ (sourceBaseChangeIso f f' e he b).hom :=
  eqToIso (congrArg (fun a => moduleUnboundedDerivedInverseImage Λ a)
      (sourceBaseChangeIso_hom_snd f f' e he b).symm) ≪≫
    moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd b f)
      (sourceBaseChangeIso f f' e he b).hom

/-- The original inverse-image compositors identify the two actual routes. -/
def moduleUnboundedSourceBaseChangeSquareIso :
    moduleUnboundedDerivedInverseImage Λ e.hom ⋙
        moduleUnboundedDerivedInverseImage Λ (pullback.snd b f') ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd b f) ⋙
        moduleUnboundedDerivedInverseImage Λ (pullbackSourceIso f' e he b).hom :=
  (moduleUnboundedDerivedInverseImageCompIso Λ e.hom (pullback.snd b f')).symm ≪≫
    moduleUnboundedRawSourceBaseChangeSourceIso f f' e he b Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
