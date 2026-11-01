/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChange
public import Aglib.CategoryTheory.NatTrans.SourceIsoToTarget

/-! # The actual direct-image exchange under source isomorphism -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wX' wS
variable {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  (e : X' ≅ X) (h : e.hom ≫ f = f') (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- The original source-only β, normalized by the original inverse-image identity. -/
def moduleUnboundedDirectImageSourceTransport :
    moduleUnboundedDerivedDirectImage Λ f ⟶
      moduleUnboundedDerivedInverseImage Λ e.hom ⋙ moduleUnboundedDerivedDirectImage Λ f' :=
  identityBaseExchange (moduleUnboundedDerivedInverseImageIdIso Λ S)
    (moduleUnboundedDerivedBaseChangeMap Λ f f' (𝟙 S) e.hom
      ((Category.comp_id f').trans h.symm))
end AlgebraicGeometry.Scheme.EtaleCohomology
