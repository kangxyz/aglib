/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramShortExact

/-! # The original stage and limit morphisms of compatible cokernel sequences -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  {F Q : DiagramCoefficientSystem X}
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F Q)

/-- The actual quotient system constructed by the pointwise cokernel universal property. -/
abbrev diagramCokernelSystem : DiagramCoefficientSystem X :=
  InjectiveSystem.System.cokernel (diagramAdjunctionData X) η

/-- The original pointwise coefficient short complex. -/
abbrev diagramCokernelComplex (i : I) : ShortComplex (AbelianSheaf.{u, u + 1} (X.obj i).unop) :=
  InjectiveSystem.System.cokernelShortComplex (diagramAdjunctionData X) η i

/-- Pointwise monicity gives its original short exact certificate. -/
lemma diagramCokernelComplex_shortExact (hη : ∀ i, Mono (η.app i)) (i : I) :
    (diagramCokernelComplex X η i).ShortExact := by
  let : Mono (η.app i) := hη i
  exact InjectiveSystem.System.cokernelShortComplex_shortExact (diagramAdjunctionData X) η i

/-- The original inverse-image transition square is a morphism of actual coefficient sequences. -/
def diagramCokernelTransition {i j : I} (a : i ⟶ j) :
    (diagramCokernelComplex X η i).map (inverseImage (X.map a).unop) ⟶
      diagramCokernelComplex X η j where
  τ₁ := diagramInverseTransition X F a
  τ₂ := diagramInverseTransition X Q a
  τ₃ := diagramInverseTransition X (diagramCokernelSystem X η) a
  comm₁₂ := (diagramInverseTransition_naturality X η a).symm
  comm₂₃ := (diagramInverseTransition_naturality X
    (InjectiveSystem.System.cokernelπ (diagramAdjunctionData X) η) a).symm

variable (c : Cocone X) [HasColimitsOfShape I AddCommGrpCat.{u + 1}]

/-- The original coefficient injections form the actual stage-to-limit sequence morphism. -/
def diagramCokernelLimitLeg (i : I) :
    (diagramCokernelComplex X η i).map (inverseImage (c.ι.app i).unop) ⟶
      coneCoefficientColimitCokernelComplex X c η where
  τ₁ := colimit.ι (coneCoefficientFunctor X c F) i
  τ₂ := colimit.ι (coneCoefficientFunctor X c Q) i
  τ₃ := colimit.ι (coneCoefficientFunctor X c (diagramCokernelSystem X η)) i
  comm₁₂ := coneCoefficientColimitMap_ι X c η i
  comm₂₃ := coneCoefficientColimitMap_ι X c
    (InjectiveSystem.System.cokernelπ (diagramAdjunctionData X) η) i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
