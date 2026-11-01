/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.SectionCone
public import Aglib.AlgebraicGeometry.Modules.Complex.Sections
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.Limits.Shapes.KernelCones
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Original quotient-section kernels

A universally injective exact sequence remains a kernel after the actual
closed-thickening pullback, its native pushforward, and section evaluation.
The original section cones therefore inherit their limit property from the
two right-hand cones. No flatness or new completion object is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (K : X.IdealSheafData) (S : ShortComplex X.Modules)

/-- Original sections preserve an injective exact sequence as a kernel fork. -/
def sectionKernel (hS : S.Exact) [Mono S.f] :
    letI := Complex.sectionsEvaluation_preservesZeroMorphisms (X := X) ⊤
    IsLimit (KernelFork.ofι
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map S.f)
      ((S.map (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))).zero)) := by
  letI := Complex.sectionsEvaluation_preservesZeroMorphisms (X := X) ⊤
  letI := SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op ⊤)
  exact KernelFork.mapIsLimit _ hS.fIsKernel
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))

/-- The same kernel after the original closed-thickening quotient and evaluation. -/
def quotientSectionKernel
    (hS : (S.map (pullback K.subschemeι)).Exact)
    [Mono ((pullback K.subschemeι).map S.f)] :
    letI := Complex.sectionsEvaluation_preservesZeroMorphisms (X := X) ⊤
    IsLimit (KernelFork.ofι
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        ((idealSheafQuotientFunctor X K).map S.f))
      ((S.map (idealSheafQuotientFunctor X K ⋙
        SheafOfModules.evaluation X.ringCatSheaf (op ⊤))).zero)) := by
  letI := Complex.sectionsEvaluation_preservesZeroMorphisms (X := X) ⊤
  letI := SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op ⊤)
  let P := pushforward K.subschemeι ⋙ SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let : Mono (S.map (pullback K.subschemeι)).f :=
    inferInstanceAs (Mono ((pullback K.subschemeι).map S.f))
  have h := KernelFork.mapIsLimit _ hS.fIsKernel P
  exact h

/-- Original vertex and thickening kernels transfer completeness to the left term. -/
def idealSheafSectionCone_isLimit_of_universallyExact
    (hS : S.Exact) [Mono S.f]
    (hbase : ∀ (Y : Scheme.{u}) (a : Y ⟶ X),
      (S.map (pullback a)).Exact ∧ Mono ((pullback a).map S.f))
    (h₂ : IsLimit (idealSheafSectionCone X K S.X₂))
    (h₃ : IsLimit (idealSheafSectionCone X K S.X₃)) :
    IsLimit (idealSheafSectionCone X K S.X₁) := by
  letI := Complex.sectionsEvaluation_preservesZeroMorphisms (X := X) ⊤
  let E := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let i := idealSheafSectionDiagramHom X K S.f
  let g := idealSheafSectionDiagramHom X K S.g
  have w (n : ℕᵒᵖ) : i.app n ≫ g.app n = 0 :=
    (S.map (idealSheafQuotientFunctor X (K ^ n.unop) ⋙ E)).zero
  have ha (n : ℕᵒᵖ) : E.map S.f ≫ (idealSheafSectionCone X K S.X₂).π.app n =
      (idealSheafSectionCone X K S.X₁).π.app n ≫ i.app n :=
    congrArg (fun t => t.app n) (idealSheafSectionCone_naturality X K S.f)
  have hb (n : ℕᵒᵖ) : E.map S.g ≫ (idealSheafSectionCone X K S.X₃).π.app n =
      (idealSheafSectionCone X K S.X₂).π.app n ≫ g.app n :=
    congrArg (fun t => t.app n) (idealSheafSectionCone_naturality X K S.g)
  refine isLimit_of_kernelCones i g w
    (idealSheafSectionCone X K S.X₁) (idealSheafSectionCone X K S.X₂)
    (idealSheafSectionCone X K S.X₃) (E.map S.f) (E.map S.g)
    (S.map E).zero ha hb (sectionKernel X S hS) ?_ h₂ h₃
  intro n
  obtain ⟨hn, hm⟩ := hbase _ (K ^ n.unop).subschemeι
  let := hm
  exact quotientSectionKernel X (K ^ n.unop) S hn

end AlgebraicGeometry.Scheme.Modules.Coherent
