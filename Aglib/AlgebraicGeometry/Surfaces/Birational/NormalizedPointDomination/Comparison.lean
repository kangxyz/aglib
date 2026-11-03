/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.ChainComposition
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CurveSurvival

/-!
# Actual output diagrams for normalized-point curve elimination

This is internal output packaging for one actual geometric diagram. The
curve embedding is derived from original proper images, not supplied. The
main existence theorem will construct the diagram and expose its actual
chain and comparison; this packaging is not a termination premise.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u
open Blowup

/-- One constructed actual comparison diagram, with a literal normalized
point chain and geometric noncollapse. No curve injection or finite path is
supplied independently of its original scheme maps. -/
structure NormalPointComparison {Q S : Scheme.{u}} [IsIntegral Q] [IsIntegral S]
    (q : Q ⟶ S) where
  /-- The actual new base. -/
  base : Scheme.{u}
  /-- The actual dominating model. -/
  model : Scheme.{u}
  /-- The accumulated literal normalized-point blowdown. -/
  beta : base ⟶ S
  /-- Projection to the actual new base. -/
  p : model ⟶ base
  /-- Comparison with the original model. -/
  g : model ⟶ Q
  /-- The original commuting scheme square. -/
  comm : g ≫ q = p ≫ beta
  /-- The existing chain object on the original accumulated map. -/
  chain : NormalizedPointBlowupChain beta
  /-- Integrality of the constructed base. -/
  [baseIntegral : IsIntegral base]
  /-- Integrality of the constructed model. -/
  [modelIntegral : IsIntegral model]
  /-- Noetherianity of the constructed base. -/
  [baseNoetherian : IsNoetherian base]
  /-- Noetherianity of the constructed model. -/
  [modelNoetherian : IsNoetherian model]
  /-- Normality of the actual base stalks. -/
  baseNormal : NormalStalks base
  /-- Normality of the actual model stalks. -/
  modelNormal : NormalStalks model
  /-- The base retains the surface dimension bound. -/
  baseDimension : topologicalKrullDim base ≤ 2
  /-- The model retains the surface dimension bound. -/
  modelDimension : topologicalKrullDim model ≤ 2
  /-- Properness of the original blowdown. -/
  [betaProper : IsProper beta]
  /-- Properness of the original base projection. -/
  [pProper : IsProper p]
  /-- Properness of the original model comparison. -/
  [gProper : IsProper g]
  /-- Dominance of the original blowdown. -/
  [betaDominant : IsDominant beta]
  /-- Dominance of the original base projection. -/
  [pDominant : IsDominant p]
  /-- Dominance of the original model comparison. -/
  [gDominant : IsDominant g]
  /-- Birationality through the original blowdown field map. -/
  betaBirational : IsIso (CommRingCat.ofHom (functionFieldMap beta))
  /-- Birationality through the original base-projection field map. -/
  pBirational : IsIso (CommRingCat.ofHom (functionFieldMap p))
  /-- Birationality through the original model-comparison field map. -/
  gBirational : IsIso (CommRingCat.ofHom (functionFieldMap g))
  /-- Actual new contracted curves do not collapse under the comparison map. -/
  noncollapse : ∀ C : IrreducibleCloseds model, C ∈ contractedCurves p →
    ¬ (g '' (C : Set model)).Subsingleton

namespace NormalPointComparison

attribute [instance] baseIntegral modelIntegral baseNoetherian modelNoetherian
  betaProper pProper gProper betaDominant pDominant gDominant

variable {Q S : Scheme.{u}} [IsIntegral Q] [IsIntegral S] {q : Q ⟶ S}

/-- The curve embedding is the actual proper image, with membership and
injectivity proved from the original geometric maps. -/
def curveEmbedding [IsLocallyNoetherian Q] (B : NormalPointComparison q)
    (hQ : NormalStalks Q) (hdQ : topologicalKrullDim Q ≤ 2) :
    contractedCurves B.p ↪ contractedCurves q where
  toFun C := ⟨B.g.irreducibleClosedImage C.val,
    Hom.irreducibleClosedImage_mem_contractedCurves B.p B.pBirational B.baseNormal
      B.g B.gBirational hQ hdQ q B.beta B.comm C.val C.property
      (B.noncollapse C.val C.property)⟩
  inj' := by
    intro C D he
    apply Subtype.ext
    exact B.g.irreducibleClosedImage_injective_of_not_subsingleton B.gBirational hQ hdQ
      C.val D.val (B.noncollapse C.val C.property) (congrArg Subtype.val he)

/-- Composition retains one actual model, the original scheme square and the
existing concatenated chain. Noncollapse is proved by successive proper images. -/
def comp (B : NormalPointComparison q) (D : NormalPointComparison B.p) :
    NormalPointComparison q where
  base := D.base
  model := D.model
  beta := D.beta ≫ B.beta
  p := D.p
  g := D.g ≫ B.g
  comm := by
    calc
      (D.g ≫ B.g) ≫ q = D.g ≫ (B.g ≫ q) := Category.assoc _ _ _
      _ = D.g ≫ (B.p ≫ B.beta) := congrArg (fun k ↦ D.g ≫ k) B.comm
      _ = (D.g ≫ B.p) ≫ B.beta := (Category.assoc _ _ _).symm
      _ = (D.p ≫ D.beta) ≫ B.beta := congrArg (fun k ↦ k ≫ B.beta) D.comm
      _ = D.p ≫ (D.beta ≫ B.beta) := Category.assoc _ _ _
  chain := B.chain.comp D.chain
  baseNormal := D.baseNormal
  modelNormal := D.modelNormal
  baseDimension := D.baseDimension
  modelDimension := D.modelDimension
  betaBirational := by
    let := B.betaBirational
    let := D.betaBirational
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  pBirational := D.pBirational
  gBirational := by
    let := B.gBirational
    let := D.gBirational
    rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  noncollapse := by
    intro C hC
    have hmid := Hom.irreducibleClosedImage_mem_contractedCurves D.p D.pBirational
      D.baseNormal D.g D.gBirational B.modelNormal B.modelDimension B.p D.beta D.comm
      C hC (D.noncollapse C hC)
    have hn := B.noncollapse (D.g.irreducibleClosedImage C) hmid
    change ¬ (B.g '' (D.g '' (C : Set D.model))).Subsingleton at hn
    change ¬ ((fun z ↦ B.g (D.g z)) '' (C : Set D.model)).Subsingleton
    simpa only [Set.image_image] using hn

/-- Successive geometric curve images equal the image under the original
composite comparison map. -/
theorem curveEmbedding_comp [IsLocallyNoetherian Q]
    (B : NormalPointComparison q) (D : NormalPointComparison B.p)
    (hQ : NormalStalks Q) (hdQ : topologicalKrullDim Q ≤ 2)
    (C : contractedCurves D.p) :
    (B.comp D).curveEmbedding hQ hdQ C =
      B.curveEmbedding hQ hdQ (D.curveEmbedding B.modelNormal B.modelDimension C) := by
  apply Subtype.ext
  exact Hom.irreducibleClosedImage_comp D.g B.g C.val

/-- Once the actual surviving curve is eliminated, the original selected
curve is missing from the composite proper-image embedding. -/
theorem missing_curve_comp [IsLocallyNoetherian Q]
    (B : NormalPointComparison q) (D : NormalPointComparison B.p)
    (hQ : NormalStalks Q) (hdQ : topologicalKrullDim Q ≤ 2)
    (C : contractedCurves q) (C' : contractedCurves B.p)
    (himage : B.curveEmbedding hQ hdQ C' = C)
    (hmiss : C' ∉ Set.range (D.curveEmbedding B.modelNormal B.modelDimension)) :
    C ∉ Set.range ((B.comp D).curveEmbedding hQ hdQ) := by
  rintro ⟨E, hE⟩
  apply hmiss
  refine ⟨E, (B.curveEmbedding hQ hdQ).injective ?_⟩
  rw [← B.curveEmbedding_comp D hQ hdQ E]
  exact hE.trans himage.symm

end NormalPointComparison
end AlgebraicGeometry.Scheme.NormalizedPointDomination
