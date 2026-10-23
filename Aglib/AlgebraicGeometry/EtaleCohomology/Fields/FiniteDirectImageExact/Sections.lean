/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteDirectImageExact.Splitting
public import Aglib.Algebra.Category.Grp.ProductSections

/-! # Original direct-image sections on a labelled splitting chart -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.FiniteEtale

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields.FiniteDirectImage

variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
  {V : X.Etale} {A : FintypeCat.{u}}
  (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y)

/-- The actual comparison from the coproduct of component tests to the original test. -/
def testCoproductMap (U : V.left.Etale) :
    Etale.coproductChart (componentTest Y e U) ⟶ pullbackTest Y U :=
  MorphismProperty.Over.homMk
    (Sigma.desc (fun a => (componentTestInclusion Y e U a).left)) (by
      change Sigma.desc (fun a => (componentTestInclusion Y e U a).left) ≫
        (pullbackTest Y U).hom = Sigma.desc (fun a => (componentTest Y e U a).hom)
      apply Sigma.hom_ext
      intro a
      simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
      exact MorphismProperty.Over.w (componentTestInclusion Y e U a))

@[reassoc] theorem testCoproductMap_ι (U : V.left.Etale) (a : A) :
    Etale.coproductChartInclusion (componentTest Y e U) a ≫ testCoproductMap Y e U =
      componentTestInclusion Y e U a := by
  apply MorphismProperty.Over.Hom.ext
  exact Sigma.ι_comp_desc _ _

instance testCoproductMap_isIso (U : V.left.Etale) : IsIso (testCoproductMap Y e U) := by
  let G := Etale.forget Y.obj.left ⋙ Over.forget Y.obj.left
  let : IsIso (G.map (testCoproductMap Y e U)) := componentTestInclusion_isIso Y e U
  exact isIso_of_reflects_iso (testCoproductMap Y e U) G

/-- The product comparison is literally restriction along the actual component maps. -/
theorem splitSections_bijective
    (F : AbelianSheaf.{u, u + 1} Y.obj.left) (U : V.left.Etale) :
    Function.Bijective (fun x : F.obj.obj (op (pullbackTest Y U)) =>
      fun a => F.obj.map (componentTestInclusion Y e U a).op x) := by
  have h := (Etale.coproductSections_bijective (componentTest Y e U) F).comp
    (ConcreteCategory.bijective_of_isIso (F.obj.map (testCoproductMap Y e U).op))
  convert h using 1
  funext x a
  change F.obj.map (componentTestInclusion Y e U a).op x =
    F.obj.map (Etale.coproductChartInclusion (componentTest Y e U) a).op
      (F.obj.map (testCoproductMap Y e U).op x)
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp, testCoproductMap_ι]

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields.FiniteDirectImage
