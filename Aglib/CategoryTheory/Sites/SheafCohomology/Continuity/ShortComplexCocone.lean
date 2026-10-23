/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexColimit

/-! # Exactness from actual componentwise colimit cocones

For complexes arising on varying sites there need not be a common source
category of coefficients. This leaf accepts the actual diagram of short
complexes and actual colimit certificates on its three components.
-/

@[expose] public noncomputable section

namespace CategoryTheory.ShortComplex

open Limits

universe uI vI uB vB

variable {I : Type uI} [Category.{vI} I]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasColimitsOfShape I B]
  (G : I ⥤ ShortComplex B) (c : Cocone G)
  (h₁ : IsColimit (π₁.mapCocone c))
  (h₂ : IsColimit (π₂.mapCocone c))
  (h₃ : IsColimit (π₃.mapCocone c))

/-- The comparison to the specified cocone, using its three actual colimit certificates. -/
def componentwiseCoconeIso :
    (((functorEquivalence I B).inverse.obj G).map colim) ≅ c.pt := by
  let e₁ : colimit (G ⋙ π₁) ≅ c.pt.X₁ :=
    colimit.isoColimitCocone ⟨π₁.mapCocone c, h₁⟩
  let e₂ : colimit (G ⋙ π₂) ≅ c.pt.X₂ :=
    colimit.isoColimitCocone ⟨π₂.mapCocone c, h₂⟩
  let e₃ : colimit (G ⋙ π₃) ≅ c.pt.X₃ :=
    colimit.isoColimitCocone ⟨π₃.mapCocone c, h₃⟩
  have he₁ (i : I) : colimit.ι (G ⋙ π₁) i ≫ e₁.hom = (c.ι.app i).τ₁ :=
    colimit.isoColimitCocone_ι_hom ⟨π₁.mapCocone c, h₁⟩ i
  have he₂ (i : I) : colimit.ι (G ⋙ π₂) i ≫ e₂.hom = (c.ι.app i).τ₂ :=
    colimit.isoColimitCocone_ι_hom ⟨π₂.mapCocone c, h₂⟩ i
  have he₃ (i : I) : colimit.ι (G ⋙ π₃) i ≫ e₃.hom = (c.ι.app i).τ₃ :=
    colimit.isoColimitCocone_ι_hom ⟨π₃.mapCocone c, h₃⟩ i
  refine isoMk e₁ e₂ e₃ ?_ ?_
  · apply colimit.hom_ext
    intro i
    change colimit.ι (G ⋙ π₁) i ≫ (e₁.hom ≫ c.pt.f) =
      colimit.ι (G ⋙ π₁) i ≫ (colim.map (Functor.whiskerLeft G π₁Toπ₂) ≫ e₂.hom)
    rw [← Category.assoc, he₁, colimit.ι_map_assoc, he₂]
    exact (c.ι.app i).comm₁₂
  · apply colimit.hom_ext
    intro i
    change colimit.ι (G ⋙ π₂) i ≫ (e₂.hom ≫ c.pt.g) =
      colimit.ι (G ⋙ π₂) i ≫ (colim.map (Functor.whiskerLeft G π₂Toπ₃) ≫ e₃.hom)
    rw [← Category.assoc, he₂, colimit.ι_map_assoc, he₃]
    exact (c.ι.app i).comm₂₃

include h₁ h₂ h₃ in
/-- Exact filtered colimits transport stage exactness to the specified target;
no injectivity assertion about an inverse-image coefficient is used. -/
lemma exact_of_componentwise_colimit [HasExactColimitsOfShape I B]
    (hG : ∀ i, (G.obj i).Exact) : c.pt.Exact := by
  let T := (functorEquivalence I B).inverse.obj G
  have hT : T.Exact := exact_of_evaluation T (fun i => by
    change (G.obj i).Exact
    exact hG i)
  exact exact_of_iso (componentwiseCoconeIso G c h₁ h₂ h₃) (hT.map colim)

end CategoryTheory.ShortComplex
