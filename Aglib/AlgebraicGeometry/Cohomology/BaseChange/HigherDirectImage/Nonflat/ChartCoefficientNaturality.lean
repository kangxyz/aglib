/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCoefficient

/-! # Coefficient naturality on the original chart arrows

The original coefficient square restricts to the original chart square.
The proof uses the actual component formula and ordinary sheaf naturality.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

/-- The native chart coefficient construction preserves every original coefficient square. -/
theorem chartCoefficient_naturality {X Y U V : Scheme.{u}}
    (p : Y ⟶ X) (a : U ⟶ X) (c : V ⟶ Y) (q : V ⟶ U)
    [IsOpenImmersion a] [IsOpenImmersion c] (w : q ≫ a = c ≫ p)
    {M M' : X.Modules} {N N' : Y.Modules}
    (ψ : M ⟶ (pushforward p).obj N) (ψ' : M' ⟶ (pushforward p).obj N')
    (μ : M ⟶ M') (ν : N ⟶ N') (h : μ ≫ ψ' = ψ ≫ (pushforward p).map ν) :
    (restrictFunctor a).map μ ≫ chartCoefficient p a c q w ψ' =
      chartCoefficient p a c q w ψ ≫ (pushforward q).map ((restrictFunctor c).map ν) := by
  apply Scheme.Modules.hom_ext
  intro O
  have hs := congrArg (fun t => t.app (a ''ᵁ O)) h
  change μ.app (a ''ᵁ O) ≫ ψ'.app (a ''ᵁ O) =
    ψ.app (a ''ᵁ O) ≫ ν.app (p ⁻¹ᵁ (a ''ᵁ O)) at hs
  have hn := ν.mapPresheaf.naturality
    (homOfLE (chartCoefficient_image_le p a c q w O)).op
  change N.presheaf.map (homOfLE (chartCoefficient_image_le p a c q w O)).op ≫
      ν.app (c ''ᵁ (q ⁻¹ᵁ O)) =
    ν.app (p ⁻¹ᵁ (a ''ᵁ O)) ≫
      N'.presheaf.map (homOfLE (chartCoefficient_image_le p a c q w O)).op at hn
  simp only [Hom.comp_app, chartCoefficient_app]
  change μ.app (a ''ᵁ O) ≫
      (ψ'.app (a ''ᵁ O) ≫ N'.presheaf.map _ ) =
    (ψ.app (a ''ᵁ O) ≫ N.presheaf.map _) ≫ ν.app (c ''ᵁ (q ⁻¹ᵁ O))
  rw [← Category.assoc, hs, Category.assoc, ← hn, ← Category.assoc]

end AlgebraicGeometry.Scheme.Modules.Nonflat
