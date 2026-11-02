/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SquareCoefficientAdjoint

/-! # The original pulled coefficient triangle under its two adjunctions -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

lemma triangleSquareCoefficientMap_homEquiv {X₀ X₁ Y₀ Y₁ W : Scheme.{u}}
    (f : X₁ ⟶ X₀) (h : Y₁ ⟶ Y₀) (v₀ : Y₀ ⟶ X₀) (v₁ : Y₁ ⟶ X₁)
    (q₀ : W ⟶ Y₀) (q₁ : W ⟶ Y₁)
    (he : v₁ ≫ f = h ≫ v₀) (hq : q₁ ≫ h = q₀)
    {F : AbelianSheaf.{u, u + 1} X₀} {G : AbelianSheaf.{u, u + 1} X₁}
    {K : AbelianSheaf.{u, u + 1} W}
    (φ : (inverseImage f).obj F ⟶ G)
    (ψ : (inverseImage q₁).obj ((inverseImage v₁).obj G) ⟶ K) :
    (inverseImageAdjunction v₀).homEquiv _ _
        ((inverseImageAdjunction q₀).homEquiv _ _
          (triangleCoefficientMap h q₀ q₁ hq
            (squareCoefficientMap v₀ v₁ f h he φ) ≫ ψ)) =
      (inverseImageAdjunction f).homEquiv _ _ φ ≫
        (directImage f).map ((inverseImageAdjunction v₁).homEquiv _ _
          ((inverseImageAdjunction q₁).homEquiv _ _ ψ)) ≫
        (directImageSquareIso v₀ v₁ f h he).inv.app ((directImage q₁).obj K) ≫
        (directImage v₀).map ((directImageTriangleIso h q₀ q₁ hq).hom.app K) := by
  let ζ := (inverseImageAdjunction q₁).homEquiv _ _ ψ
  let σ := squareCoefficientMap v₀ v₁ f h he φ
  have hc := squareCoefficientMap_homEquiv f h v₀ v₁ he φ ζ
  rw [Adjunction.comp_homEquiv] at hc
  change (inverseImageAdjunction v₀).homEquiv _ _
    ((inverseImageAdjunction h).homEquiv _ _ (σ ≫ ζ)) = _ at hc
  rw [Adjunction.homEquiv_naturality_right] at hc
  have ht := triangleCoefficientMap_homEquiv h q₀ q₁ hq σ ψ
  have ht' := ht.trans (Category.assoc _ _ _).symm
  have hv := congrArg
    ((inverseImageAdjunction v₀).homEquiv F ((directImage q₀).obj K)) ht'
  have hn := (inverseImageAdjunction v₀).homEquiv_naturality_right
    ((inverseImageAdjunction h).homEquiv _ _ σ ≫ (directImage h).map ζ)
    ((directImageTriangleIso h q₀ q₁ hq).hom.app K)
  have he' := congrArg
    (fun z : F ⟶ (directImage v₀).obj ((directImage h).obj ((directImage q₁).obj K)) =>
      z ≫ (directImage v₀).map ((directImageTriangleIso h q₀ q₁ hq).hom.app K)) hc
  simpa only [Category.assoc] using hv.trans (hn.trans he')

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
