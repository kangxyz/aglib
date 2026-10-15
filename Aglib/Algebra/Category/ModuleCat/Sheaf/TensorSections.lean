/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorPushforward

/-!
Source: `Quillen/Algebra/Category/ModuleCat/Sheaf/TensorSections.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 71]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Sections of the sheaf tensor

Original pure tensors followed by sheafification determine module-sheaf morphisms.
The section formulas retain both coefficient maps and restriction maps.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SheafOfModulesOfCommRing
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
/-- The section obtained by applying the original sheafification unit to a pure tensor. -/
def tensorSection (M N : SheafOfModulesOfCommRing R) (U : Cᵒᵖ)
    (m : ((toPresheaf R).obj M).obj U) (n : ((toPresheaf R).obj N).obj U) :
    ((toPresheaf R).obj ((tensorLeftFunctor R M).obj N)).obj U :=
  ((associatedSheafUnit R).app
    (((toPresheaf R).obj M) ⊗ ((toPresheaf R).obj N))).app U (m ⊗ₜ[R.obj.obj U] n)
/-- Original tensor generators commute with the original presheaf restriction maps. -/
theorem tensorSection_naturality (M N : SheafOfModulesOfCommRing R)
    {U V : Cᵒᵖ} (f : U ⟶ V) (m : ((toPresheaf R).obj M).obj U)
    (n : ((toPresheaf R).obj N).obj U) :
    (((toPresheaf R).obj ((tensorLeftFunctor R M).obj N)).map f)
        (tensorSection R M N U m n) =
      tensorSection R M N V (((toPresheaf R).obj M).map f m)
        (((toPresheaf R).obj N).map f n) := by
  exact (PresheafOfModules.naturality_apply
    ((associatedSheafUnit R).app
      (((toPresheaf R).obj M) ⊗ ((toPresheaf R).obj N))) f
        (m ⊗ₜ[R.obj.obj U] n)).symm
/-- Morphisms from the actual sheaf tensor are determined by the original pure-tensor generators. -/
theorem tensor_hom_ext {M N P : SheafOfModulesOfCommRing R}
    {f g : (tensorLeftFunctor R M).obj N ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (m : ((toPresheaf R).obj M).obj U)
      (n : ((toPresheaf R).obj N).obj U),
      f.val.app U (tensorSection R M N U m n) =
        g.val.app U (tensorSection R M N U m n)) : f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (𝟙 _)).homEquiv _ _ |>.injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h U m n
/-- Both original module maps carry a tensor generator to the tensor of their images. -/
theorem tensor_map_tensorSection {M M' N N' : SheafOfModulesOfCommRing R}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ)
    (m : ((toPresheaf R).obj M).obj U) (n : ((toPresheaf R).obj N).obj U) :
    ((associatedSheaf R).map (((toPresheaf R).map f) ⊗ₘ ((toPresheaf R).map g))).val.app U
        (tensorSection R M N U m n) =
      tensorSection R M' N' U (f.val.app U m) (g.val.app U n) := by
  have h := (associatedSheafUnit R).naturality
    (((toPresheaf R).map f) ⊗ₘ ((toPresheaf R).map g))
  exact (congrArg (fun a => a.app U (m ⊗ₜ[R.obj.obj U] n)) h).symm
end SheafOfModulesOfCommRing
end
