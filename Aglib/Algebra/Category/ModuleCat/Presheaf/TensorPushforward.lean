/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Aglib.Algebra.Category.ModuleCat.Monoidal.RestrictScalars

/-!
Source: `Quillen/Algebra/Category/ModuleCat/Presheaf/TensorPushforward.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 69]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Tensor and module-presheaf pushforward

The comparison is formed from the original sectionwise scalar-restriction tensor maps.
It is natural in both module arguments and invertible when the ring morphism is invertible.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
namespace PresheafOfModulesOfCommRing
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⟶ F.op ⋙ R)
/-- The original sectionwise scalar-restriction tensor map. -/
def pushforwardTensorHom (M N : PresheafOfModulesOfCommRing.{u} R) :
    (pushforward φ).obj M ⊗ (pushforward φ).obj N ⟶ (pushforward φ).obj (M ⊗ N) where
  app U := LaxMonoidal.μ (ModuleCat.restrictScalars (φ.app U).hom)
    (M.obj (F.op.obj U)) (N.obj (F.op.obj U))
  naturality {U V} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    change LaxMonoidal.μ (ModuleCat.restrictScalars (φ.app V).hom)
      (M.obj (F.op.obj V)) (N.obj (F.op.obj V))
      (M.map (F.op.map f) m ⊗ₜ[S.obj V] N.map (F.op.map f) n) =
      (M ⊗ N).map (F.op.map f)
        (LaxMonoidal.μ (ModuleCat.restrictScalars (φ.app U).hom)
          (M.obj (F.op.obj U)) (N.obj (F.op.obj U)) (m ⊗ₜ[S.obj U] n))
    rw [ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul]
    rfl
/-- The comparison retains the original pure tensors. -/
theorem pushforwardTensorHom_tmul (M N : PresheafOfModulesOfCommRing.{u} R)
    (U : Cᵒᵖ) (m : M.obj (F.op.obj U)) (n : N.obj (F.op.obj U)) :
    (pushforwardTensorHom φ M N).app U (m ⊗ₜ[S.obj U] n) =
      m ⊗ₜ[R.obj (F.op.obj U)] n :=
  ModuleCat.restrictScalars_μ_tmul _ _ _ _ _
/-- Both coefficient maps commute with the original tensor comparison. -/
theorem pushforwardTensorHom_naturality
    {M M' N N' : PresheafOfModulesOfCommRing.{u} R} (f : M ⟶ M') (g : N ⟶ N') :
    ((pushforward φ).map f ⊗ₘ (pushforward φ).map g) ≫
        pushforwardTensorHom φ M' N' =
      pushforwardTensorHom φ M N ≫ (pushforward φ).map (f ⊗ₘ g) := by
  ext U : 1
  exact LaxMonoidal.μ_natural (ModuleCat.restrictScalars (φ.app U).hom)
    (f.app (F.op.obj U)) (g.app (F.op.obj U))
/-- The tensor comparison is invertible when the original ring map is an isomorphism. -/
def pushforwardTensorIso [IsIso φ] (M N : PresheafOfModulesOfCommRing.{u} R) :
    (pushforward φ).obj M ⊗ (pushforward φ).obj N ≅ (pushforward φ).obj (M ⊗ N) := by
  have h (U : Cᵒᵖ) : IsIso ((pushforwardTensorHom φ M N).app U) := by
    change IsIso (LaxMonoidal.μ (ModuleCat.restrictScalars (φ.app U).hom) _ _)
    exact ModuleCat.isIso_restrictScalars_tensor
      ((asIso (φ.app U)).commRingCatIsoToRingEquiv) _ _
  exact isoMk (fun U => asIso ((pushforwardTensorHom φ M N).app U))
    (fun {_ _} f => (pushforwardTensorHom φ M N).naturality f)
/-- The isomorphism uses the original comparison arrow. -/
theorem pushforwardTensorIso_hom [IsIso φ] (M N : PresheafOfModulesOfCommRing.{u} R) :
    (pushforwardTensorIso φ M N).hom = pushforwardTensorHom φ M N := rfl
end PresheafOfModulesOfCommRing
