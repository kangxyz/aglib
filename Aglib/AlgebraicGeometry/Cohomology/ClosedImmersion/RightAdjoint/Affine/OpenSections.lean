/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Affine.SourceIsomorphism

/-!
# Actual affine open-square maps on closed-adjoint sections

The geometric open comparison is normalized by the original closed counits
and the original two restriction units. The resulting coinduced Hom formula
uses actual affine sections, with no quasicoherence assumption on a coefficient
or an injective-resolution term.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem cartesianPushforwardSquare_top
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) (M : W.Modules) :
    ((cartesianPushforwardSquare a b f j h).hom.app M).app ⊤ = 𝟙 Γ(M, ⊤) := by
  simp only [cartesianPushforwardSquare, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Hom.comp_app, pushforwardComp_hom_app_app,
    pushforwardComp_inv_app_app, pushforwardCongr_hom_app_app]
  change (𝟙 Γ(M, ⊤)) ≫ M.presheaf.map _ ≫ (𝟙 Γ(M, ⊤)) = 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  calc
    _ = M.presheaf.map (𝟙 (Opposite.op ⊤)) := congrArg _ (Subsingleton.elim _ _)
    _ = _ := M.presheaf.map_id _

variable {A A' B B' : CommRingCat.{u}}
  (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)]
  (h : IsPullback (Spec.map ψ) (Spec.map τ) (Spec.map σ) (Spec.map φ))

/-- Original source restriction on sections followed by the original ordinary
closed-adjoint open comparison. -/
def closedImmersionRightAdjointAffineOpenSections (N : (Spec A).Modules) :
    (moduleSpecΓFunctor (R := B)).obj
        ((closedImmersionRightAdjoint (Spec.map σ)).obj N) ⟶
      (ModuleCat.restrictScalars ψ.hom).obj
        ((moduleSpecΓFunctor (R := B')).obj
          ((closedImmersionRightAdjoint (Spec.map τ)).obj
            ((restrictFunctor (Spec.map φ)).obj N))) :=
  moduleSpecΓFunctor.map
      ((restrictAdjunction (Spec.map ψ)).unit.app
        ((closedImmersionRightAdjoint (Spec.map σ)).obj N)) ≫
    (pushforwardGlobalSectionsIso ψ).hom.app
      ((restrictFunctor (Spec.map ψ)).obj
        ((closedImmersionRightAdjoint (Spec.map σ)).obj N)) ≫
    (ModuleCat.restrictScalars ψ.hom).map
      (moduleSpecΓFunctor.map
        ((closedImmersionRightAdjointOpenIso (Spec.map ψ) (Spec.map τ)
          (Spec.map σ) (Spec.map φ) h).hom.app N))

/-- Evaluation at one after the actual affine open-square map is the original
ambient restriction of evaluation at one. -/
theorem closedImmersionRightAdjointAffineOpenSections_apply_one
    (N : (Spec A).Modules)
    (x : (moduleSpecΓFunctor (R := B)).obj
      ((closedImmersionRightAdjoint (Spec.map σ)).obj N)) :
    closedImmersionRightAdjointSectionsLinearEquiv τ
        ((restrictFunctor (Spec.map φ)).obj N)
        (closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h N x) (1 : B') =
      (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app N) ≫
        (pushforwardGlobalSectionsIso φ).hom.app ((restrictFunctor (Spec.map φ)).obj N))
        (closedImmersionRightAdjointSectionsLinearEquiv σ N x (1 : B)) := by
  let K := (closedImmersionRightAdjoint (Spec.map σ)).obj N
  let o := (closedImmersionRightAdjointOpenIso (Spec.map ψ) (Spec.map τ)
    (Spec.map σ) (Spec.map φ) h).hom.app N
  let y : (moduleSpecΓFunctor (R := B')).obj
      ((closedImmersionRightAdjoint (Spec.map τ)).obj
        ((restrictFunctor (Spec.map φ)).obj N)) :=
    closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h N x
  let r : (moduleSpecΓFunctor (R := A)).obj N ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((moduleSpecΓFunctor (R := A')).obj ((restrictFunctor (Spec.map φ)).obj N)) :=
    moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app N) ≫
      (pushforwardGlobalSectionsIso φ).hom.app ((restrictFunctor (Spec.map φ)).obj N)
  change closedImmersionRightAdjointSectionsLinearEquiv τ
      ((restrictFunctor (Spec.map φ)).obj N) y (1 : B') =
    r (closedImmersionRightAdjointSectionsLinearEquiv σ N x (1 : B))
  refine (closedImmersionRightAdjointSectionsLinearEquiv_apply_one τ
    ((restrictFunctor (Spec.map φ)).obj N) y).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => r z)
    (closedImmersionRightAdjointSectionsLinearEquiv_apply_one σ N x).symm)
  have H := congrArg (fun z => z.app ⊤ x)
    (closedImmersionRightAdjointOpenIso_unit_counit (Spec.map ψ) (Spec.map τ)
      (Spec.map σ) (Spec.map φ) h N)
  change (((restrictAdjunction (Spec.map ψ)).unit.app K).app ⊤ ≫
      ((cartesianPushforwardSquare (Spec.map ψ) (Spec.map τ) (Spec.map σ)
        (Spec.map φ) h).hom.app ((restrictFunctor (Spec.map ψ)).obj K)).app ⊤ ≫
      o.app ⊤ ≫ ((closedImmersionRightAdjunction (Spec.map τ)).counit.app
        ((restrictFunctor (Spec.map φ)).obj N)).app ⊤) x =
    (((closedImmersionRightAdjunction (Spec.map σ)).counit.app N).app ⊤ ≫
      ((restrictAdjunction (Spec.map φ)).unit.app N).app ⊤) x at H
  rw [cartesianPushforwardSquare_top] at H
  erw [Category.id_comp] at H
  exact H

/-- The original affine open comparison intertwines coinduced evaluation on
the image of every original source-ring element. -/
theorem closedImmersionRightAdjointAffineOpenSections_apply
    (N : (Spec A).Modules)
    (x : (moduleSpecΓFunctor (R := B)).obj
      ((closedImmersionRightAdjoint (Spec.map σ)).obj N)) (b : B) :
    closedImmersionRightAdjointSectionsLinearEquiv τ
        ((restrictFunctor (Spec.map φ)).obj N)
        (closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h N x) (ψ b) =
      (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app N) ≫
        (pushforwardGlobalSectionsIso φ).hom.app ((restrictFunctor (Spec.map φ)).obj N))
        (closedImmersionRightAdjointSectionsLinearEquiv σ N x b) := by
  let F := closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h N
  let N' := (restrictFunctor (Spec.map φ)).obj N
  let y : (moduleSpecΓFunctor (R := B')).obj
      ((closedImmersionRightAdjoint (Spec.map τ)).obj N') := F x
  let y' : (moduleSpecΓFunctor (R := B')).obj
      ((closedImmersionRightAdjoint (Spec.map τ)).obj N') := F (b • x)
  let r : (moduleSpecΓFunctor (R := A)).obj N →
      (moduleSpecΓFunctor (R := A')).obj N' := fun z =>
    (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app N) ≫
      (pushforwardGlobalSectionsIso φ).hom.app N') z
  have hs : y' = ψ b • y := by
    exact F.hom.map_smul b x
  change closedImmersionRightAdjointSectionsLinearEquiv τ N' y (ψ b) =
    r (closedImmersionRightAdjointSectionsLinearEquiv σ N x b)
  calc
    _ = closedImmersionRightAdjointSectionsLinearEquiv τ N' (ψ b • y) (1 : B') := by
      simpa only [one_mul] using
        (closedImmersionRightAdjointSectionsLinearEquiv_smul_apply τ N' y (ψ b) (1 : B')).symm
    _ = closedImmersionRightAdjointSectionsLinearEquiv τ N' y' (1 : B') :=
      congrArg (fun z => closedImmersionRightAdjointSectionsLinearEquiv τ N' z (1 : B')) hs.symm
    _ = r (closedImmersionRightAdjointSectionsLinearEquiv σ N (b • x) (1 : B)) :=
      closedImmersionRightAdjointAffineOpenSections_apply_one φ σ τ ψ h N (b • x)
    _ = _ := congrArg (fun z => r z) (by
      simpa only [one_mul] using
        closedImmersionRightAdjointSectionsLinearEquiv_smul_apply σ N x b (1 : B))

end AlgebraicGeometry.Scheme.Modules
