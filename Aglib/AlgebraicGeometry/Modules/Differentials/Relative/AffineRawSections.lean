/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Differentials.ExteriorBaseChange
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineRawCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineRawPullback
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.BaseForms
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient


/-!
# Original affine raw pullback on sections and images

Actual affine section comparisons identify the original raw pullback arrow
and its image with the original algebraic raw map. These are comparisons of
the original arrows, not an image-bound assumption.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open CommRingCat.KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Modules.Differentials

private theorem affine_section_square {C D : Type*} [Category C] [Category D]
    (F : D ⥤ C) (G : C ⥤ D) (η : 𝟭 C ≅ G ⋙ F)
    {X Y : D} {M N : C} (eX : X ≅ G.obj M) (eY : Y ≅ G.obj N)
    (f : X ⟶ Y) (g : M ⟶ N) (h : f ≫ eY.hom = eX.hom ≫ G.map g) :
    F.map f ≫ (F.map eY.hom ≫ η.inv.app N) =
      (F.map eX.hom ≫ η.inv.app M) ≫ g := by
  calc
    _ = F.map (f ≫ eY.hom) ≫ η.inv.app N := by
      rw [F.map_comp]
      simp only [Category.assoc]
    _ = F.map (eX.hom ≫ G.map g) ≫ η.inv.app N :=
      congrArg (fun q => F.map q ≫ η.inv.app N) h
    _ = F.map eX.hom ≫ ((G ⋙ F).map g ≫ η.inv.app N) := by
      rw [F.map_comp]
      simp only [Functor.comp_map, Category.assoc]
    _ = F.map eX.hom ≫ (η.inv.app M ≫ g) :=
      congrArg (fun q => F.map eX.hom ≫ q) (η.inv.naturality g)
    _ = _ := (Category.assoc _ _ _).symm

variable {Λ A B : CommRingCat.{u}} (α : Λ ⟶ A) (σ : A ⟶ B) (n : ℕ)

/-- The actual source comparison before taking affine global sections. -/
def rawPullbackAffineSourceIso :
    (pullback (Spec.map σ)).obj
      (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n) ≅
    tilde ((ModuleCat.extendScalars σ.hom).obj
      (ModuleCat.of A (⋀[A]^n (CommRingCat.KaehlerDifferential α)))) :=
  (pullback (Spec.map σ)).mapIso (baseRawFormsIso α n) ≪≫
    (tildePullbackIso σ).app (ModuleCat.of A (⋀[A]^n (CommRingCat.KaehlerDifferential α)))

/-- Original affine source sections, in their actual scalar-extended raw module. -/
def rawPullbackSourceSectionsEquiv :
    moduleSpecΓFunctor.obj ((pullback (Spec.map σ)).obj
      (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n)) ≃ₗ[B]
    (ModuleCat.extendScalars σ.hom).obj
      (ModuleCat.of A (⋀[A]^n (CommRingCat.KaehlerDifferential α))) :=
  ((moduleSpecΓFunctor.mapIso (rawPullbackAffineSourceIso α σ n)) ≪≫
    (tilde.toTildeΓNatIso.app _).symm).toLinearEquiv

/-- Original affine target sections, in the same actual raw exterior module. -/
def rawPullbackTargetSectionsEquiv :
    moduleSpecΓFunctor.obj (moduleExteriorPower (Spec B)
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n) ≃ₗ[B]
    ModuleCat.of B (⋀[B]^n (CommRingCat.KaehlerDifferential (α ≫ σ))) :=
  ((moduleSpecΓFunctor.mapIso (targetRawFormsAffineIso α σ n)) ≪≫
    (tilde.toTildeΓNatIso.app _).symm).toLinearEquiv

/-- Original affine section comparisons preserve the whole raw pullback arrow. -/
theorem rawPullbackSections_apply
    (z : moduleSpecΓFunctor.obj ((pullback (Spec.map σ)).obj
      (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n))) :
    rawPullbackTargetSectionsEquiv α σ n
      (moduleSpecΓFunctor.map (rawFormsPullback (Spec.map α) (Spec.map σ) n) z) =
    affineRawLinearMap α σ n (rawPullbackSourceSectionsEquiv α σ n z) := by
  exact ConcreteCategory.congr_hom
    (affine_section_square moduleSpecΓFunctor (tilde.functor B) tilde.toTildeΓNatIso
      (rawPullbackAffineSourceIso α σ n) (targetRawFormsAffineIso α σ n)
      (rawFormsPullback (Spec.map α) (Spec.map σ) n) (affineRawLinearMap α σ n)
      (rawFormsPullback_affine α σ n)) z

/-- Membership in the actual geometric raw image is equivalent to membership
in the original algebraic raw image, not in a substituted determinant image. -/
theorem rawPullbackSections_mem_range_iff
    (z : moduleSpecΓFunctor.obj (moduleExteriorPower (Spec B)
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n)) :
    rawPullbackTargetSectionsEquiv α σ n z ∈ LinearMap.range (affineRawLinearMap α σ n).hom ↔
    z ∈ LinearMap.range
      (moduleSpecΓFunctor.map (rawFormsPullback (Spec.map α) (Spec.map σ) n)).hom := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(rawPullbackSourceSectionsEquiv α σ n).symm v, ?_⟩
    apply (rawPullbackTargetSectionsEquiv α σ n).injective
    exact (rawPullbackSections_apply α σ n _).trans
      ((congrArg (affineRawLinearMap α σ n)
        ((rawPullbackSourceSectionsEquiv α σ n).apply_symm_apply v)).trans hv)
  · rintro ⟨v, rfl⟩
    exact ⟨rawPullbackSourceSectionsEquiv α σ n v, (rawPullbackSections_apply α σ n v).symm⟩

end AlgebraicGeometry.Scheme.Modules.Differentials
