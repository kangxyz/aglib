/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Rees.AffineImage
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms

/-! # Actual image sections on affine opens

The image inclusion has the same sectionwise range as the original map on
any affine open, with the original structure-sheaf module action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction to an affine open immersion preserves the section epimorphism
of a short exact sequence with quasicoherent first term. -/
theorem affineRestriction_shortExact_surjective {X : Scheme.{u}}
    {R : CommRingCat.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map
      ((restrictFunctor j).map S.g)) := by
  let : (S.map (restrictFunctor j)).X₁.IsQuasicoherent := by
    change ((restrictFunctor j).obj S.X₁).IsQuasicoherent
    exact isQuasicoherent_restrictFunctor j S.X₁
  have hT : (S.map (restrictFunctor j)).ShortExact := hS.map_of_exact (restrictFunctor j)
  have hE : Epi ((moduleSpecΓFunctor (R := R)).map ((restrictFunctor j).map S.g)) :=
    AffineCech.epi_globalSections_of_quasicoherent_kernel (R := R)
      (S := S.map (restrictFunctor j)) hT
  exact (ModuleCat.epi_iff_surjective _).mp hE

/-- An epimorphism with quasicoherent kernel is surjective in affine open coordinates. -/
theorem affineRestriction_epi_surjective {X : Scheme.{u}}
    {R : CommRingCat.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (π : M ⟶ N) [Epi π] [(kernel π).IsQuasicoherent] :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map
      ((restrictFunctor j).map π)) :=
  affineRestriction_shortExact_surjective (X := X) (R := R) j
    (S := ShortComplex.mk (kernel.ι π) π (kernel.condition π))
    (show (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact from
      { exact := ShortComplex.exact_kernel π })

/-- Surjectivity on affine-chart coordinates is surjectivity of original sections. -/
theorem affineOpenSections_surjective_of_chart {X : Scheme.{u}} (U : X.affineOpens)
    {M N : X.Modules} (π : M ⟶ N)
    (hs : Function.Surjective ((moduleSpecΓFunctor (R := Γ(X, U))).map
      ((restrictFunctor U.property.fromSpec).map π))) :
    Function.Surjective (π.app U.val) := by
  intro n
  obtain ⟨m, hm⟩ := hs ((affineChartΓIso U N).inv n)
  refine ⟨(affineChartΓIso U M).hom m, ?_⟩
  have h := congrArg (fun k => k m) (affineChartΓIso_naturality U π)
  change (affineChartΓIso U N).hom
      (((moduleSpecΓFunctor (R := Γ(X, U))).map
        ((restrictFunctor U.property.fromSpec).map π)) m) =
    (π.app U.val) ((affineChartΓIso U M).hom m) at h
  exact h.symm.trans ((congrArg (affineChartΓIso U N).hom hm).trans
    ((affineChartΓIso U N).toLinearEquiv.apply_symm_apply n))

/-- On an affine open, sections preserve an epimorphism with quasicoherent kernel. -/
theorem affineOpenSections_epi_surjective {X : Scheme.{u}} (U : X.affineOpens)
    {M N : X.Modules} (π : M ⟶ N) [Epi π] [(kernel π).IsQuasicoherent] :
    Function.Surjective (π.app U.val) := by
  apply affineOpenSections_surjective_of_chart U π
  exact affineRestriction_epi_surjective (X := X) (R := Γ(X, U)) U.property.fromSpec π

/-- Actual sections of the source surject onto actual image sections on an affine open. -/
theorem affineOpenSections_factorThruImage_surjective {X : Scheme.{u}}
    (U : X.affineOpens) {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) : Function.Surjective ((Abelian.factorThruImage φ).app U.val) := by
  let := QuasiCoherent.quasicoherent_cokernel φ
  let := QuasiCoherent.quasicoherent_kernel (cokernel.π φ)
  let := QuasiCoherent.quasicoherent_kernel (Abelian.factorThruImage φ)
  exact affineOpenSections_epi_surjective U (Abelian.factorThruImage φ)

/-- Affine-open image normalization retains the actual original section map. -/
theorem affineOpenSections_image_range {X : Scheme.{u}} (U : X.affineOpens)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    LinearMap.range ((Abelian.image.ι φ).val.app (op U.val)).hom =
      LinearMap.range (φ.val.app (op U.val)).hom := by
  ext n
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨m, rfl⟩ := affineOpenSections_factorThruImage_surjective U φ x
    refine ⟨m, ?_⟩
    exact (congrArg (fun k => (k.app U.val) m) (Abelian.image.fac φ)).symm
  · rintro ⟨m, rfl⟩
    refine ⟨(Abelian.factorThruImage φ).app U.val m, ?_⟩
    exact congrArg (fun k => (k.app U.val) m) (Abelian.image.fac φ)

/-- The same range statement for Mathlib's chosen categorical image. -/
theorem affineOpenSections_categoricalImage_range {X : Scheme.{u}} (U : X.affineOpens)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    LinearMap.range ((image.ι φ).val.app (op U.val)).hom =
      LinearMap.range (φ.val.app (op U.val)).hom := by
  rw [← affineOpenSections_image_range U φ]
  ext n
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(Abelian.imageIsoImage φ).inv.app U.val x, ?_⟩
    have h : (Abelian.imageIsoImage φ).hom ≫ image.ι φ = Abelian.image.ι φ :=
      Abelian.imageIsoImage_hom_comp_image_ι φ
    have he : (Abelian.imageIsoImage φ).inv ≫ Abelian.image.ι φ = image.ι φ := by
      calc
        (Abelian.imageIsoImage φ).inv ≫ Abelian.image.ι φ =
            (Abelian.imageIsoImage φ).inv ≫ ((Abelian.imageIsoImage φ).hom ≫ image.ι φ) :=
          congrArg (fun k => (Abelian.imageIsoImage φ).inv ≫ k) h.symm
        _ = image.ι φ := (Abelian.imageIsoImage φ).inv_hom_id_assoc _
    exact congrArg (fun k => (k.app U.val) x) he
  · rintro ⟨x, rfl⟩
    refine ⟨(Abelian.imageIsoImage φ).hom.app U.val x, ?_⟩
    exact congrArg (fun k => (k.app U.val) x)
      (Abelian.imageIsoImage_hom_comp_image_ι φ)

end AlgebraicGeometry.Scheme.Modules
