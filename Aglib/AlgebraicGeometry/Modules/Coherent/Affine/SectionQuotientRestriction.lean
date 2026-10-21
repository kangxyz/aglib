/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.SectionQuotientComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSectionsNaturality

/-! # Restriction squares for original affine quotient presentations -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)]
  (M : (Spec R).Modules) [M.IsQuasicoherent]
  (M' : (Spec S).Modules) [M'.IsQuasicoherent]
  (N : ModuleCat.{u} R) (N' : ModuleCat.{u} S)

/-- A scalar-extension square of original presentations gives the genuine sheaf
restriction square. The local comparison is the one specified by its original
affine sections, not an independently chosen descent isomorphism. -/
theorem affineQuotientFromSections_restriction
    (q : moduleSpecΓFunctor.obj M ⟶ N)
    (q' : moduleSpecΓFunctor.obj M' ⟶ N')
    (a : M.restrict (Spec.map φ) ⟶ M')
    (b : (ModuleCat.extendScalars φ.hom).obj N ≅ N')
    (h : (ModuleCat.extendScalars φ.hom).map q ≫ b.hom =
      (affineRestrictGlobalSectionsIso φ M).hom ≫ moduleSpecΓFunctor.map a ≫ q') :
    (restrictFunctor (Spec.map φ)).map (affineQuotientFromSections M N q) ≫
      (affineSheafIsoOfSectionIso ((tilde N).restrict (Spec.map φ)) N'
        ((affineRestrictGlobalSectionsIso φ (tilde N)).symm ≪≫
          (ModuleCat.extendScalars φ.hom).mapIso (tilde.toTildeΓNatIso.app N).symm ≪≫ b)).hom =
    a ≫ affineQuotientFromSections M' N' q' := by
  let E := ModuleCat.extendScalars φ.hom
  let e := (affineRestrictGlobalSectionsIso φ (tilde N)).symm ≪≫
    E.mapIso (tilde.toTildeΓNatIso.app N).symm ≪≫ b
  have hs : moduleSpecΓFunctor.map
      ((restrictFunctor (Spec.map φ)).map (affineQuotientFromSections M N q)) ≫ e.hom =
      moduleSpecΓFunctor.map a ≫ q' := by
    apply (cancel_epi (affineRestrictGlobalSectionsIso φ M).hom).mp
    rw [← Category.assoc, ← affineRestrictGlobalSectionsIso_naturality]
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← E.map_comp_assoc, affineQuotientFromSections_sections]
    exact h
  have hq := affineSheafIsoOfSectionIso_quotient
    ((tilde N).restrict (Spec.map φ)) N' e
    ((restrictFunctor (Spec.map φ)).map (affineQuotientFromSections M N q))
    (moduleSpecΓFunctor.map a ≫ q') hs
  have ha := affineQuotientFromSections_naturality
    (moduleSpecΓFunctor.map a ≫ q') q' a (𝟙 N')
    (by simp only [Category.comp_id])
  simp only [tilde.map_id, Category.comp_id] at ha
  exact hq.trans ha.symm

end AlgebraicGeometry.Scheme.Modules.Coherent
