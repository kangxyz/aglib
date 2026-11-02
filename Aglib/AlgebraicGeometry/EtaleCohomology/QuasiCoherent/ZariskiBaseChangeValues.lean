/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleCohomologyPullback
public import Aglib.CategoryTheory.Adjunction.PresheafPullbackNaturality

/-! # Original values of the Zariski--étale image square

The whole original counit calculation is specialized to the native preimage-open
comparison. The resulting map is literal geometric restriction on that open.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual direct-image comparison evaluates by the inverse original
preimage-open isomorphism, with no change to the coefficient sheaf. -/
theorem zariskiRestrictionDirectImageIso_hom_app
    (A : AbelianSheaf.{u, u + 1} X) (U : Y.Opens) :
    ((zariskiRestrictionDirectImageIso f).hom.app A).hom.app (op U) =
      A.obj.map ((opensToEtaleBaseChangeObjIso f U).inv).op := by
  change (𝟙 _) ≫ A.obj.map ((opensToEtaleBaseChangeObjIso f U).inv).op ≫ (𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

/-- The inverse preimage-open chart, transposed by the native over adjunction,
is the actual restricted scheme morphism. -/
theorem preimageOpen_counit (U : Y.Opens) :
    (Over.map f).map ((Scheme.Etale.forget X).map
        (opensToEtaleBaseChangeObjIso f U).inv) ≫
      (Over.mapPullbackAdj f).counit.app ((Scheme.Etale.forget Y).obj
        ((opensToEtale Y).obj U)) =
      Over.homMk (f ∣_ U) (morphismRestrict_ι f U) := by
  apply Over.OverMorphism.ext
  change (isPullback_morphismRestrict f U).isoPullback.hom ≫
    CategoryTheory.Limits.pullback.fst U.ι f = f ∣_ U
  exact (isPullback_morphismRestrict f U).isoPullback_hom_fst

/-- The whole section-unit/image-square composite is original restriction along
the restricted morphism, followed by the same module composition comparison. -/
theorem additiveCoefficientPullbackUnit_preimage
    (M : Y.Modules) [M.IsQuasicoherent] (U : Y.Opens) :
    (additiveCoefficientPullbackUnit f M).hom.app (op ((opensToEtale Y).obj U)) ≫
      (additiveCoefficient X ((pullback f).obj M)).obj.map
        ((opensToEtaleBaseChangeObjIso f U).inv).op =
      (additiveSectionsPresheaf Y M).map
        (Over.homMk (f ∣_ U) (morphismRestrict_ι f U)).op ≫
      (additiveBaseRestrictionIso f M).hom.app
        (op ((Scheme.Etale.forget X).obj ((opensToEtale X).obj (f ⁻¹ᵁ U)))) := by
  have h := Adjunction.presheafPullbackUnit_app_comp (Over.mapPullbackAdj f)
    (additiveSectionsPresheaf Y M) (additiveSectionsPresheaf X ((pullback f).obj M))
    (additiveBaseRestrictionIso f M).hom
    ((Scheme.Etale.forget X).map (opensToEtaleBaseChangeObjIso f U).inv)
  have hk := congrArg
    (fun k : (Over.map f).obj ((Scheme.Etale.forget X).obj
        ((opensToEtale X).obj (f ⁻¹ᵁ U))) ⟶
        ((Scheme.Etale.forget Y).obj ((opensToEtale Y).obj U)) =>
      (additiveSectionsPresheaf Y M).map k.op)
    (preimageOpen_counit f U)
  calc
    _ = (additiveSectionsPresheaf Y M).map
        ((Over.map f).map ((Scheme.Etale.forget X).map
          (opensToEtaleBaseChangeObjIso f U).inv) ≫
        (Over.mapPullbackAdj f).counit.app
          ((Scheme.Etale.forget Y).obj ((opensToEtale Y).obj U))).op ≫
      (additiveBaseRestrictionIso f M).hom.app
        (op ((Scheme.Etale.forget X).obj ((opensToEtale X).obj (f ⁻¹ᵁ U)))) := h
    _ = _ := congrArg (fun k => k ≫ (additiveBaseRestrictionIso f M).hom.app
      (op ((Scheme.Etale.forget X).obj ((opensToEtale X).obj (f ⁻¹ᵁ U))))) hk

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
