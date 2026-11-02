/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineSheaf
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PresentationUnits

/-! # Unit sections of the original presented affine sheaf map

The original source presentation cancels against its actual inverse. The
installed tilde comparison then carries its geometric unit to the original
scalar unit, for any target presentation arrow and any target sheaf.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

/-- The original affine map evaluates on presentation-unit sections by the
original scalar map. The target presentation need not be invertible. -/
theorem affineMapOfTilde_unit_apply
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {P : ModuleCat.{u} R} {Q : ModuleCat.{u} S}
    {E : (Spec R).Modules} {F : (Spec S).Modules}
    (e : (tilde.functor R).obj P ≅ E)
    (c : (tilde.functor S).obj Q ⟶ F)
    (t : (ModuleCat.extendScalars φ.hom).obj P ⟶ Q)
    (x : P) :
    (affineMapOfTilde φ e c t).app ⊤
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app E).app ⊤
          (((tilde.adjunction (R := R)).unit.app P ≫
            moduleSpecΓFunctor.map e.hom) x)) =
      ((tilde.adjunction (R := S)).unit.app Q ≫
        moduleSpecΓFunctor.map c)
          (t ((1 : S) ⊗ₜ[R,φ.hom] x)) := by
  have he :
      (pullback (Spec.map φ)).map e.hom ≫ affineMapOfTilde φ e c t =
        (tildePullbackIso φ).hom.app P ≫ (tilde.functor S).map t ≫ c := by
    change (pullback (Spec.map φ)).map e.hom ≫
      (pullback (Spec.map φ)).map e.inv ≫ _ = _
    rw [← Functor.map_comp_assoc, e.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hn := congrArg
    (fun q => q.app ⊤ ((tilde.adjunction (R := R)).unit.app P x))
    ((pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality e.hom)
  change
    ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app E).app ⊤
        (e.hom.app ⊤ ((tilde.adjunction (R := R)).unit.app P x)) =
      ((pullback (Spec.map φ)).map e.hom).app ⊤
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          ((tilde.functor R).obj P)).app ⊤
            ((tilde.adjunction (R := R)).unit.app P x)) at hn
  have hu := congrArg (fun q => q x) (tildePullbackIso_globalSections_unit φ P)
  change
    moduleSpecΓFunctor.map ((tildePullbackIso φ).hom.app P)
        ((moduleSpecΓFunctor.map
            ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
              ((tilde.functor R).obj P)) ≫
          (pushforwardGlobalSectionsIso φ).hom.app
            ((pullback (Spec.map φ)).obj ((tilde.functor R).obj P)))
              ((tilde.adjunction (R := R)).unit.app P x)) =
      (tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj P)
        ((1 : S) ⊗ₜ[R,φ.hom] x) at hu
  rw [moduleSpecΓFunctor_map_pushforwardGlobalSectionsIso_apply] at hu
  change
    ((tildePullbackIso φ).hom.app P).app ⊤
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          ((tilde.functor R).obj P)).app ⊤
            ((tilde.adjunction (R := R)).unit.app P x)) =
      (tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj P)
        ((1 : S) ⊗ₜ[R,φ.hom] x) at hu
  have ht := congrArg (fun q => q ((1 : S) ⊗ₜ[R,φ.hom] x))
    ((tilde.adjunction (R := S)).unit.naturality t).symm
  change
    ((tilde.functor S).map t).app ⊤
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj P)
          ((1 : S) ⊗ₜ[R,φ.hom] x)) =
      (tilde.adjunction (R := S)).unit.app Q (t ((1 : S) ⊗ₜ[R,φ.hom] x)) at ht
  change
    (affineMapOfTilde φ e c t).app ⊤
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app E).app ⊤
          (e.hom.app ⊤ ((tilde.adjunction (R := R)).unit.app P x))) =
      c.app ⊤ ((tilde.adjunction (R := S)).unit.app Q
        (t ((1 : S) ⊗ₜ[R,φ.hom] x)))
  rw [hn]
  have he' := congrArg
    (fun q => q.app ⊤
      (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
        ((tilde.functor R).obj P)).app ⊤
          ((tilde.adjunction (R := R)).unit.app P x))) he
  change
    (affineMapOfTilde φ e c t).app ⊤
        (((pullback (Spec.map φ)).map e.hom).app ⊤
          (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            ((tilde.functor R).obj P)).app ⊤
              ((tilde.adjunction (R := R)).unit.app P x))) =
      c.app ⊤
        (((tilde.functor S).map t).app ⊤
          (((tildePullbackIso φ).hom.app P).app ⊤
            (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
              ((tilde.functor R).obj P)).app ⊤
                ((tilde.adjunction (R := R)).unit.app P x)))) at he'
  rw [he', hu, ht]

end AlgebraicGeometry.Scheme.Modules.Nonflat
