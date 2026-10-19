/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.UnitTensor
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.PullbackComposition

/-!
# Transitivity of the cohomology base-change map

For `f : X ⟶ Spec A` and ring maps `σ : A →+* B`, `τ : B →+* C`, write `X_B = X ×_{Spec A} Spec B`
with projections `p`, `f_B`, and `(X_B)_C = X_B ×_{Spec B} Spec C` with first projection `p'`.
If the base-change map of `M` along `σ` and the base-change map of `p^* M` along `τ` are
isomorphisms in degree `n`, then so is the base-change map of `M` along `τ ∘ σ`
(`moduleCohomologyBaseChangeMap_isIso_comp`). The comparison is the isomorphism
`(X_B)_C ≅ X_C` of the pasted fibre square (`baseChangeTransIso`) with its coefficient
comparison, which is `C`-linear and bijective in every degree (`baseChangeTransCohomologyHom`).
The proof evaluates on unit pure tensors, where both sides are iterated geometric pullbacks;
those agree by `moduleCohomologyPullback_pullbackSquare_apply`
(`Cohomology/Functoriality/Modules/PullbackComposition`).

This is the step "composing the above two base change isomorphisms" of Nitsure, *Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1, proof of Thm 4.3, (C), p. 21. The iterated
base change through a flat square, in the opposite direction, is `Composite.lean`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y Z : Scheme.{u}}

section Transitivity

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B) (τ : B →+* C)

/-- `(X_B)_C`, with the composite first projection, is a fibre product of `f` and
`Spec (τ ∘ σ)`. -/
theorem isPullback_baseChangeTrans :
    IsPullback
      (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
          (Spec.map (CommRingCat.ofHom τ)) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom σ)))
      (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom τ)))
      f (Spec.map (CommRingCat.ofHom (τ.comp σ))) := by
  have h := (IsPullback.of_hasPullback (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
    (Spec.map (CommRingCat.ofHom τ))).paste_horiz
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom σ)))
  have e : Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom σ) =
      Spec.map (CommRingCat.ofHom (τ.comp σ)) := by
    rw [← Spec.map_comp]
    rfl
  rwa [e] at h

/-- The comparison `(X_B)_C ≅ X_C` of iterated and direct base change. -/
def baseChangeTransIso :
    pullback (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) (Spec.map (CommRingCat.ofHom τ)) ≅
      pullback f (Spec.map (CommRingCat.ofHom (τ.comp σ))) :=
  (isPullback_baseChangeTrans f σ τ).isoPullback

@[reassoc]
theorem baseChangeTransIso_hom_fst :
    (baseChangeTransIso f σ τ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (τ.comp σ))) =
      pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
          (Spec.map (CommRingCat.ofHom τ)) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom σ)) :=
  (isPullback_baseChangeTrans f σ τ).isoPullback_hom_fst

@[reassoc]
theorem baseChangeTransIso_hom_snd :
    (baseChangeTransIso f σ τ).hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (τ.comp σ))) =
      pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom τ)) :=
  (isPullback_baseChangeTrans f σ τ).isoPullback_hom_snd

/-- The structural maps agree: `j ≫ snd_C = snd'`, read on global functions of `Spec C`. -/
theorem baseChangeTransIso_appTop_comp :
    (baseChangeTransIso f σ τ).hom.appTop.hom.comp
        ((pullback.snd f (Spec.map (CommRingCat.ofHom (τ.comp σ)))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom) =
      ((pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
          (Spec.map (CommRingCat.ofHom τ))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom).comp (RingHom.id C) := by
  rw [← baseChangeTransIso_hom_snd f σ τ, Scheme.Hom.comp_appTop]
  rfl

/-- The transport `H^q(X_C, M_C) ⟶ H^q((X_B)_C, (M_B)_C)` as a morphism of `C`-modules: the
geometric map along `baseChangeTransIso` with the coefficient arrow
`pullbackSquareCoefficientArrow`. -/
def baseChangeTransCohomologyHom (M : X.Modules) (q : ℕ) :
    letI := moduleCohomologyModuleOfHom (pullback f (Spec.map (CommRingCat.ofHom (τ.comp σ))))
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (τ.comp σ)))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (τ.comp σ))))).obj M)
      q
    letI := moduleCohomologyModuleOfHom
      (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) (Spec.map (CommRingCat.ofHom τ)))
      ((pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
          (Spec.map (CommRingCat.ofHom τ))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
          (Spec.map (CommRingCat.ofHom τ)))).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)) q
    ModuleCat.of C (Sheaf.H.{u + 1} (moduleAddSheaf
        (pullback f (Spec.map (CommRingCat.ofHom (τ.comp σ))))
        ((Scheme.Modules.pullback
          (pullback.fst f (Spec.map (CommRingCat.ofHom (τ.comp σ))))).obj M)) q) ⟶
      ModuleCat.of C (Sheaf.H.{u + 1} (moduleAddSheaf
        (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
          (Spec.map (CommRingCat.ofHom τ)))
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
          (Spec.map (CommRingCat.ofHom τ)))).obj
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)))
          q) :=
  letI := moduleCohomologyModuleOfHom (pullback f (Spec.map (CommRingCat.ofHom (τ.comp σ))))
    ((pullback.snd f (Spec.map (CommRingCat.ofHom (τ.comp σ)))).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (τ.comp σ))))).obj M) q
  letI := moduleCohomologyModuleOfHom
    (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) (Spec.map (CommRingCat.ofHom τ)))
    ((pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom τ))).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
    ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom τ)))).obj
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)) q
  ModuleCat.ofHom
    { toFun := moduleCohomologyMapAlong (baseChangeTransIso f σ τ).hom
        (pullbackSquareCoefficientArrow (baseChangeTransIso_hom_fst f σ τ) M) q
      map_add' := map_add _
      map_smul' := fun c y =>
        (moduleCohomologyRestrictionMap (baseChangeTransIso f σ τ).hom (RingHom.id C) _ _
          (baseChangeTransIso_appTop_comp f σ τ)
          (pullbackSquareCoefficientArrow (baseChangeTransIso_hom_fst f σ τ) M)
          q).hom.map_smul c y }

theorem baseChangeTransCohomologyHom_apply (M : X.Modules) (q : ℕ)
    (y : Sheaf.H.{u + 1} (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom (τ.comp σ))))
      ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (τ.comp σ))))).obj M)) q) :
    baseChangeTransCohomologyHom f σ τ M q y =
      moduleCohomologyMapAlong (baseChangeTransIso f σ τ).hom
        (pullbackSquareCoefficientArrow (baseChangeTransIso_hom_fst f σ τ) M) q y :=
  rfl

/-- The transport is bijective in every degree. -/
theorem baseChangeTransCohomologyHom_bijective (M : X.Modules) (q : ℕ) :
    Function.Bijective (moduleCohomologyMapAlong (baseChangeTransIso f σ τ).hom
      (pullbackSquareCoefficientArrow (baseChangeTransIso_hom_fst f σ τ) M) q) :=
  moduleCohomologyMapAlong_bijective _ _ q

instance (M : X.Modules) (q : ℕ) : IsIso (baseChangeTransCohomologyHom f σ τ M q) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (baseChangeTransCohomologyHom_bijective f σ τ M q)

end Transitivity

section TransitivityIso

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B) (τ : B →+* C)

-- Pure tensors in `(extendScalars f).obj M` are typed through `restrictScalars`; rewriting with
-- them needs the module-category presentation, which is not reducible.
set_option backward.isDefEq.respectTransparency false in
/-- **Transitivity of cohomology base change**: for `f : X ⟶ Spec A` and ring maps
`σ : A →+* B`, `τ : B →+* C`, if the degree-`n` base-change maps of `M` along `σ` and of its
pullback `M_B` on `X_B = X ×_{Spec A} Spec B` along `τ` are isomorphisms, so is the degree-`n`
base-change map of `M` along `τ ∘ σ`. -/
theorem moduleCohomologyBaseChangeMap_isIso_comp (M : X.Modules) (n : ℕ)
    (h₁ : IsIso (moduleCohomologyBaseChangeMap f σ M n))
    (h₂ : IsIso (moduleCohomologyBaseChangeMap (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) τ
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M) n)) :
    IsIso (moduleCohomologyBaseChangeMap f (τ.comp σ) M n) := by
  have hK : moduleCohomologyBaseChangeMap f (τ.comp σ) M n ≫
        baseChangeTransCohomologyHom f σ τ M n =
      (ModuleCat.extendScalarsComp.{u, u + 1} σ τ).hom.app _ ≫
        (ModuleCat.extendScalars τ).map (moduleCohomologyBaseChangeMap f σ M n) ≫
          moduleCohomologyBaseChangeMap (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) τ
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)
            n := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rw [ModuleCat.extendScalarsComp_hom_app_comp_map_comp_one_tmul _ _ _ _
      (fun m => moduleCohomologyPullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) M n m)
      (moduleCohomologyBaseChangeMap_one_tmul f σ M n)
      (fun y => moduleCohomologyPullback
        (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
          (Spec.map (CommRingCat.ofHom τ))) _ n y)
      (moduleCohomologyBaseChangeMap_one_tmul _ τ _ n),
      ConcreteCategory.comp_apply, baseChangeTransCohomologyHom_apply,
      moduleCohomologyBaseChangeMap_one_tmul f (τ.comp σ) M n x]
    exact moduleCohomologyMapAlong_pullbackSquareCoefficientArrow
      (baseChangeTransIso_hom_fst f σ τ) M n x
  have hc : IsIso (moduleCohomologyBaseChangeMap f (τ.comp σ) M n ≫
      baseChangeTransCohomologyHom f σ τ M n) := by
    rw [hK]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance hc

end TransitivityIso

end AlgebraicGeometry.Scheme.Cohomology
