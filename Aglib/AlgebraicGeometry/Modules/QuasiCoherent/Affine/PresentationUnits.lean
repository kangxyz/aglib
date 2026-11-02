/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PushforwardSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Sections

/-! # Detecting affine pullback maps on original presentation units

The original tilde presentation and geometric adjunction give a family of
sections that detects maps out of the actual pullback. The target is arbitrary;
no quasicoherence assumption or new adjunction construction is needed.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Maps out of an originally presented affine pullback agree if they agree on
all original presentation-unit sections. -/
theorem affinePresentation_unit_ext
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {P : ModuleCat.{u} R}
    {E : (Spec R).Modules} {F : (Spec S).Modules}
    (e : (tilde.functor R).obj P ≅ E)
    (a b : (pullback (Spec.map φ)).obj E ⟶ F)
    (h : ∀ x : P,
      a.app ⊤
          (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app E).app ⊤
            (((tilde.adjunction (R := R)).unit.app P ≫
              moduleSpecΓFunctor.map e.hom) x)) =
        b.app ⊤
          (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app E).app ⊤
            (((tilde.adjunction (R := R)).unit.app P ≫
              moduleSpecΓFunctor.map e.hom) x))) :
    a = b := by
  apply (cancel_epi ((pullback (Spec.map φ)).map e.hom)).mp
  apply ((pullbackPushforwardAdjunction (Spec.map φ)).homEquiv
    ((tilde.functor R).obj P) F).injective
  simp only [Adjunction.homEquiv_naturality_left]
  apply ((tilde.adjunction (R := R)).homEquiv P
    ((pushforward (Spec.map φ)).obj F)).injective
  apply (cancel_mono ((pushforwardGlobalSectionsIso φ).hom.app F)).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    (moduleSpecΓFunctor.map
        (e.hom ≫ (pullbackPushforwardAdjunction (Spec.map φ)).unit.app E ≫
          (pushforward (Spec.map φ)).map a) ≫
        (pushforwardGlobalSectionsIso φ).hom.app F)
          ((tilde.adjunction (R := R)).unit.app P x) =
      (moduleSpecΓFunctor.map
        (e.hom ≫ (pullbackPushforwardAdjunction (Spec.map φ)).unit.app E ≫
          (pushforward (Spec.map φ)).map b) ≫
        (pushforwardGlobalSectionsIso φ).hom.app F)
          ((tilde.adjunction (R := R)).unit.app P x)
  rw [moduleSpecΓFunctor_map_pushforwardGlobalSectionsIso_apply φ
    (e.hom ≫ (pullbackPushforwardAdjunction (Spec.map φ)).unit.app E ≫
      (pushforward (Spec.map φ)).map a)
    ((tilde.adjunction (R := R)).unit.app P x)]
  rw [moduleSpecΓFunctor_map_pushforwardGlobalSectionsIso_apply φ
    (e.hom ≫ (pullbackPushforwardAdjunction (Spec.map φ)).unit.app E ≫
      (pushforward (Spec.map φ)).map b)
    ((tilde.adjunction (R := R)).unit.app P x)]
  change
    a.app ⊤
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app E).app ⊤
          (((tilde.adjunction (R := R)).unit.app P ≫
            moduleSpecΓFunctor.map e.hom) x)) =
      b.app ⊤
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app E).app ⊤
          (((tilde.adjunction (R := R)).unit.app P ≫
            moduleSpecΓFunctor.map e.hom) x))
  exact h x

end AlgebraicGeometry.Scheme.Modules
