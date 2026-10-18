/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.RightAdjoint.Affine
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.RightAdjoint.Restriction
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.RightAdjoint.Restriction.Counit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction

/-!
# Original closed-adjoint affine sections and source isomorphisms

The affine coinduction comparison is normalized by the actual geometric
counit. This normalization determines its source-ring change by evaluation
at one and the native coinduced scalar action, for arbitrary coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem tildeUnit_pushforwardComparison_inv
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (N : ModuleCat S) :
    (tilde.adjunction (R := R)).unit.app ((ModuleCat.restrictScalars φ.hom).obj N) ≫
        moduleSpecΓFunctor.map ((tildePushforwardIso φ).inv.app N) =
      (ModuleCat.restrictScalars φ.hom).map ((tilde.adjunction (R := S)).unit.app N) ≫
        (pushforwardGlobalSectionsIso φ).inv.app (tilde N) := by
  apply (cancel_mono (moduleSpecΓFunctor.map ((tildePushforwardIso φ).hom.app N))).mp
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  erw [(moduleSpecΓFunctor (R := R)).map_id, Category.comp_id,
    tildePushforwardIso_globalSections_unit]
  simp only [← Category.assoc]
  change _ = (ModuleCat.restrictScalars φ.hom).map
    ((tilde.adjunction (R := S)).unit.app N) ≫
      (ModuleCat.restrictScalars φ.hom).map (tilde.toTildeΓNatIso.inv.app N) ≫ _
  rw [← (ModuleCat.restrictScalars φ.hom).map_comp_assoc]
  change _ = (ModuleCat.restrictScalars φ.hom).map
    (tilde.toTildeΓNatIso.hom.app N ≫ tilde.toTildeΓNatIso.inv.app N) ≫ _
  rw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsClosedImmersion (Spec.map φ)]

/-- Evaluation at one of the original affine coinduction comparison is the
original geometric closed-adjunction counit on affine sections. -/
theorem closedImmersionRightAdjointAffineIso_counit_sections
    (N : (Spec R).Modules) :
    (ModuleCat.restrictScalars φ.hom).map
        ((closedImmersionRightAdjointAffineIso φ).hom.app N) ≫
      (ModuleCat.restrictCoextendScalarsAdj φ.hom).counit.app
        ((moduleSpecΓFunctor (R := R)).obj N) =
    (pushforwardGlobalSectionsIso φ).inv.app
        ((closedImmersionRightAdjoint (Spec.map φ)).obj N) ≫
      moduleSpecΓFunctor.map ((closedImmersionRightAdjunction (Spec.map φ)).counit.app N) := by
  let K := (moduleSpecΓFunctor (R := S)).obj
    ((closedImmersionRightAdjoint (Spec.map φ)).obj N)
  let t := tilde.adjunction (R := R)
  let c := ModuleCat.restrictCoextendScalarsAdj φ.hom
  let a := closedImmersionRightAdjointAffineAdjunction φ
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app a (c.comp t) N
  have ht := congrArg (t.homEquiv ((ModuleCat.restrictScalars φ.hom).obj K) N) h
  change (t.homEquiv _ N)
      (((c.comp t).homEquiv K N).symm ((closedImmersionRightAdjointAffineIso φ).hom.app N)) =
    (t.homEquiv _ N) (a.counit.app N) at ht
  rw [Adjunction.comp_homEquiv] at ht
  change (t.homEquiv ((ModuleCat.restrictScalars φ.hom).obj K) N)
    ((t.homEquiv ((ModuleCat.restrictScalars φ.hom).obj K) N).symm
      ((c.homEquiv K ((moduleSpecΓFunctor (R := R)).obj N)).symm
        ((closedImmersionRightAdjointAffineIso φ).hom.app N))) =
      (t.homEquiv ((ModuleCat.restrictScalars φ.hom).obj K) N) (a.counit.app N) at ht
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_counit] at ht
  rw [ht]
  rw [Adjunction.homEquiv_unit]
  change t.unit.app ((ModuleCat.restrictScalars φ.hom).obj K) ≫
    moduleSpecΓFunctor.map
      ((tildePushforwardIso φ).inv.app K ≫
        (pushforward (Spec.map φ)).map
          ((tilde.adjunction (R := S)).counit.app
            ((closedImmersionRightAdjoint (Spec.map φ)).obj N)) ≫
        (closedImmersionRightAdjunction (Spec.map φ)).counit.app N) = _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ← Category.assoc,
    tildeUnit_pushforwardComparison_inv]
  have hn := (pushforwardGlobalSectionsIso φ).inv.naturality
    ((tilde.adjunction (R := S)).counit.app
      ((closedImmersionRightAdjoint (Spec.map φ)).obj N))
  dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map] at hn ⊢
  erw [Category.assoc]
  erw [← reassoc_of% hn]
  rw [← (ModuleCat.restrictScalars φ.hom).map_comp_assoc,
    (tilde.adjunction (R := S)).right_triangle_components]
  exact (congrArg (fun z => z ≫
      (pushforwardGlobalSectionsIso φ).inv.app
        ((closedImmersionRightAdjoint (Spec.map φ)).obj N) ≫
      moduleSpecΓFunctor.map ((closedImmersionRightAdjunction (Spec.map φ)).counit.app N))
    ((ModuleCat.restrictScalars φ.hom).map_id K)).trans (Category.id_comp _)

/-- Evaluation at one is the original geometric counit evaluated on the total
affine open. -/
theorem closedImmersionRightAdjointSectionsLinearEquiv_apply_one
    (N : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := S)).obj
      ((closedImmersionRightAdjoint (Spec.map φ)).obj N)) :
    closedImmersionRightAdjointSectionsLinearEquiv φ N m (1 : S) =
      ((closedImmersionRightAdjunction (Spec.map φ)).counit.app N).app ⊤ m := by
  exact congrArg (fun z => z m) (closedImmersionRightAdjointAffineIso_counit_sections φ N)

section SourceIsomorphism

variable {A B C : CommRingCat.{u}} (σ : A ⟶ B) (τ : A ⟶ C) (e : C ≃+* B)
  [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)]
  (h : IsPullback (Spec.map e.toCommRingCatIso.inv) (Spec.map τ)
    (Spec.map σ) (𝟙 (Spec A)))

/-- The actual source-isomorphism arrow on closed-adjoint affine sections,
including the original open restriction unit. -/
def closedImmersionRightAdjointSourceIsoSections (N : (Spec A).Modules) :
    (moduleSpecΓFunctor (R := B)).obj
        ((closedImmersionRightAdjoint (Spec.map σ)).obj N) ⟶
      (ModuleCat.restrictScalars e.toCommRingCatIso.inv.hom).obj
        ((moduleSpecΓFunctor (R := C)).obj
          ((closedImmersionRightAdjoint (Spec.map τ)).obj N)) :=
  moduleSpecΓFunctor.map
      ((restrictAdjunction (Spec.map e.toCommRingCatIso.inv)).unit.app
        ((closedImmersionRightAdjoint (Spec.map σ)).obj N)) ≫
    (pushforwardGlobalSectionsIso e.toCommRingCatIso.inv).hom.app
      ((restrictFunctor (Spec.map e.toCommRingCatIso.inv)).obj
        ((closedImmersionRightAdjoint (Spec.map σ)).obj N)) ≫
    (ModuleCat.restrictScalars e.toCommRingCatIso.inv.hom).map
      (moduleSpecΓFunctor.map
        ((closedImmersionRightAdjointOpenIso (Spec.map e.toCommRingCatIso.inv)
            (Spec.map τ) (Spec.map σ) (𝟙 (Spec A)) h).hom.app N ≫
          (closedImmersionRightAdjoint (Spec.map τ)).map
            (restrictFunctorId.hom.app N)))

/-- The native source-isomorphism comparison preserves evaluation at one. -/
theorem closedImmersionRightAdjointSourceIsoSections_apply_one
    (N : (Spec A).Modules)
    (x : (moduleSpecΓFunctor (R := B)).obj
      ((closedImmersionRightAdjoint (Spec.map σ)).obj N)) :
    closedImmersionRightAdjointSectionsLinearEquiv τ N
        (closedImmersionRightAdjointSourceIsoSections σ τ e h N x) (1 : C) =
      closedImmersionRightAdjointSectionsLinearEquiv σ N x (1 : B) := by
  let z : (moduleSpecΓFunctor (R := C)).obj
      ((closedImmersionRightAdjoint (Spec.map τ)).obj N) :=
    closedImmersionRightAdjointSourceIsoSections σ τ e h N x
  change closedImmersionRightAdjointSectionsLinearEquiv τ N z (1 : C) = _
  refine (closedImmersionRightAdjointSectionsLinearEquiv_apply_one τ N z).trans ?_
  refine Eq.trans ?_
    (closedImmersionRightAdjointSectionsLinearEquiv_apply_one σ N x).symm
  let K := (closedImmersionRightAdjoint (Spec.map σ)).obj N
  let a := Spec.map e.toCommRingCatIso.inv
  let o := (closedImmersionRightAdjointOpenIso a (Spec.map τ)
    (Spec.map σ) (𝟙 (Spec A)) h).hom.app N
  let y : (moduleSpecΓFunctor (R := C)).obj ((restrictFunctor a).obj K) :=
    (moduleSpecΓFunctor.map ((restrictAdjunction a).unit.app K) ≫
    (pushforwardGlobalSectionsIso e.toCommRingCatIso.inv).hom.app
      ((restrictFunctor a).obj K)) x
  change (((pushforward (Spec.map τ)).map
      (o ≫ (closedImmersionRightAdjoint (Spec.map τ)).map
        (restrictFunctorId.hom.app N)) ≫
      (closedImmersionRightAdjunction (Spec.map τ)).counit.app N).app ⊤) y = _
  have hn : (pushforward (Spec.map τ)).map
        ((closedImmersionRightAdjoint (Spec.map τ)).map (restrictFunctorId.hom.app N)) ≫
      (closedImmersionRightAdjunction (Spec.map τ)).counit.app N =
    (closedImmersionRightAdjunction (Spec.map τ)).counit.app
        ((restrictFunctor (𝟙 (Spec A))).obj N) ≫ restrictFunctorId.hom.app N :=
    (closedImmersionRightAdjunction (Spec.map τ)).counit.naturality
      (restrictFunctorId.hom.app N)
  rw [(pushforward (Spec.map τ)).map_comp, Category.assoc, hn]
  have H := congrArg
    (fun z => (restrictFunctorId.hom.app N).app ⊤ (z.app ⊤ x))
    (closedImmersionRightAdjointOpenIso_unit_counit a (Spec.map τ)
      (Spec.map σ) (𝟙 (Spec A)) h N)
  have hsquare :
      ((cartesianPushforwardSquare a (Spec.map τ) (Spec.map σ) (𝟙 (Spec A)) h).hom.app
        ((restrictFunctor a).obj K)).app ⊤ = 𝟙 Γ((restrictFunctor a).obj K, ⊤) := by
    simp only [cartesianPushforwardSquare, Iso.trans_hom, NatTrans.comp_app,
      Iso.symm_hom, Hom.comp_app, pushforwardComp_hom_app_app,
      pushforwardComp_inv_app_app, pushforwardCongr_hom_app_app]
    change (𝟙 Γ((restrictFunctor a).obj K, ⊤)) ≫
      ((restrictFunctor a).obj K).presheaf.map _ ≫
        (𝟙 Γ((restrictFunctor a).obj K, ⊤)) = 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    calc
      _ = ((restrictFunctor a).obj K).presheaf.map (𝟙 (Opposite.op ⊤)) :=
        congrArg _ (Subsingleton.elim _ _)
      _ = _ := ((restrictFunctor a).obj K).presheaf.map_id _
  have hidentity : ((restrictAdjunction (𝟙 (Spec A))).unit.app N).app ⊤ ≫
      (restrictFunctorId.hom.app N).app ⊤ = 𝟙 Γ(N, ⊤) := by
    let V : (Spec A).Opens := (𝟙 (Spec A)) ''ᵁ ⊤
    let f : Opposite.op (⊤ : (Spec A).Opens) ⟶ Opposite.op V :=
      (homOfLE (show V ≤ ⊤ from le_top)).op
    let g : Opposite.op V ⟶ Opposite.op (⊤ : (Spec A).Opens) :=
      (eqToHom (show (⊤ : (Spec A).Opens) = V by simp [V])).op
    change N.presheaf.map f ≫ N.presheaf.map g = 𝟙 Γ(N, ⊤)
    rw [← N.presheaf.map_comp]
    calc
      _ = N.presheaf.map (𝟙 (Opposite.op ⊤)) :=
        congrArg _ (Subsingleton.elim _ _)
      _ = _ := N.presheaf.map_id _
  change (((restrictAdjunction a).unit.app K).app ⊤ ≫
      ((cartesianPushforwardSquare a (Spec.map τ) (Spec.map σ) (𝟙 (Spec A)) h).hom.app
        ((restrictFunctor a).obj K)).app ⊤ ≫ o.app ⊤ ≫
      ((closedImmersionRightAdjunction (Spec.map τ)).counit.app
        ((restrictFunctor (𝟙 (Spec A))).obj N)).app ⊤ ≫
      (restrictFunctorId.hom.app N).app ⊤) x =
    (((closedImmersionRightAdjunction (Spec.map σ)).counit.app N).app ⊤ ≫
      ((restrictAdjunction (𝟙 (Spec A))).unit.app N).app ⊤ ≫
      (restrictFunctorId.hom.app N).app ⊤) x at H
  rw [hsquare] at H
  erw [Category.id_comp, hidentity, Category.comp_id] at H
  have hy : y = ((restrictAdjunction a).unit.app K).app ⊤ x := rfl
  erw [hy]
  exact H

/-- The actual geometric source-isomorphism comparison is precomposition by
the original ring isomorphism in the original affine coinduced Hom model. -/
theorem closedImmersionRightAdjointSourceIsoSections_apply
    (N : (Spec A).Modules)
    (x : (moduleSpecΓFunctor (R := B)).obj
      ((closedImmersionRightAdjoint (Spec.map σ)).obj N)) (c : C) :
    closedImmersionRightAdjointSectionsLinearEquiv τ N
        (closedImmersionRightAdjointSourceIsoSections σ τ e h N x) c =
      closedImmersionRightAdjointSectionsLinearEquiv σ N x (e c) := by
  let F := closedImmersionRightAdjointSourceIsoSections σ τ e h N
  let y : (moduleSpecΓFunctor (R := C)).obj
      ((closedImmersionRightAdjoint (Spec.map τ)).obj N) := F x
  let y' : (moduleSpecΓFunctor (R := C)).obj
      ((closedImmersionRightAdjoint (Spec.map τ)).obj N) := F (e c • x)
  have hs : y' = c • y := by
    have hh := F.hom.map_smul (e c) x
    change y' = e.symm (e c) • y at hh
    simpa only [RingEquiv.symm_apply_apply] using hh
  change closedImmersionRightAdjointSectionsLinearEquiv τ N y c = _
  calc
    _ = closedImmersionRightAdjointSectionsLinearEquiv τ N (c • y) (1 : C) := by
      simpa only [one_mul] using
        (closedImmersionRightAdjointSectionsLinearEquiv_smul_apply τ N y c (1 : C)).symm
    _ = closedImmersionRightAdjointSectionsLinearEquiv τ N y' (1 : C) :=
      congrArg (fun z => closedImmersionRightAdjointSectionsLinearEquiv τ N z (1 : C)) hs.symm
    _ = closedImmersionRightAdjointSectionsLinearEquiv σ N (e c • x) (1 : B) :=
      closedImmersionRightAdjointSourceIsoSections_apply_one σ τ e h N (e c • x)
    _ = _ := by
      simpa only [one_mul] using
        closedImmersionRightAdjointSectionsLinearEquiv_smul_apply σ N x (e c) (1 : B)

end SourceIsomorphism

end AlgebraicGeometry.Scheme.Modules
