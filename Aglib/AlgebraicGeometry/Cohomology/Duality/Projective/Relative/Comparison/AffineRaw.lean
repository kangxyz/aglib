/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.AffineComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# The original affine pushforward map before the trace

The established coefficient duality makes the original derived-sections map
bijective. The actual affine Hom comparison and native composition isomorphism
then show that the original derived-pushforward map is bijective. The target
comparison uses the full affine coefficient model. No trace is replaced and no
flatness assumption is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Cohomology.projectiveCoefficientTraceTarget

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem map_bijective_of_target_iso
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (X : C)
    {Y Z : C} (E : Y ≅ Z)
    (h : Function.Bijective (F.map (X := X) (Y := Z))) :
    Function.Bijective (F.map (X := X) (Y := Y)) := by
  let A := Iso.homCongr (Iso.refl X) E
  let B := Iso.homCongr (Iso.refl (F.obj X)) (F.mapIso E)
  have heq : B ∘ (F.map (X := X) (Y := Y)) =
      (F.map (X := X) (Y := Z)) ∘ A := by
    funext a
    simp only [A, B, Function.comp_apply, Iso.homCongr_apply, Iso.refl_inv,
      Category.id_comp, Functor.mapIso_hom, Functor.map_comp]
  have hb := h.comp A.bijective
  rw [← heq] at hb
  exact (Equiv.comp_bijective (F.map (X := X) (Y := Y)) B).mp hb

private theorem map_bijective_of_natIso
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (E : F ≅ G) (X Y : C)
    (h : Function.Bijective (G.map (X := X) (Y := Y))) :
    Function.Bijective (F.map (X := X) (Y := Y)) := by
  let B := Iso.homCongr (E.app X) (E.app Y)
  have heq : (G.map (X := X) (Y := Y)) = B ∘ (F.map (X := X) (Y := Y)) := by
    funext a
    change G.map a = E.inv.app X ≫ F.map a ≫ E.hom.app Y
    rw [E.hom.naturality, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [heq] at h
  exact (Equiv.comp_bijective (F.map (X := X) (Y := Y)) B).mp h

/-- The native ordinary derived-sections map is bijective on the original
differential-coefficient Ext pair in every nonnegative degree. -/
theorem projectiveDerivedGlobalSectionsDifferentialHom_bijective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent]
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (q : ℕ) :
    let G := (moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus
    Function.Bijective
      (G.map (X := (DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj M)
        (Y := ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N))⟦(q : ℤ)⟧)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let P := ProjectiveSpace R ι
  let G := (moduleGlobalSectionsFunctorOfHom P
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus
  let F := G ⋙ DerivedCategory.Plus.ι
  let S := DerivedCategory.Plus.singleFunctor P.Modules 0
  let J := moduleSpecΓFunctor.obj N
  let W := projectiveResidueTwistTensorCoefficients R ι J
  let A := (Ext.homPlusAddEquiv (X := M) (Y := W) q).toEquiv
  let B := Iso.homCongr (Iso.refl (F.obj (S.obj M)))
    ((F.commShiftIso (q : ℤ)).app (S.obj W))
  have heq : (fun x : Ext.{u + 1} M W q => x.homPlus.map F) =
      B ∘ ((F.map (X := S.obj M) (Y := (S.obj W)⟦(q : ℤ)⟧)) ∘ A) := by
    funext x
    simp only [A, B, Function.comp_apply, Iso.homCongr_apply, Iso.refl_inv,
      Category.id_comp, ShiftedHom.map, Iso.app_hom]
    rfl
  have hb := projectiveDerivedGlobalSectionsCoefficients_bijective R ι n e J M hM q
  change Function.Bijective (fun x : Ext.{u + 1} M W q => x.homPlus.map F) at hb
  rw [heq] at hb
  have hF := (Equiv.comp_bijective
    ((F.map (X := S.obj M) (Y := (S.obj W)⟦(q : ℤ)⟧)) ∘ A) B).mp hb
  have hF' := (Equiv.bijective_comp A
    (F.map (X := S.obj M) (Y := (S.obj W)⟦(q : ℤ)⟧))).mp hF
  have hG : Function.Bijective
      (G.map (X := S.obj M) (Y := (S.obj W)⟦(q : ℤ)⟧)) := by
    exact (Function.Bijective.of_comp_iff'
      ((Functor.FullyFaithful.ofFullyFaithful
        (DerivedCategory.Plus.ι (C := ModuleCat.{u} R))).map_bijective _ _)
      (G.map (X := S.obj M) (Y := (S.obj W)⟦(q : ℤ)⟧))).mp hF'
  exact map_bijective_of_target_iso G (S.obj M)
    ((shiftFunctor (DerivedCategory.Plus P.Modules) (q : ℤ)).mapIso
      (S.mapIso (projectiveDifferentialCoefficientResidueIso R ι n e N))) hG

/-- The actual derived-pushforward map on differential-coefficient Ext is bijective
over an affine Noetherian base, before postcomposition with any trace. -/
theorem projectiveDerivedPushforwardDifferentialExt_bijective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : (Spec (.of R)).Modules) [N.IsQuasicoherent]
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (q : ℕ) :
    Function.Bijective (fun x : Ext.{u + 1} M
        ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N) q =>
      x.homPlus.map (Scheme.Modules.derivedPushforwardPlus (toSpec R ι) ⋙
        DerivedCategory.Plus.ι)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let : (moduleSpecΓFunctor (R := .of R)).Additive := moduleSpecΓFunctor_additive (.of R)
  let P := ProjectiveSpace R ι
  let p := toSpec R ι
  let S := DerivedCategory.Plus.singleFunctor P.Modules 0
  let Ω := (relativeTopDifferentialCoefficientsFunctor p n).obj N
  let Rp := Scheme.Modules.derivedPushforwardPlus p
  let Γ := moduleGlobalSectionsFunctorOfHom (Spec (.of R)) (Scheme.ΓSpecIso (.of R)).inv.hom
  let RΓ := Γ.rightDerivedFunctorPlus
  let G := (moduleGlobalSectionsFunctorOfHom P
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus
  let C := moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso (.of R)).inv.hom
  have hG := projectiveDerivedGlobalSectionsDifferentialHom_bijective R ι n e N M hM q
  have hcomp : Function.Bijective
      ((Rp ⋙ RΓ).map (X := S.obj M) (Y := (S.obj Ω)⟦(q : ℤ)⟧)) :=
    map_bijective_of_natIso C.symm (S.obj M) ((S.obj Ω)⟦(q : ℤ)⟧) hG
  let J : Γ ≅ moduleSpecΓFunctor :=
    NatIso.ofComponents
      (fun L => (moduleTopSectionsIso (Spec (.of R)) (Scheme.ΓSpecIso (.of R)).inv.hom L).symm)
      (by intro L L' f; ext x; rfl)
  let T := ((DerivedCategory.Plus.singleFunctor (Spec (.of R)).Modules (n : ℤ)).obj N)⟦(q : ℤ)⟧
  have hRΓ : Function.Bijective (RΓ.map (X := Rp.obj (S.obj M)) (Y := T)) :=
    map_bijective_of_natIso (Γ.rightDerivedFunctorPlusIso J) (Rp.obj (S.obj M)) T
      (moduleSpecDerivedPushforwardSectionsHom_bijective p M N n q)
  let E := (Rp.commShiftIso (q : ℤ)).app (S.obj Ω) ≪≫
    (shiftFunctor (DerivedCategory.Plus (Spec (.of R)).Modules) (q : ℤ)).mapIso
      (projectiveDifferentialCoefficientsAffineSingleIso R ι n e N)
  have hRΓ' := map_bijective_of_target_iso RΓ (Rp.obj (S.obj M)) E hRΓ
  have hRp : Function.Bijective (Rp.map (X := S.obj M) (Y := (S.obj Ω)⟦(q : ℤ)⟧)) :=
    (Function.Bijective.of_comp_iff' hRΓ'
      (Rp.map (X := S.obj M) (Y := (S.obj Ω)⟦(q : ℤ)⟧))).mp hcomp
  let F := Rp ⋙ DerivedCategory.Plus.ι
  have hF : Function.Bijective (F.map (X := S.obj M) (Y := (S.obj Ω)⟦(q : ℤ)⟧)) :=
    ((Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι (C := (Spec (.of R)).Modules))).map_bijective _ _).comp hRp
  let A := (Ext.homPlusAddEquiv (X := M) (Y := Ω) q).toEquiv
  let B := Iso.homCongr (Iso.refl (F.obj (S.obj M)))
    ((F.commShiftIso (q : ℤ)).app (S.obj Ω))
  have heq : (fun x : Ext.{u + 1} M Ω q => x.homPlus.map F) =
      B ∘ ((F.map (X := S.obj M) (Y := (S.obj Ω)⟦(q : ℤ)⟧)) ∘ A) := by
    funext x
    simp only [A, B, Function.comp_apply, Iso.homCongr_apply, Iso.refl_inv,
      Category.id_comp, ShiftedHom.map, Iso.app_hom]
    rfl
  change Function.Bijective (fun x : Ext.{u + 1} M Ω q => x.homPlus.map F)
  rw [heq]
  exact B.bijective.comp (hF.comp A.bijective)

end AlgebraicGeometry.Scheme.Cohomology
