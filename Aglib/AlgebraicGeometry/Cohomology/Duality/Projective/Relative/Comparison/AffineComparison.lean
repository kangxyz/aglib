/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.AffineModel
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.CompositionShift
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.OpenCoefficients
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.CoefficientsCoherent
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.DerivedHom

/-!
# Actual affine maps used in the relative Serre comparison

The established coefficient duality identifies the same native derived
sections map on Ext. The native affine Hom comparison identifies actual
sections on the needed direct-image Hom groups. These statements retain
all original resolution, coefficient and shift maps.
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

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u) [Fintype ι]

/-- The established affine comparison makes the very same native derived-global-sections
map on Ext bijective, since its original coefficient trace is invertible. -/
theorem projectiveDerivedGlobalSectionsCoefficients_bijective
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (q : ℕ) :
    Function.Bijective (fun x : Ext.{u + 1} M
        (projectiveResidueTwistTensorCoefficients R ι J) q =>
      x.homPlus.map ((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp
          (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι)) := by
  let P := ProjectiveSpace R ι
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let F := (moduleGlobalSectionsFunctorOfHom P α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let g := fun x : Ext.{u + 1} M (projectiveResidueTwistTensorCoefficients R ι J) q =>
    x.homPlus.map F
  let : IsIso (projectiveDerivedTraceCoefficients R ι n e J) :=
    projectiveDerivedTraceCoefficients_isIso R ι n e J
  let E := Iso.homCongr (Iso.refl (F.obj ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj M)))
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (q : ℤ)).mapIso
      (asIso (projectiveDerivedTraceCoefficients R ι n e J)))
  have heq : (projectiveDerivedSerreMapCoefficients R ι n e J M q : _ → _) = E ∘ g := by
    funext x
    rw [projectiveDerivedSerreMapCoefficients_apply]
    change x.homPlus.map F ≫ _ = 𝟙 _ ≫ x.homPlus.map F ≫ _
    rw [Category.id_comp]
    rfl
  have hb := projectiveDerivedSerreMapCoefficients_bijective R ι n e J M hM q
  rw [heq] at hb
  exact (Equiv.comp_bijective g E).mp hb

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

private def plusShiftedHomEquiv {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (K L : DerivedCategory.Plus C) (k : ℤ) :
    ShiftedHom K L k ≃ ShiftedHom (DerivedCategory.Plus.ι.obj K)
      (DerivedCategory.Plus.ι.obj L) k :=
  ((Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι (C := C))).homEquiv).trans
    (Iso.homCongr (Iso.refl _) ((DerivedCategory.Plus.ι.commShiftIso k).app L))

private theorem plusShiftedHomEquiv_apply
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (K L : DerivedCategory.Plus C) (k : ℤ) (a : ShiftedHom K L k) :
    plusShiftedHomEquiv K L k a = a.map DerivedCategory.Plus.ι := by
  change 𝟙 _ ≫ DerivedCategory.Plus.ι.map a ≫
    (DerivedCategory.Plus.ι.commShiftIso k).hom.app L = _
  rw [Category.id_comp]
  rfl

/-- Actual derived affine sections are bijective on the original Hom groups from a
quasicoherent direct image to a shifted quasicoherent single. This is the SAME functor
map, obtained from the native affine Hom comparison by its displayed original isomorphisms. -/
theorem moduleSpecDerivedPushforwardSectionsHom_bijective
    {A : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec A)
    [QuasiCompact p] [QuasiSeparated p] (M : X.Modules) [M.IsQuasicoherent]
    (N : (Spec A).Modules) [N.IsQuasicoherent] (n r : ℕ) :
    let F := (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus
    let K := (Scheme.Modules.derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
    Function.Bijective
      (F.map (X := K) (Y := ((DerivedCategory.Plus.singleFunctor (Spec A).Modules
        (n : ℤ)).obj N)⟦(r : ℤ)⟧)) := by
  let F := (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus
  let K := (Scheme.Modules.derivedPushforwardPlus p).obj
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  let S₀ := (DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N
  let Sₙ := (DerivedCategory.Plus.singleFunctor (Spec A).Modules (n : ℤ)).obj N
  let k : ℤ := (r : ℤ) - n
  let c := relativeOpenCoefficientShiftIso N (n : ℤ) (r : ℤ)
  let d := relativeOpenCoefficientShiftIso (moduleSpecΓFunctor.obj N) (n : ℤ) (r : ℤ)
  let FF := Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := (Spec A).Modules))
  let cP : Sₙ⟦(r : ℤ)⟧ ≅ S₀⟦k⟧ := FF.preimageIso
    ((DerivedCategory.Plus.ι.commShiftIso (r : ℤ)).app Sₙ ≪≫ c ≪≫
      ((DerivedCategory.Plus.ι.commShiftIso k).app S₀).symm)
  let e : moduleGlobalSectionsFunctorOfHom (Spec A) (Scheme.ΓSpecIso A).inv.hom ≅
      moduleSpecΓFunctor :=
    NatIso.ofComponents
      (fun L => (moduleTopSectionsIso (Spec A) (Scheme.ΓSpecIso A).inv.hom L).symm)
      (by intro L L' f; ext x; rfl)
  let C := moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso A).inv.hom ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward p).rightDerivedFunctorPlus
      ((moduleGlobalSectionsFunctorOfHom (Spec A)
        (Scheme.ΓSpecIso A).inv.hom).rightDerivedFunctorPlusIso e)
  let E := (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlusSingleIsoOfAcyclic N
    (AffineDerived.isZero_rightDerived_globalSections_succ N)
  let D := DerivedCategory.Plus.ι.mapIso (F.mapIso cP) ≪≫
    DerivedCategory.Plus.ι.mapIso ((F.commShiftIso k).app S₀) ≪≫
    (DerivedCategory.Plus.ι.commShiftIso k).app (F.obj S₀) ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k).mapIso
      (DerivedCategory.Plus.ι.mapIso E) ≪≫ d.symm
  let E₁ := plusShiftedHomEquiv K Sₙ (r : ℤ)
  let T := (moduleGlobalSectionsFunctorOfHom X
    (p.appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom)).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  let E₂ : (F.obj K ⟶ F.obj (Sₙ⟦(r : ℤ)⟧)) ≃
      (DerivedCategory.Plus.ι.obj T ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (n : ℤ)).obj
          (moduleSpecΓFunctor.obj N))⟦(r : ℤ)⟧) :=
    ((Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι (C := ModuleCat.{u} A))).homEquiv).trans
      (Iso.homCongr (DerivedCategory.Plus.ι.mapIso
        (C.app ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))).symm D)
  have heq : E₂ ∘ (F.map (X := K) (Y := Sₙ⟦(r : ℤ)⟧)) =
      (moduleSpecDerivedPushforwardHomAddEquiv p M N n r) ∘ E₁ := by
    funext a
    have hv : DerivedCategory.Plus.ι.preimage
        (((E₁ a) ≫ c.hom) ≫ (DerivedCategory.Plus.ι.commShiftIso k).inv.app S₀) =
          a ≫ cP.hom := by
      apply DerivedCategory.Plus.ι.map_injective
      rw [Functor.map_preimage, Functor.map_comp]
      change ((E₁ a) ≫ c.hom) ≫ (DerivedCategory.Plus.ι.commShiftIso k).inv.app S₀ =
        DerivedCategory.Plus.ι.map a ≫ DerivedCategory.Plus.ι.map (FF.preimage _)
      rw [FF.map_preimage, plusShiftedHomEquiv_apply]
      simp only [ShiftedHom.map, Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
        Category.assoc]
    rw [Function.comp_apply, Function.comp_apply, moduleSpecDerivedPushforwardHomAddEquiv_apply]
    change E₂ (F.map a) =
      DerivedCategory.Plus.ι.map (C.hom.app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ≫
      ShiftedHom.map (DerivedCategory.Plus.ι.preimage
        (((E₁ a) ≫ c.hom) ≫ (DerivedCategory.Plus.ι.commShiftIso k).inv.app S₀) :
          ShiftedHom K S₀ k)
          (F ⋙ DerivedCategory.Plus.ι) ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k).map
        (DerivedCategory.Plus.ι.map E.hom) ≫ d.inv
    rw [hv]
    simp only [E₂, D, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom, ShiftedHom.map, Functor.comp_map, Functor.map_comp,
      Functor.commShiftIso_comp_hom_app, Category.assoc]
  have hb := (moduleSpecDerivedPushforwardHomAddEquiv p M N n r).bijective.comp E₁.bijective
  rw [← heq] at hb
  exact (Equiv.comp_bijective (F.map (X := K) (Y := Sₙ⟦(r : ℤ)⟧)) E₂).mp hb

end AlgebraicGeometry.Scheme.Cohomology
