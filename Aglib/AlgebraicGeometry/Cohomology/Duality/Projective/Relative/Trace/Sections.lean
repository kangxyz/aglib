/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Composition

/-!
# Native affine sections for the relative projective trace

The original restriction unit determines affine module morphisms. On an affine
Cartesian open square, the original higher direct image restriction becomes the
original geometric cohomology map under the original affine section comparisons.
The schemes, coefficients and injective resolutions remain arbitrary.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u

namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

theorem affineHom_ext {A : CommRingCat.{u}} {M N : (Spec A).Modules}
    [M.IsQuasicoherent] {f g : M ⟶ N}
    (h : moduleSpecΓFunctor.map f = moduleSpecΓFunctor.map g) : f = g := by
  apply (cancel_epi M.fromTildeΓ).mp
  have hf := fromTildeΓNatTrans.naturality f
  have hg := fromTildeΓNatTrans.naturality g
  change (tilde.functor A).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ = M.fromTildeΓ ≫ f at hf
  change (tilde.functor A).map (moduleSpecΓFunctor.map g) ≫ N.fromTildeΓ = M.fromTildeΓ ≫ g at hg
  exact hf.symm.trans ((congrArg (fun t => (tilde.functor A).map t ≫ N.fromTildeΓ) h).trans hg)

/-- The map on global sections induced by the unit of the open restriction adjunction. -/
def affineUnitSections
    {R A : CommRingCat.{u}} (j : Spec A ⟶ Spec R) [IsOpenImmersion j]
    (M : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := R)).obj M →
      (moduleSpecΓFunctor (R := A)).obj (((Modules.restrictFunctor j).obj M)) :=
  fun x => ((restrictAdjunction j).unit.app M).app ⊤ x
theorem affineUnitSections_eq
    {R A : CommRingCat.{u}} (j : Spec A ⟶ Spec R) [IsOpenImmersion j]
    (M : (Spec R).Modules) (x : (moduleSpecΓFunctor (R := R)).obj M) :
    affineUnitSections j M x = ((restrictAdjunction j).unit.app M).app ⊤ x := rfl
theorem affineRestrictHom_ext
    {R A : CommRingCat.{u}} (j : Spec A ⟶ Spec R) [IsOpenImmersion j]
    {M : (Spec R).Modules} [M.IsQuasicoherent] {N : (Spec A).Modules}
    {s t : ((Modules.restrictFunctor j).obj M) ⟶ N}
    (h : ∀ x : (moduleSpecΓFunctor (R := R)).obj M,
      ModuleCat.Hom.hom ((moduleSpecΓFunctor (R := A)).map s)
          (affineUnitSections j M x) =
        ModuleCat.Hom.hom ((moduleSpecΓFunctor (R := A)).map t)
          (affineUnitSections j M x)) : s = t := by
  apply ((restrictAdjunction j).homEquiv M N).injective
  apply affineHom_ext (A := R) (M := M) (N := (Scheme.Modules.pushforward j).obj N)
  ext x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h x
theorem affineUnitSections_naturality
    {R A : CommRingCat.{u}} (j : Spec A ⟶ Spec R) [IsOpenImmersion j]
    {M N : (Spec R).Modules} (s : M ⟶ N)
    (x : (moduleSpecΓFunctor (R := R)).obj M) :
    affineUnitSections j N
        (ModuleCat.Hom.hom ((moduleSpecΓFunctor (R := R)).map s) x) =
      ModuleCat.Hom.hom ((moduleSpecΓFunctor (R := A)).map
        ((Modules.restrictFunctor j).map s)) (affineUnitSections j M x) := by
  have hu := (restrictAdjunction j).unit.naturality s
  have hh := congrArg
    (fun f : M ⟶ (Scheme.Modules.pushforward j).obj (((Modules.restrictFunctor j).obj N)) =>
      ModuleCat.Hom.hom ((moduleSpecΓFunctor (R := R)).map f) x) hu
  exact hh

/-- The coefficient cohomology linear map has the original additive component. -/
theorem moduleCohomologyMapOfHom_apply
    {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
    {M N : X.Modules} (C : M ⟶ N) (n : ℕ)
    (c : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    (show Sheaf.H.{u + 1} (moduleAddSheaf X N) n from
      moduleCohomologyMapOfHom X α C n c) =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map C) n c := rfl

/-- The original cohomology map of a restriction adjunct is the original
coefficient map after the original restriction unit. -/
theorem moduleCohomologyMapAlong_homEquiv
    {X W : Scheme.{u}} (i : W ⟶ X) [IsOpenImmersion i]
    (M : X.Modules) (N : W.Modules)
    (C : (Modules.restrictFunctor i).obj M ⟶ N) (n : ℕ)
    (c : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyMapAlong i ((restrictAdjunction i).homEquiv M N C) n c =
      Sheaf.H.map ((SheafOfModules.toSheaf W.ringCatSheaf).map C) n
        (moduleCohomologyMapAlong i ((restrictAdjunction i).unit.app M) n c) := by
  rw [Adjunction.homEquiv_unit]
  exact moduleCohomologyMapAlong_postcomp i ((restrictAdjunction i).unit.app M) C n c

/-- The native affine higher-image comparison evaluated on the original open unit.
The target morphism is qcqs by the supplied Cartesian square. -/
theorem affineHigherOpenSections_unit
    {R A : Type u} [CommRing R] [CommRing A] {X W : Scheme.{u}}
    (i : W ⟶ X) (q : W ⟶ Spec (.of A)) (p : X ⟶ Spec (.of R))
    [QuasiCompact p] [QuasiSeparated p] (σ : R →+* A)
    [IsOpenImmersion i] [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    (H : IsPullback i q p (Spec.map (CommRingCat.ofHom σ)))
    (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M)
    (J : InjectiveResolution ((Modules.restrictFunctor i).obj M)) (n : ℕ)
    (x : (moduleSpecΓFunctor (R := .of R)).obj
      (((Scheme.Modules.pushforward p).rightDerived n).obj M)) :
    let : QuasiCompact q := MorphismProperty.of_isPullback H inferInstance
    let : QuasiSeparated q := MorphismProperty.of_isPullback H inferInstance
    moduleHigherDirectImageAffineSectionsLinearEquiv (R := A) q
        ((Modules.restrictFunctor i).obj M) J n
        (ModuleCat.Hom.hom ((moduleSpecΓFunctor (R := .of A)).map
          (X := (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj
            (((Scheme.Modules.pushforward p).rightDerived n).obj M))
          (Y := ((Scheme.Modules.pushforward q).rightDerived n).obj
            ((Modules.restrictFunctor i).obj M))
          ((Scheme.Modules.higherDirectImageOpenRestrictionIso i q p
            (Spec.map (CommRingCat.ofHom σ)) H n).hom.app M))
          (affineUnitSections (Spec.map (CommRingCat.ofHom σ))
            (((Scheme.Modules.pushforward p).rightDerived n).obj M) x)) =
      moduleCohomologyMapAlong i ((restrictAdjunction i).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv (R := R) p M I n x) := by
  let : QuasiCompact q := MorphismProperty.of_isPullback H inferInstance
  let : QuasiSeparated q := MorphismProperty.of_isPullback H inferInstance
  let F : (moduleSpecΓFunctor (R := .of A)).obj
      ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj
        (((Scheme.Modules.pushforward p).rightDerived n).obj M)) →
      Sheaf.H.{u + 1} (moduleAddSheaf W ((Modules.restrictFunctor i).obj M)) n :=
    fun t => moduleHigherDirectImageAffineSectionsLinearEquiv (R := A) q
      ((Modules.restrictFunctor i).obj M) J n
      (ModuleCat.Hom.hom ((moduleSpecΓFunctor (R := .of A)).map
        (X := (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj
          (((Scheme.Modules.pushforward p).rightDerived n).obj M))
        (Y := ((Scheme.Modules.pushforward q).rightDerived n).obj
          ((Modules.restrictFunctor i).obj M))
        ((Scheme.Modules.higherDirectImageOpenRestrictionIso i q p
          (Spec.map (CommRingCat.ofHom σ)) H n).hom.app M)) t)
  have hunit := congrArg F (affineUnitSections_eq
    (Spec.map (CommRingCat.ofHom σ))
    (((Scheme.Modules.pushforward p).rightDerived n).obj M) x)
  have hnative := moduleHigherDirectImageAffineSectionsLinearEquiv_openRestriction
    i q p (CommRingCat.ofHom σ) H M I J n x
  exact hunit.trans hnative

end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
