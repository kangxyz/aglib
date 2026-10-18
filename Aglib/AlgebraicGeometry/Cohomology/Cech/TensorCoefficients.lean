/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.AffineSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.Algebra.Category.ModuleCat.Tensor.ScalarExtension
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.CoefficientNaturality
public import Aglib.AlgebraicGeometry.Cohomology.Cech.ModuleBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.AffinePullback
public import Aglib.Algebra.Homology.Flat.ModuleTensor
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.UniversalTensor
public import Aglib.Algebra.Homology.Embedding.MapExtend.Naturality
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFunctorAssociator.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free.Sections
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-! # Actual Cech complexes with arbitrary base-module tensor coefficients

The native finite Cech coefficient comparison is followed by the original tensor
section map and geometric pullback unit. On affine intersections it is invertible
for quasicoherent coefficients, over every commutative ring and every base module.
The native bounded good truncation commutes with this tensor whenever its two
following original terms are flat: universal boundary tensor exactness supplies
preservation of the actual cycle kernel. The forward map retains the literal
original truncation inclusion. No flatness assumption on the base module, generic
preservation-of-homology instance, or unbounded K-flat assertion is used.

Coefficient morphisms commute with the actual section, cochain and finite-model
maps. For the base ring itself, the actual geometric units and original tensor
right unitor recover the native cochain right-unitor map.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.BraidedCategory
  AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open HomologicalComplex CategoryTheory.Cech
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

private def moduleTildeGlobalSectionsSeed (J : ModuleCat.{u} R) :
    J ⟶ (moduleSectionsPresheaf (Spec (CommRingCat.of R))
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (tilde J)).obj (op ⊤) :=
  ModuleCat.ofHom (X := J)
    (Y := (moduleSectionsPresheaf (Spec (CommRingCat.of R))
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (tilde J)).obj (op ⊤))
    (tilde.toOpen (R := CommRingCat.of R) J ⊤).hom

/-- The original tilde and geometric pullback units give the global coefficient section. -/
def modulePullbackTildeGlobalSeed (p : X ⟶ Spec (CommRingCat.of R)) (J : ModuleCat.{u} R) :
    J ⟶ (moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
        ((Scheme.Modules.pullback p).obj (tilde J))).obj (op (p ⁻¹ᵁ ⊤)) :=
  ModuleCat.ofHom (X := J)
    (Y := (moduleSectionsPresheaf (Spec (CommRingCat.of R))
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (tilde J)).obj (op ⊤))
    (tilde.toOpen (R := CommRingCat.of R) J ⊤).hom ≫
    (moduleSectionsMapAlong p (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      (RingHom.id R) (by ext r; rfl)
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (tilde J))).app (op ⊤) ≫
    (ModuleCat.restrictScalarsId R).hom.app _

/-- The original tilde and geometric pullback units give a coefficient section on every open. -/
def modulePullbackTildeSeed (p : X ⟶ Spec (CommRingCat.of R)) (J : ModuleCat.{u} R) :
    (Functor.const X.Opensᵒᵖ).obj J ⟶
      moduleSectionsPresheaf X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
          ((Scheme.Modules.pullback p).obj (tilde J)) where
  app U := modulePullbackTildeGlobalSeed p J ≫
    (moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
        ((Scheme.Modules.pullback p).obj (tilde J))).map
          (homOfLE (show U.unop ≤ p ⁻¹ᵁ ⊤ by simp)).op
  naturality {U V} i := by
    change (𝟙 J) ≫ (modulePullbackTildeGlobalSeed p J ≫ _) =
      (modulePullbackTildeGlobalSeed p J ≫ _) ≫ _
    rw [Category.id_comp, Category.assoc, ← CategoryTheory.Functor.map_comp]
    exact congrArg (fun k ↦ modulePullbackTildeGlobalSeed p J ≫
      (moduleSectionsPresheaf X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
          ((Scheme.Modules.pullback p).obj (tilde J))).map k) (Subsingleton.elim _ _)

/-- The coefficient section is the original pullback unit followed by the original restriction. -/
theorem modulePullbackTildeSeed_app_apply (p : X ⟶ Spec (CommRingCat.of R))
    (J : ModuleCat.{u} R) (U : X.Opens) (j : J) :
    (modulePullbackTildeSeed p J).app (op U) j =
      ((Scheme.Modules.pullback p).obj (tilde J)).presheaf.map
        (homOfLE (show U ≤ p ⁻¹ᵁ ⊤ by simp)).op
        ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (tilde J)).app ⊤)
          (tilde.toOpen (R := CommRingCat.of R) J ⊤ j)) := rfl

/-- Every native coefficient morphism preserves these original unit sections. -/
theorem modulePullbackTildeSeed_map_apply (p : X ⟶ Spec (CommRingCat.of R))
    {J J' : ModuleCat.{u} R} (f : J ⟶ J') (U : X.Opens) (j : J) :
    ((Scheme.Modules.pullback p).map (tilde.map f)).app U
      ((modulePullbackTildeSeed p J).app (op U) j) =
        (modulePullbackTildeSeed p J').app (op U) (f j) := by
  let P := (Scheme.Modules.pullback p).obj (tilde J)
  let P' := (Scheme.Modules.pullback p).obj (tilde J')
  let ψ := (Scheme.Modules.pullback p).map (tilde.map f)
  let η := (Scheme.Modules.pullbackPushforwardAdjunction p).unit
  let i := (homOfLE (show U ≤ p ⁻¹ᵁ ⊤ by simp)).op
  have hη := congrArg (fun q ↦ q.app ⊤) (η.naturality (tilde.map f))
  have hu := congrArg (fun q ↦ q (tilde.toOpen (R := CommRingCat.of R) J ⊤ j)) hη
  change (η.app (tilde J')).app ⊤
      ((tilde.map f).app ⊤ (tilde.toOpen (R := CommRingCat.of R) J ⊤ j)) =
    ψ.app (p ⁻¹ᵁ ⊤)
      ((η.app (tilde J)).app ⊤ (tilde.toOpen (R := CommRingCat.of R) J ⊤ j)) at hu
  have hf := congrArg (fun q ↦ q j)
    (tilde.toOpen_map_app (R := CommRingCat.of R) f ⊤)
  change (tilde.map f).app ⊤ (tilde.toOpen (R := CommRingCat.of R) J ⊤ j) =
    tilde.toOpen (R := CommRingCat.of R) J' ⊤ (f j) at hf
  have ht := hu.symm.trans (congrArg (fun z ↦ (η.app (tilde J')).app ⊤ z) hf)
  have hr := PresheafOfModules.naturality_apply ψ.val i
    ((η.app (tilde J)).app ⊤ (tilde.toOpen (R := CommRingCat.of R) J ⊤ j))
  change ψ.app U (P.presheaf.map i
    ((η.app (tilde J)).app ⊤ (tilde.toOpen (R := CommRingCat.of R) J ⊤ j))) =
    P'.presheaf.map i (ψ.app (p ⁻¹ᵁ ⊤)
      ((η.app (tilde J)).app ⊤ (tilde.toOpen (R := CommRingCat.of R) J ⊤ j))) at hr
  calc
    _ = ψ.app U (P.presheaf.map i
        ((η.app (tilde J)).app ⊤ (tilde.toOpen (R := CommRingCat.of R) J ⊤ j))) :=
      congrArg (fun z ↦ ψ.app U z) (modulePullbackTildeSeed_app_apply p J U j)
    _ = P'.presheaf.map i (ψ.app (p ⁻¹ᵁ ⊤)
        ((η.app (tilde J)).app ⊤ (tilde.toOpen (R := CommRingCat.of R) J ⊤ j))) := hr
    _ = P'.presheaf.map i
        ((η.app (tilde J')).app ⊤ (tilde.toOpen (R := CommRingCat.of R) J' ⊤ (f j))) :=
      congrArg (fun z ↦ P'.presheaf.map i z) ht
    _ = _ := (modulePullbackTildeSeed_app_apply p J' U (f j)).symm

/-- Tensor original sections with arbitrary base coefficients using the actual tensor section. -/
def moduleTensorTildeSectionsMap (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (J : ModuleCat.{u} R) :
    moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M ⋙ tensorRight J ⟶
    moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      ((moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J))) := by
  let α : R →+* Γ(X, ⊤) :=
    p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let P := (Scheme.Modules.pullback p).obj (tilde J)
  let γ := modulePullbackTildeSeed p J
  refine
    { app := fun U ↦
        ModuleCat.MonoidalCategory.tensorLift
          (fun m j ↦ moduleTensorSection X M P U.unop
            (show Γ(M, U.unop) from m) (show Γ(P, U.unop) from γ.app U j))
          (by
            intro m m' j
            exact moduleTensorSection_add_left X M P U.unop m m' (γ.app U j))
          (by
            intro r m j
            change moduleTensorSection X M P U.unop
              (globalRestriction X U.unop (α r) • (show Γ(M, U.unop) from m))
                (show Γ(P, U.unop) from γ.app U j) =
              globalRestriction X U.unop (α r) •
                moduleTensorSection X M P U.unop m (γ.app U j)
            exact moduleTensorSection_smul_left X M P U.unop
              (globalRestriction X U.unop (α r)) m (γ.app U j))
          (by
            intro m j j'
            exact (congrArg (fun z ↦ moduleTensorSection X M P U.unop m z)
              ((γ.app U).hom.map_add j j')).trans
                (moduleTensorSection_add_right X M P U.unop m (γ.app U j) (γ.app U j')))
          (by
            intro r m j
            change moduleTensorSection X M P U.unop m (γ.app U (r • j)) =
              globalRestriction X U.unop (α r) •
                moduleTensorSection X M P U.unop m (γ.app U j)
            have hγ := (γ.app U).hom.map_smul r j
            change γ.app U (r • j) =
              globalRestriction X U.unop (α r) • (show Γ(P, U.unop) from γ.app U j) at hγ
            exact (congrArg (fun z ↦ moduleTensorSection X M P U.unop m z) hγ).trans
              (moduleTensorSection_smul_right X M P U.unop
                (globalRestriction X U.unop (α r)) m (γ.app U j)))
      naturality := ?_ }
  intro U V i
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m j
  change moduleTensorSection X M P V.unop (M.presheaf.map i m) (γ.app V j) =
    ((moduleTensorLeftFunctor X M).obj P).presheaf.map i
      (moduleTensorSection X M P U.unop m (γ.app U j))
  have hγ := congrArg (fun q ↦ q j) (γ.naturality i)
  change γ.app V j = P.presheaf.map i (γ.app U j) at hγ
  have hres := moduleTensorSection_restrict M P i.unop m (γ.app U j)
  exact (congrArg (fun z ↦ moduleTensorSection X M P V.unop
    (M.presheaf.map i m) z) hγ).trans hres.symm

/-- Each pure tensor maps to the original tensor section and coefficient unit section. -/
theorem moduleTensorTildeSectionsMap_app_tmul (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (J : ModuleCat.{u} R) (U : X.Opens)
    (m : (moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M).obj (op U))
    (j : J) :
    (moduleTensorTildeSectionsMap p M J).app (op U) (m ⊗ₜ[R] j) =
      moduleTensorSection X M ((Scheme.Modules.pullback p).obj (tilde J)) U
        (show Γ(M, U) from m)
        (show Γ((Scheme.Modules.pullback p).obj (tilde J), U) from
          (modulePullbackTildeSeed p J).app (op U) j) := rfl

/-- The original sheaf coefficient map retains every pure tensor generator. -/
theorem moduleTensorTildeSectionsMap_map_tmul (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) {J J' : ModuleCat.{u} R} (f : J ⟶ J') (U : X.Opens)
    (m : (moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M).obj (op U))
    (j : J) :
    ((moduleTensorLeftFunctor X M).map ((Scheme.Modules.pullback p).map (tilde.map f))).app U
      ((moduleTensorTildeSectionsMap p M J).app (op U) (m ⊗ₜ[R] j)) =
    (moduleTensorTildeSectionsMap p M J').app (op U) (m ⊗ₜ[R] f j) := by
  let ψ := (Scheme.Modules.pullback p).map (tilde.map f)
  have hγ := modulePullbackTildeSeed_map_apply p f U j
  have ht := moduleTensorLeftFunctor_map_section (X := X) M ψ U m
    ((modulePullbackTildeSeed p J).app (op U) j)
  exact (congrArg (fun z ↦ ((moduleTensorLeftFunctor X M).map ψ).app U z)
    (moduleTensorTildeSectionsMap_app_tmul p M J U m j)).trans
      (ht.trans ((congrArg (fun z ↦ moduleTensorSection X M
        ((Scheme.Modules.pullback p).obj (tilde J')) U m z) hγ).trans
          (moduleTensorTildeSectionsMap_app_tmul p M J' U m (f j)).symm))

/-- The actual section comparison is natural in every base-module coefficient morphism. -/
theorem moduleTensorTildeSectionsMap_naturality_coefficients
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
    {J J' : ModuleCat.{u} R} (f : J ⟶ J') :
    moduleTensorTildeSectionsMap p M J ≫
      (moduleSectionsPresheafFunctor X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).map
          ((moduleTensorLeftFunctor X M).map ((Scheme.Modules.pullback p).map (tilde.map f))) =
    Functor.whiskerLeft
      (moduleSectionsPresheaf X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M)
      ((tensoringRight (ModuleCat.{u} R)).map f) ≫ moduleTensorTildeSectionsMap p M J' := by
  ext U : 2
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m j
  exact moduleTensorTildeSectionsMap_map_tmul p M f U.unop m j

/-- The original finite-product comparison followed by the actual tensor section map. -/
def moduleCechTensorTildeMap {ι : Type u} [Finite ι]
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (J : ModuleCat.{u} R)
    (U : ι → X.Opens) :
    ((tensorRight J).mapHomologicalComplex (.up ℕ)).obj
      (moduleCechComplex X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U) ⟶
    moduleCechComplex X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      ((moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J))) U :=
  (finiteCechComplexCoefficientIso (tensorRight J) U
    (moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M)).hom ≫
    (cechComplexFunctor U).map (moduleTensorTildeSectionsMap p M J)

/-- The forward Cech arrow retains the original product projections and section tensor maps. -/
theorem moduleCechTensorTildeMap_f_π {ι : Type u} [Finite ι]
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (J : ModuleCat.{u} R)
    (U : ι → X.Opens) (q : ℕ) (a : Fin (q + 1) → ι) :
    (moduleCechTensorTildeMap p M J U).f q ≫
      Pi.π (fun a : Fin (q + 1) → ι =>
        (moduleSectionsPresheaf X
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
          ((moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J)))).obj
            (op (∏ᶜ fun k => U (a k)))) a =
      (tensorRight J).map
        (Pi.π (fun a : Fin (q + 1) → ι =>
          (moduleSectionsPresheaf X
            (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M).obj
              (op (∏ᶜ fun k => U (a k)))) a) ≫
        (moduleTensorTildeSectionsMap p M J).app (op (∏ᶜ fun k => U (a k))) := by
  dsimp only [moduleCechTensorTildeMap]
  simp only [comp_f]
  change (𝟙 _ ≫ piComparison (tensorRight J)
    (fun a : Fin (q + 1) → ι =>
      (moduleSectionsPresheaf X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M).obj
          (op (∏ᶜ fun k => U (a k))))) ≫
    Limits.Pi.map (fun a : Fin (q + 1) → ι =>
      (moduleTensorTildeSectionsMap p M J).app (op (∏ᶜ fun k => U (a k)))) ≫ _ = _
  rw [Category.id_comp, Pi.map_π, ← Category.assoc, piComparison_comp_π]

/-- The actual natural-number Cech arrow commutes with every coefficient morphism. -/
theorem moduleCechTensorTildeMap_naturality_coefficients {ι : Type u} [Finite ι]
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
    {J J' : ModuleCat.{u} R} (f : J ⟶ J') (U : ι → X.Opens) :
    (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map f)
      (.up ℕ)).app (moduleCechComplex X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U) ≫
      moduleCechTensorTildeMap p M J' U =
    moduleCechTensorTildeMap p M J U ≫
      (cechComplexFunctor U).map
        ((moduleSectionsPresheafFunctor X
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).map
            ((moduleTensorLeftFunctor X M).map
              ((Scheme.Modules.pullback p).map (tilde.map f)))) := by
  dsimp only [moduleCechTensorTildeMap]
  rw [← Category.assoc, finiteCechComplexCoefficientIso_naturality_functor]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [moduleTensorTildeSectionsMap_naturality_coefficients]

private def modulePullbackRestrictionIso {V Y : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (p : X ⟶ Y) :
    Scheme.Modules.pullback p ⋙ Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.pullback (j ≫ p) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).comp
    (Scheme.Modules.restrictAdjunction j)).leftAdjointUniq
      ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ p)).ofNatIsoRight
        (Scheme.Modules.pushforwardComp j p).symm)

private theorem modulePullbackRestrictionIso_unit {V Y : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j] (p : X ⟶ Y) (N : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N ≫
      (Scheme.Modules.pushforward p).map
        ((Scheme.Modules.restrictAdjunction j).unit.app
          ((Scheme.Modules.pullback p).obj N)) ≫
      (Scheme.Modules.pushforward j ⋙ Scheme.Modules.pushforward p).map
        ((modulePullbackRestrictionIso j p).hom.app N) =
    (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ p)).unit.app N ≫
      (Scheme.Modules.pushforwardComp j p).inv.app
        ((Scheme.Modules.pullback (j ≫ p)).obj N) := by
  exact Adjunction.unit_leftAdjointUniq_hom_app
    ((Scheme.Modules.pullbackPushforwardAdjunction p).comp
      (Scheme.Modules.restrictAdjunction j))
    ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ p)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp j p).symm) N

private theorem moduleAffineChart_appTop (U : X.Opens) (hU : IsAffineOpen U) :
    hU.fromSpec.appTop = X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op ≫
      (Scheme.ΓSpecIso Γ(X, U)).inv := by
  have h := hU.fromSpec_app_of_le ⊤ le_top
  change hU.fromSpec.appTop = X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op ≫
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map (𝟙 (op ⊤)) at h
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using h

private theorem moduleAffineChart_scalars (p : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) :
    (hU.fromSpec ≫ p).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv.hom.comp
        ((globalRestriction X U).comp
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  rw [Scheme.Hom.comp_appTop, moduleAffineChart_appTop]
  rfl

private def moduleSpecSectionsIso (S : CommRingCat.{u}) (N : (Spec S).Modules) :
    (moduleSectionsPresheaf (Spec S) (Scheme.ΓSpecIso S).inv.hom N).obj (op ⊤) ≅
      (moduleSpecΓFunctor (R := S)).obj N := Iso.refl _

private def modulePullbackTildeAffineSectionIso (p : X ⟶ Spec (CommRingCat.of R))
    (J : ModuleCat.{u} R) (U : X.Opens) (hU : IsAffineOpen U) :
    (ModuleCat.extendScalars ((globalRestriction X U).comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))).obj J ≅
      ModuleCat.of Γ(X, U) Γ((Scheme.Modules.pullback p).obj (tilde J), U) := by
  let j := hU.fromSpec
  let pC := j ≫ p
  let α₀ := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := (Scheme.ΓSpecIso Γ(X, U)).inv.hom
  let σ := (globalRestriction X U).comp (p.appTop.hom.comp α₀)
  let hσ := moduleAffineChart_scalars p U hU
  letI : IsIso (CommRingCat.ofHom α₀) :=
    inferInstanceAs (IsIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)
  letI : IsIso (CommRingCat.ofHom β) :=
    inferInstanceAs (IsIso (Scheme.ΓSpecIso Γ(X, U)).inv)
  letI : IsIso (moduleTildeGlobalSectionsSeed J) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (tilde.isoTop (R := CommRingCat.of R) J).toLinearEquiv.bijective
  have hpush : IsPushout (CommRingCat.ofHom α₀) (CommRingCat.ofHom σ)
      pC.appTop (CommRingCat.ofHom β) :=
    IsPushout.of_horiz_isIso ⟨by ext r; exact DFunLike.congr_fun hσ r⟩
  letI := moduleSectionsTensorComparison_top_isIso pC α₀ β σ hσ hpush (tilde J)
  exact (ModuleCat.extendScalars σ).mapIso (asIso (moduleTildeGlobalSectionsSeed J)) ≪≫
    asIso ((moduleSectionsTensorComparison pC α₀ β σ hσ (tilde J)).app (op ⊤)) ≪≫
    moduleSpecSectionsIso Γ(X, U) ((Scheme.Modules.pullback pC).obj (tilde J)) ≪≫
    (moduleSpecΓFunctor (R := Γ(X, U))).mapIso
      ((modulePullbackRestrictionIso j p).symm.app (tilde J)) ≪≫
    affineChartΓIso ⟨U, hU⟩ ((Scheme.Modules.pullback p).obj (tilde J))

private theorem modulePullbackRestrictionIso_unit_app {V Y : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j] (p : X ⟶ Y) (N : Y.Modules) (z : Γ(N, ⊤)) :
    ((modulePullbackRestrictionIso j p).hom.app N).app ⊤
      (((Scheme.Modules.pullback p).obj N).presheaf.map
        (homOfLE (show j ''ᵁ (⊤ : V.Opens) ≤ ⊤ from le_top)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N).app ⊤ z)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ p)).unit.app N).app ⊤ z := by
  exact congrArg (fun q => q.app ⊤ z) (modulePullbackRestrictionIso_unit j p N)

private theorem modulePullbackTildeAffineSectionIso_hom_one_tmul
    (p : X ⟶ Spec (CommRingCat.of R)) (J : ModuleCat.{u} R)
    (U : X.Opens) (hU : IsAffineOpen U) (j₀ : J) :
    (modulePullbackTildeAffineSectionIso p J U hU).hom
      ((1 : Γ(X, U)) ⊗ₜ[R, (globalRestriction X U).comp
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)] j₀) =
      (modulePullbackTildeSeed p J).app (op U) j₀ := by
  let j := hU.fromSpec
  let pC := j ≫ p
  let P := (Scheme.Modules.pullback p).obj (tilde J)
  let e := (modulePullbackRestrictionIso j p).app (tilde J)
  let α₀ := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := (Scheme.ΓSpecIso Γ(X, U)).inv.hom
  let σ := (globalRestriction X U).comp (p.appTop.hom.comp α₀)
  let hσ := moduleAffineChart_scalars p U hU
  let z : Γ(tilde (R := CommRingCat.of R) J, ⊤) := tilde.toOpen (R := CommRingCat.of R) J ⊤ j₀
  have hχ := moduleSectionsTensorComparison_one_tmul pC α₀ β σ hσ (tilde J) ⊤
    (moduleTildeGlobalSectionsSeed J j₀)
  change (moduleSectionsTensorComparison pC α₀ β σ hσ (tilde J)).app (op ⊤)
    ((1 : Γ(X, U)) ⊗ₜ[R,σ] z) =
      ((Scheme.Modules.pullbackPushforwardAdjunction pC).unit.app (tilde J)).app ⊤ z at hχ
  have hu := modulePullbackRestrictionIso_unit_app j p (tilde J) z
  have hres : e.inv.app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction pC).unit.app (tilde J)).app ⊤ z) =
    P.presheaf.map (homOfLE (show j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) ≤ ⊤ from le_top)).op
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (tilde J)).app ⊤ z) := by
    have hi := congrArg (fun q => q.app ⊤
      (P.presheaf.map (homOfLE (show j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) ≤ ⊤ from le_top)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (tilde J)).app ⊤ z)))
      e.hom_inv_id
    exact (congrArg (fun w => e.inv.app ⊤ w) hu).symm.trans hi
  change (affineChartΓIso ⟨U, hU⟩ P).hom
    (e.inv.app ⊤ ((moduleSectionsTensorComparison pC α₀ β σ hσ (tilde J)).app (op ⊤)
      ((1 : Γ(X, U)) ⊗ₜ[R,σ] z))) = _
  rw [hχ, hres, modulePullbackTildeSeed_app_apply]
  change P.presheaf.map _ (P.presheaf.map _ _) = P.presheaf.map _ _
  rw [← CategoryTheory.Functor.map_comp_apply]
  exact congrArg (fun a => P.presheaf.map a
    (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (tilde J)).app ⊤ z))
    (Subsingleton.elim _ _)

private def moduleOpenSectionsIso (α : R →+* Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) :
    (moduleSectionsPresheaf X α M).obj (op U) ≅
      (ModuleCat.restrictScalars ((globalRestriction X U).comp α)).obj
        (ModuleCat.of Γ(X, U) Γ(M, U)) := Iso.refl _

private def moduleTensorTildeAffineSectionsIso (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) [M.IsQuasicoherent] (J : ModuleCat.{u} R)
    (U : X.Opens) (hU : IsAffineOpen U) :
    (tensorRight J).obj ((moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M).obj (op U)) ≅
      (moduleSectionsPresheaf X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
        ((moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J)))).obj
          (op U) := by
  let α := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let σ := (globalRestriction X U).comp α
  let T := ModuleCat.of Γ(X, U) Γ(M, U)
  let P := (Scheme.Modules.pullback p).obj (tilde J)
  let C := ModuleCat.of Γ(X, U) Γ(P, U)
  exact tensorIso (moduleOpenSectionsIso α M U) (Iso.refl J) ≪≫
    β_ ((ModuleCat.restrictScalars σ).obj T) J ≪≫
    (ModuleCat.scalarExtensionTensorIso σ J T).symm ≪≫
    (ModuleCat.restrictScalars σ).mapIso
      (tensorIso (modulePullbackTildeAffineSectionIso p J U hU) (Iso.refl T)) ≪≫
    (ModuleCat.restrictScalars σ).mapIso (β_ C T) ≪≫
    (ModuleCat.restrictScalars σ).mapIso (moduleTensorSectionIso M P U hU) ≪≫
    (moduleOpenSectionsIso α ((moduleTensorLeftFunctor X M).obj P) U).symm

private theorem moduleTensorTildeAffineSectionsIso_hom_tmul
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
    (J : ModuleCat.{u} R) (U : X.Opens) (hU : IsAffineOpen U)
    (m : (moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M).obj (op U))
    (j : J) :
    (moduleTensorTildeAffineSectionsIso p M J U hU).hom (m ⊗ₜ[R] j) =
      (moduleTensorTildeSectionsMap p M J).app (op U) (m ⊗ₜ[R] j) := by
  change moduleTensorSection X M ((Scheme.Modules.pullback p).obj (tilde J)) U m
    ((modulePullbackTildeAffineSectionIso p J U hU).hom
      ((1 : Γ(X, U)) ⊗ₜ[R, (globalRestriction X U).comp
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)] j)) = _
  rw [modulePullbackTildeAffineSectionIso_hom_one_tmul]
  rfl

/-- On an affine open, the original tensor section arrow is invertible for quasicoherent M. -/
theorem moduleTensorTildeSectionsMap_app_isIso_of_isAffine
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
    (J : ModuleCat.{u} R) (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso ((moduleTensorTildeSectionsMap p M J).app (op U)) := by
  have heq : (moduleTensorTildeAffineSectionsIso p M J U hU).hom =
      (moduleTensorTildeSectionsMap p M J).app (op U) := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m j
    exact moduleTensorTildeAffineSectionsIso_hom_tmul p M J U hU m j
  rw [← heq]
  infer_instance

/-- Affine tuple intersections make the actual Cech arrow invertible for arbitrary base modules. -/
theorem moduleCechTensorTildeMap_isIso {ι : Type u} [Finite ι]
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
    (J : ModuleCat.{u} R) (U : ι → X.Opens)
    (haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k))) :
    IsIso (moduleCechTensorTildeMap p M J U) := by
  have hn (q : ℕ) : IsIso (((cechComplexFunctor U).map
      (moduleTensorTildeSectionsMap p M J)).f q) := by
    have hi (a : Fin (q + 1) → ι) :
        IsIso ((moduleTensorTildeSectionsMap p M J).app (op (∏ᶜ fun k => U (a k)))) :=
      moduleTensorTildeSectionsMap_app_isIso_of_isAffine p M J _ (haff q a)
    let := hi
    change IsIso (Limits.Pi.map (fun a : Fin (q + 1) → ι =>
      (moduleTensorTildeSectionsMap p M J).app (op (∏ᶜ fun k => U (a k)))))
    infer_instance
  let := hn
  let := HomologicalComplex.Hom.isIso_of_components
    ((cechComplexFunctor U).map (moduleTensorTildeSectionsMap p M J))
  dsimp only [moduleCechTensorTildeMap]
  infer_instance

/-- Extend the original Cech tensor arrow by zero through its native functor comparison. -/
def moduleCechIntTensorTildeMap {ι : Type u} [Finite ι]
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (J : ModuleCat.{u} R)
    (U : ι → X.Opens) :
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).obj
      (moduleCechIntComplex X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M) ⟶
    moduleCechIntComplex X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U
      ((moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J))) :=
  ((moduleCechComplex X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U).mapExtendIso
        (tensorRight J) ComplexShape.embeddingUpNat).hom ≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map
      (moduleCechTensorTildeMap p M J U)

/-- The same integer Cech arrow is invertible on affine tuple intersections. -/
theorem moduleCechIntTensorTildeMap_isIso {ι : Type u} [Finite ι]
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
    (J : ModuleCat.{u} R) (U : ι → X.Opens)
    (haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k))) :
    IsIso (moduleCechIntTensorTildeMap p M J U) := by
  let := moduleCechTensorTildeMap_isIso p M J U haff
  dsimp only [moduleCechIntTensorTildeMap]
  infer_instance

/-- Package the original integer Cech tensor arrow as its canonical isomorphism. -/
def moduleCechIntTensorTildeIso {ι : Type u} [Finite ι]
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
    (J : ModuleCat.{u} R) (U : ι → X.Opens)
    (haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k))) :
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).obj
      (moduleCechIntComplex X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M) ≅
    moduleCechIntComplex X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U
      ((moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J))) := by
  letI := moduleCechIntTensorTildeMap_isIso p M J U haff
  exact asIso (moduleCechIntTensorTildeMap p M J U)

/-- The actual integer Cech arrow commutes with every native coefficient morphism. -/
theorem moduleCechIntTensorTildeMap_naturality_coefficients {ι : Type u} [Finite ι]
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
    {J J' : ModuleCat.{u} R} (f : J ⟶ J') (U : ι → X.Opens) :
    (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map f)
      (.up ℤ)).app (moduleCechIntComplex X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M) ≫
      moduleCechIntTensorTildeMap p M J' U =
    moduleCechIntTensorTildeMap p M J U ≫
      (moduleCechIntFunctor X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U).map
          ((moduleTensorLeftFunctor X M).map
            ((Scheme.Modules.pullback p).map (tilde.map f))) := by
  let C := moduleCechComplex X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U
  let τ : tensorRight J ⟶ tensorRight J' := (tensoringRight (ModuleCat.{u} R)).map f
  let E := ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)
  let g := (cechComplexFunctor U).map
    ((moduleSectionsPresheafFunctor X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).map
        ((moduleTensorLeftFunctor X M).map ((Scheme.Modules.pullback p).map (tilde.map f))))
  have h := C.mapExtendIso_hom_natTrans (tensorRight J) (tensorRight J') τ
    ComplexShape.embeddingUpNat
  change (NatTrans.mapHomologicalComplex τ (.up ℤ)).app
      (C.extend ComplexShape.embeddingUpNat) ≫
    ((C.mapExtendIso (tensorRight J') ComplexShape.embeddingUpNat).hom ≫
      E.map (moduleCechTensorTildeMap p M J' U)) =
    ((C.mapExtendIso (tensorRight J) ComplexShape.embeddingUpNat).hom ≫
      E.map (moduleCechTensorTildeMap p M J U)) ≫ E.map g
  rw [← Category.assoc, h]
  have hnat : (NatTrans.mapHomologicalComplex τ (.up ℕ)).app C ≫
      moduleCechTensorTildeMap p M J' U = moduleCechTensorTildeMap p M J U ≫ g :=
    moduleCechTensorTildeMap_naturality_coefficients p M f U
  have he := congrArg (fun φ =>
    (C.mapExtendIso (tensorRight J) ComplexShape.embeddingUpNat).hom ≫ E.map φ) hnat
  simpa only [E, CategoryTheory.Functor.map_comp, Category.assoc,
    ComplexShape.Embedding.extendFunctor_map, HomologicalComplex.extendMap_comp] using he

section Bounded
variable {ι : Type u} [Finite ι] [X.IsSeparated]
  (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
  (J : ModuleCat.{u} R) (U : ι → X.Opens) (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
  [Module.Flat R ((moduleCechIntComplex X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M).X ((n : ℤ) + 1))]
  [Module.Flat R ((moduleCechIntComplex X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M).X ((n : ℤ) + 2))]

/-- The same native finite good Cech model commutes with arbitrary coefficient tensoring. -/
def moduleFiniteCechTensorTildeIso :
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).obj
      (moduleFiniteCechComplex X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n) ≅
    moduleFiniteCechComplex X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U
      ((moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J))) n := by
  letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let K := moduleCechIntComplex X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M
  have haff (q : ℕ) (a : Fin (q + 1) → ι) : IsAffineOpen (∏ᶜ fun k => U (a k)) := by
    have h : (∏ᶜ fun k => U (a k)) = ⨅ k, U (a k) := by
      apply le_antisymm
      · exact le_iInf fun k => leOfHom (Pi.π _ k)
      · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
    rw [h]
    exact IsAffineOpen.iInf (fun k => hU (a k))
  exact CochainComplex.tensorRightTruncLEIso J K (n : ℤ)
      (moduleCechIntComplex_universally_lTensor_exact p M U n e hU hcover) ≪≫
    ((ComplexShape.embeddingUpIntLE (n : ℤ)).truncLEFunctor (ModuleCat.{u} R)).mapIso
      (moduleCechIntTensorTildeIso p M J U haff)

/-- The bounded comparison retains the literal tensor of the original truncation inclusion. -/
@[reassoc]
theorem moduleFiniteCechTensorTildeIso_hom_ιTruncLE :
    (moduleFiniteCechTensorTildeIso p M J U n e hU hcover).hom ≫
      moduleFiniteCechInclusion X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U
        ((moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J))) n =
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).map
      (moduleFiniteCechInclusion X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n) ≫
      moduleCechIntTensorTildeMap p M J U := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let K := moduleCechIntComplex X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M
  let L := moduleCechIntComplex X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U
    ((moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J)))
  let θ : ((tensorRight J).mapHomologicalComplex (.up ℤ)).obj K ⟶ L :=
    moduleCechIntTensorTildeMap p M J U
  change ((CochainComplex.tensorRightTruncLEIso J K (n : ℤ)
      (moduleCechIntComplex_universally_lTensor_exact p M U n e hU hcover)).hom ≫
    CochainComplex.truncLEMap θ (n : ℤ)) ≫ L.ιTruncLE (n : ℤ) =
      ((tensorRight J).mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE (n : ℤ)) ≫ θ
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality, ← Category.assoc,
    CochainComplex.tensorRightTruncLEIso_hom_ιTruncLE]

include e hU hcover
/-- The literal bounded-model arrow computes the ordinary tensor coefficient Cech complex. -/
theorem moduleFiniteCechTensorTildeInclusion_quasiIso :
    QuasiIso (((tensorRight J).mapHomologicalComplex (.up ℤ)).map
      (moduleFiniteCechInclusion X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n) ≫
      moduleCechIntTensorTildeMap p M J U) := by
  rw [← moduleFiniteCechTensorTildeIso_hom_ιTruncLE p M J U n e hU hcover]
  let P := (Scheme.Modules.pullback p).obj (tilde J)
  let N := (moduleTensorLeftFunctor X M).obj P
  let : N.IsQuasicoherent := isQuasicoherent_moduleTensorLeftFunctor M P
  let := moduleFiniteCechInclusion_quasiIso X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U N n e hU hcover
  infer_instance

/-- The original finite-model isomorphism commutes with every native coefficient morphism. -/
theorem moduleFiniteCechTensorTildeIso_naturality_coefficients
    {J' : ModuleCat.{u} R} (f : J ⟶ J') :
    (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map f)
      (.up ℤ)).app (moduleFiniteCechComplex X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n) ≫
      (moduleFiniteCechTensorTildeIso p M J' U n e hU hcover).hom =
    (moduleFiniteCechTensorTildeIso p M J U n e hU hcover).hom ≫
      (moduleFiniteCechFunctor X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U n).map
          ((moduleTensorLeftFunctor X M).map
            ((Scheme.Modules.pullback p).map (tilde.map f))) := by
  let α := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let N' := (moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J'))
  let : Mono (moduleFiniteCechInclusion X α U N' n) := by
    change Mono (HomologicalComplex.ιTruncLE (moduleCechIntComplex X α U N')
      (ComplexShape.embeddingUpIntLE (n : ℤ)))
    infer_instance
  apply (cancel_mono (moduleFiniteCechInclusion X α U N' n)).mp
  simp only [Category.assoc]
  rw [moduleFiniteCechTensorTildeIso_hom_ιTruncLE,
    moduleFiniteCechInclusion_naturality,
    moduleFiniteCechTensorTildeIso_hom_ιTruncLE_assoc]
  have hn := (NatTrans.mapHomologicalComplex
    ((tensoringRight (ModuleCat.{u} R)).map f) (.up ℤ)).naturality
      (moduleFiniteCechInclusion X α U M n)
  have h₀ := congrArg (fun φ => φ ≫ moduleCechIntTensorTildeMap p M J' U) hn
  have h₁ := congrArg (fun φ =>
    ((tensorRight J).mapHomologicalComplex (.up ℤ)).map
      (moduleFiniteCechInclusion X α U M n) ≫ φ)
    (moduleCechIntTensorTildeMap_naturality_coefficients p M f U)
  exact (by simpa only [Category.assoc] using h₀.symm.trans h₁)

end Bounded
private theorem modulePullbackTildeSeed_self_one (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    (pullbackUnitIso p).hom.app U
      ((modulePullbackTildeSeed p (ModuleCat.of R R)).app (op U) (1 : R)) = (1 : Γ(X, U)) := by
  have hu := pullbackUnitIso_homEquiv p
  change (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
      (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) ≫
    (Scheme.Modules.pushforward p).map (pullbackUnitIso p).hom =
      SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom at hu
  have h₁ := congrArg (fun q => q.app ⊤ (1 : Γ(Spec (CommRingCat.of R), ⊤))) hu
  change (pullbackUnitIso p).hom.app ⊤
    (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
      (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf)).app ⊤
        (1 : Γ(Spec (CommRingCat.of R), ⊤))) = p.appTop 1 at h₁
  let i := (homOfLE (show U ≤ p ⁻¹ᵁ ⊤ by simp)).op
  have hn := PresheafOfModules.naturality_apply (pullbackUnitIso p).hom.val i
    (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
      (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf)).app ⊤
        (1 : Γ(Spec (CommRingCat.of R), ⊤)))
  rw [modulePullbackTildeSeed_app_apply, tilde_toOpen_self_one]
  refine hn.trans ?_
  change X.presheaf.map i ((pullbackUnitIso p).hom.app ⊤
    (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
      (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf)).app ⊤
        (1 : Γ(Spec (CommRingCat.of R), ⊤)))) = 1
  rw [h₁, map_one, map_one]

/-- For the base ring, the original pullback unit gives the original structural scalar. -/
theorem modulePullbackTildeSeed_self_apply (p : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (r : R) :
    (pullbackUnitIso p).hom.app U
      ((modulePullbackTildeSeed p (ModuleCat.of R R)).app (op U) r) =
    globalRestriction X U
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
  let α := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let a := (modulePullbackTildeSeed p (ModuleCat.of R R)).app (op U) ≫
    ((moduleSectionsPresheafFunctor X α).map (pullbackUnitIso p).hom).app (op U)
  have h₁ : a (1 : R) = (1 : Γ(X, U)) := modulePullbackTildeSeed_self_one p U
  have hs := a.hom.map_smul r (1 : R)
  change a (r * 1) = globalRestriction X U (α r) * (show Γ(X, U) from a (1 : R)) at hs
  change a r = globalRestriction X U (α r)
  simpa only [mul_one, h₁] using hs

/-- The original pullback-unit and right tensor unitor identify the ring coefficient with M. -/
def moduleTensorPullbackTildeSelfIso (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) :
    (moduleTensorLeftFunctor X M).obj
      ((Scheme.Modules.pullback p).obj (tilde (ModuleCat.of R R))) ≅ M :=
  (moduleTensorLeftFunctor X M).mapIso (pullbackUnitIso p) ≪≫
    (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app M

/-- The original unit isomorphism recovers multiplication by the original base scalar. -/
theorem moduleTensorPullbackTildeSelfIso_hom_tmul
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (U : X.Opens)
    (m : (moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M).obj (op U))
    (r : R) :
    (moduleTensorPullbackTildeSelfIso p M).hom.app U
      ((moduleTensorTildeSectionsMap p M (ModuleCat.of R R)).app (op U) (m ⊗ₜ[R] r)) =
      r • m := by
  change ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app M).val.app (op U)
    (((moduleTensorLeftFunctor X M).map (pullbackUnitIso p).hom).app U
      (moduleTensorSection X M ((Scheme.Modules.pullback p).obj (tilde (ModuleCat.of R R)))
        U m ((modulePullbackTildeSeed p (ModuleCat.of R R)).app (op U) r))) = _
  have hmap := moduleTensorLeftFunctor_map_section (X := X) M (pullbackUnitIso p).hom U m
    ((modulePullbackTildeSeed p (ModuleCat.of R R)).app (op U) r)
  have hγ := modulePullbackTildeSeed_self_apply p U r
  have ht := tensorRightUnitIso_hom_section X M U m
    (globalRestriction X U (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
  exact (congrArg (fun z =>
    ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app M).val.app (op U) z)
    hmap).trans ((congrArg (fun z =>
      ((SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).hom.app M).val.app (op U)
        (moduleTensorSection X M (SheafOfModules.unit X.ringCatSheaf) U m z)) hγ).trans ht)

/-- The ring-coefficient section map is the native right unitor after the geometric units. -/
theorem moduleTensorTildeSectionsMap_self (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) :
    moduleTensorTildeSectionsMap p M (ModuleCat.of R R) ≫
      (moduleSectionsPresheafFunctor X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).map
          (moduleTensorPullbackTildeSelfIso p M).hom =
    Functor.whiskerLeft (moduleSectionsPresheaf X
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M)
        (rightUnitorNatIso (ModuleCat.{u} R)).hom := by
  ext U : 2
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m r
  exact (moduleTensorPullbackTildeSelfIso_hom_tmul p M U.unop m r).trans
    (ModuleCat.MonoidalCategory.rightUnitor_hom_apply m r).symm

/-- The ring-coefficient Cech comparison is exactly the native cochain right-unitor map. -/
theorem moduleCechTensorTildeMap_self {ι : Type u} [Finite ι]
    (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (U : ι → X.Opens) :
    moduleCechTensorTildeMap p M (ModuleCat.of R R) U ≫
      (cechComplexFunctor U).map
        ((moduleSectionsPresheafFunctor X
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).map
            (moduleTensorPullbackTildeSelfIso p M).hom) =
    (NatTrans.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R)).hom (.up ℕ)).app
      (moduleCechComplex X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U) := by
  let P := moduleSectionsPresheaf X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M
  dsimp only [moduleCechTensorTildeMap]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, moduleTensorTildeSectionsMap_self]
  ext q : 1
  apply Pi.hom_ext
  intro a
  simp only [comp_f, NatTrans.mapHomologicalComplex_app_f]
  change ((𝟙 _ ≫ piComparison (tensorRight (ModuleCat.of R R))
    (fun a : Fin (q + 1) → ι => P.obj (op (∏ᶜ fun k => U (a k))))) ≫
      Limits.Pi.map (fun a : Fin (q + 1) → ι =>
        (ρ_ (P.obj (op (∏ᶜ fun k => U (a k))))).hom)) ≫
    Pi.π (fun a : Fin (q + 1) → ι => P.obj (op (∏ᶜ fun k => U (a k)))) a =
    (ρ_ (∏ᶜ fun a : Fin (q + 1) → ι => P.obj (op (∏ᶜ fun k => U (a k))))).hom ≫
      Pi.π (fun a : Fin (q + 1) → ι => P.obj (op (∏ᶜ fun k => U (a k)))) a
  simp only [Category.id_comp, Category.assoc, Pi.map_π]
  rw [← Category.assoc, piComparison_comp_π]
  exact (rightUnitorNatIso (ModuleCat.{u} R)).hom.naturality
    (Pi.π (fun a : Fin (q + 1) → ι => P.obj (op (∏ᶜ fun k => U (a k)))) a)

section SelfComplexes

variable {ι : Type u} [Finite ι]
  (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (U : ι → X.Opens)

/-- The original integer Cech coefficient map at the ring is the native right unitor. -/
@[reassoc]
theorem moduleCechIntTensorTildeMap_self :
    moduleCechIntTensorTildeMap p M (ModuleCat.of R R) U ≫
      (moduleCechIntFunctor X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U).map
          (moduleTensorPullbackTildeSelfIso p M).hom =
    (NatTrans.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R)).hom (.up ℤ)).app
      (moduleCechIntComplex X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M) := by
  let C := moduleCechComplex X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U
  let τ : tensorRight (ModuleCat.of R R) ⟶ 𝟭 (ModuleCat.{u} R) :=
    (rightUnitorNatIso (ModuleCat.{u} R)).hom
  let E := ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)
  have hid :
      (C.mapExtendIso (𝟭 (ModuleCat.{u} R)) ComplexShape.embeddingUpNat).hom = 𝟙 _ := by
    ext j : 1
    change (HomologicalComplex.extend.mapXIso C (𝟭 (ModuleCat.{u} R))
      (ComplexShape.embeddingUpNat.r j)).hom = 𝟙 _
    generalize ComplexShape.embeddingUpNat.r j = a
    cases a with
    | none => exact (isZero_zero (ModuleCat.{u} R)).eq_of_tgt _ _
    | some i => rfl
  have hτ := C.mapExtendIso_hom_natTrans (tensorRight (ModuleCat.of R R))
    (𝟭 (ModuleCat.{u} R)) τ ComplexShape.embeddingUpNat
  rw [hid, Category.comp_id] at hτ
  have hC := moduleCechTensorTildeMap_self p M U
  have hE := congrArg (fun q =>
    (C.mapExtendIso (tensorRight (ModuleCat.of R R)) ComplexShape.embeddingUpNat).hom ≫
      E.map q) hC
  dsimp only [moduleCechIntTensorTildeMap]
  change (C.mapExtendIso (tensorRight (ModuleCat.of R R)) ComplexShape.embeddingUpNat).hom ≫
    HomologicalComplex.extendMap (moduleCechTensorTildeMap p M (ModuleCat.of R R) U)
      ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      ((cechComplexFunctor U).map
        ((moduleSectionsPresheafFunctor X
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).map
          (moduleTensorPullbackTildeSelfIso p M).hom)) ComplexShape.embeddingUpNat =
    (NatTrans.mapHomologicalComplex τ (.up ℤ)).app (C.extend ComplexShape.embeddingUpNat)
  have hE' := hE.trans hτ.symm
  simpa only [E, CategoryTheory.Functor.map_comp, Category.assoc,
    ComplexShape.Embedding.extendFunctor_obj, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_comp] using hE'

variable [X.IsSeparated] [M.IsQuasicoherent]
  (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
  [Module.Flat R ((moduleCechIntComplex X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M).X ((n : ℤ) + 1))]
  [Module.Flat R ((moduleCechIntComplex X
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M).X ((n : ℤ) + 2))]

/-- The original finite Cech coefficient isomorphism at the ring is the native right unitor. -/
@[reassoc]
theorem moduleFiniteCechTensorTildeIso_self :
    (moduleFiniteCechTensorTildeIso p M (ModuleCat.of R R) U n e hU hcover).hom ≫
      (moduleFiniteCechFunctor X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U n).map
          (moduleTensorPullbackTildeSelfIso p M).hom =
    (NatTrans.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R)).hom (.up ℤ)).app
      (moduleFiniteCechComplex X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n) := by
  let α := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let K := moduleCechIntComplex X α U M
  let i := moduleFiniteCechInclusion X α U M n
  let : Mono i := by
    change Mono (HomologicalComplex.ιTruncLE K (ComplexShape.embeddingUpIntLE (n : ℤ)))
    infer_instance
  apply (cancel_mono i).mp
  simp only [Category.assoc]
  rw [moduleFiniteCechInclusion_naturality, ← Category.assoc]
  rw [moduleFiniteCechTensorTildeIso_hom_ιTruncLE, Category.assoc,
    moduleCechIntTensorTildeMap_self]
  exact (NatTrans.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R)).hom
    (.up ℤ)).naturality i

end SelfComplexes

section TensorAugmentation

variable {ι : Type u} [Finite ι]
  (p : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) (J : ModuleCat.{u} R)
  (U : ι → X.Opens)

/-- Tensoring the original Cech augmentation is the original top-section tensor map followed
by the original coefficient augmentation, through the native single-tensor comparison. -/
@[reassoc]
theorem moduleCechTensorTildeMap_augmentation :
    ((tensorRight J).mapHomologicalComplex (.up ℕ)).map
        (moduleCechAugmentation X
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U) ≫
      moduleCechTensorTildeMap p M J U =
    (HomologicalComplex.singleMapHomologicalComplex (tensorRight J) (.up ℕ) (0 : ℕ)).hom.app
        ((moduleSectionsPresheaf X
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M).obj (op ⊤)) ≫
      (CochainComplex.single₀ (ModuleCat.{u} R)).map
        ((moduleTensorTildeSectionsMap p M J).app (op ⊤)) ≫
      moduleCechAugmentation X
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
        ((moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J))) U := by
  let α := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let P := moduleSectionsPresheaf X α M
  let N := (moduleTensorLeftFunctor X M).obj ((Scheme.Modules.pullback p).obj (tilde J))
  let F := tensorRight J
  let a := (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) (0 : ℕ)).app
    (P.obj (op ⊤))
  change ((F.mapHomologicalComplex (.up ℕ)).map (moduleCechAugmentation X α M U)) ≫
      moduleCechTensorTildeMap p M J U =
    a.hom ≫ (CochainComplex.single₀ (ModuleCat.{u} R)).map
      ((moduleTensorTildeSectionsMap p M J).app (op ⊤)) ≫ moduleCechAugmentation X α N U
  apply (cancel_epi a.inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  ext q : 1
  cases q with
  | zero =>
    have ha : a.inv.f 0 = 𝟙 (F.obj (P.obj (op ⊤))) := by
      change ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) (0 : ℕ)).inv.app
        (P.obj (op ⊤))).f 0 = _
      rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
      simp [singleObjXSelf, singleObjXIsoOfEq]
    simp only [comp_f, Category.assoc]
    change a.inv.f 0 ≫ F.map (cechAugmentationZero X U P) ≫
        (moduleCechTensorTildeMap p M J U).f 0 =
      (moduleTensorTildeSectionsMap p M J).app (op ⊤) ≫
        cechAugmentationZero X U (moduleSectionsPresheaf X α N)
    rw [ha]
    erw [Category.id_comp]
    apply Pi.hom_ext (f := fun b : Fin 1 → ι =>
      (moduleSectionsPresheaf X α N).obj (op (∏ᶜ fun k => U (b k))))
    intro b
    simp only [Category.assoc]
    erw [moduleCechTensorTildeMap_f_π, ← Category.assoc, ← Functor.map_comp,
      cechAugmentationZero_π, cechAugmentationZero_π]
    exact (moduleTensorTildeSectionsMap p M J).naturality
      ((homOfLE (show (∏ᶜ fun k => U (b k)) ≤ ⊤ from le_top)).op)
  | succ q =>
    exact (isZero_single_obj_X (.up ℕ) (0 : ℕ) (F.obj (P.obj (op ⊤))) (q + 1)
      (by omega)).eq_of_src _ _

end TensorAugmentation

end AlgebraicGeometry.Scheme.Cohomology
