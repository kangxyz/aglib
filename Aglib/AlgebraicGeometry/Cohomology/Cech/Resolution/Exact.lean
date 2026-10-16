/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Resolution.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Affine.PushforwardAcyclicity
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.Grp.AB

/-!
# The genuine module-valued Cech resolution zigzag

Injective module coefficients make the original Cech rows exact. For a
quasicoherent coefficient, sections of its actual module injective resolution
are exact on affine opens. Products of these actual columns are exact.
The two original augmentations therefore give quasi-isomorphisms to the same
native module-valued total complex.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open AlgebraicGeometry TopologicalSpace Opposite CategoryTheory.Cech

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
  {ι : Type u} (U : ι → X.Opens)

/-- Injectivity in the original module category gives positive Cech exactness over `R`. -/
theorem moduleInjectiveCech_exact_succ (M : X.Modules) [Injective M] (n : ℕ) :
    (moduleCechComplex X α M U).ExactAt (n + 1) := by
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  apply (ShortComplex.exact_map_iff_of_faithful _ F).mp
  exact (Scheme.Modules.injectiveCech_exact_succ X M U n).of_iso
    (moduleCechForgetIso X α M U).symm

/-- The original restriction augmentation is a quasi-isomorphism for injective modules. -/
theorem moduleInjectiveCechAugmentation_quasiIso (M : X.Modules) [Injective M]
    (hcover : iSup U = ⊤) : QuasiIso (moduleCechAugmentation X α M U) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => exact moduleCechAugmentation_quasiIsoAt_zero X α M U hcover
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ n)]
    exact moduleInjectiveCech_exact_succ X α U M n

instance moduleSectionsPresheafFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (moduleSectionsPresheafFunctor X α) := by
  apply preservesFiniteLimits_of_evaluation
  intro V
  let ρ : Γ(X, ⊤) →+* Γ(X, V.unop) :=
    (X.ringCatSheaf.obj.map ((isTerminalTop (α := X.Opens)).op.to V)).hom
  let F : X.Modules ⥤ ModuleCat.{u} R :=
    SheafOfModules.evaluation X.ringCatSheaf V ⋙
      ModuleCat.restrictScalars ρ ⋙ ModuleCat.restrictScalars α
  let e : moduleSectionsPresheafFunctor X α ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj V ≅ F :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; ext x; rfl)
  let : (ModuleCat.restrictScalars.{u} ρ).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} ρ).isRightAdjoint
  let : (ModuleCat.restrictScalars.{u} α).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} α).isRightAdjoint
  let : PreservesFiniteLimits (SheafOfModules.evaluation.{u} X.ringCatSheaf V) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf V
  let : PreservesFiniteLimits F := by
    dsimp only [F]
    infer_instance
  exact preservesFiniteLimits_of_natIso e.symm

/-- The original structural-ring Cech term in degree `p`. -/
def moduleCechDegreeFunctor (p : ℕ) :=
  moduleCechFunctor X α U ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) p

instance (p : ℕ) : (moduleCechDegreeFunctor X α U p).Additive := by
  dsimp [moduleCechDegreeFunctor]
  infer_instance

/-- The actual family of structural-ring sections on degree-`p` tuple intersections. -/
def moduleCechSectionFamilyFunctor (p : ℕ) :=
  moduleSectionsPresheafFunctor X α ⋙
    (Functor.whiskeringLeft _ _ _).obj (cechTupleOpens X U p)

instance (p : ℕ) : (moduleCechSectionFamilyFunctor X α U p).Additive := by
  dsimp [moduleCechSectionFamilyFunctor]
  infer_instance

instance (p : ℕ) : PreservesFiniteLimits (moduleCechSectionFamilyFunctor X α U p) := by
  dsimp [moduleCechSectionFamilyFunctor]
  infer_instance

/-- A Cech term is the native product of its actual section modules. -/
def moduleCechDegreeIsoLimit (p : ℕ) :
    moduleCechDegreeFunctor X α U p ≅ moduleCechSectionFamilyFunctor X α U p ⋙ lim := by
  refine NatIso.ofComponents
    (fun M ↦ Pi.isoLimit ((moduleCechSectionFamilyFunctor X α U p).obj M)) ?_
  intro M N f
  apply limit.hom_ext
  rintro ⟨a⟩
  simp only [Category.assoc, Functor.comp_map, Pi.isoLimit_hom_π, lim_map, limMap_π,
    Pi.isoLimit_hom_π_assoc]
  change ((moduleCechFunctor X α U).map f).f p ≫ Pi.π _ a =
    Pi.π _ a ≫ ((moduleSectionsPresheafFunctor X α).map f).app _
  simp [moduleCechFunctor, cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
    FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
    AlgebraicTopology.AlternatingCofaceMapComplex.map, Pi.map_π]

instance (p : ℕ) : PreservesFiniteLimits (moduleCechDegreeFunctor X α U p) :=
  preservesFiniteLimits_of_natIso (moduleCechDegreeIsoLimit X α U p).symm

variable {M : X.Modules} (I : InjectiveResolution M)

/-- Left exactness gives the actual module-resolution column augmentation in degree zero. -/
theorem moduleCechColumnAugmentation_quasiIsoAt_zero (p : ℕ) :
    QuasiIsoAt ((moduleCechColumnAugmentation X α U I).f p) 0 := by
  let F := moduleCechDegreeFunctor X α U p
  have hi : IsIso (I.toRightDerivedZero' F) := inferInstance
  have hh := (CochainComplex.isIso_liftCycles_iff
    ((F.mapHomologicalComplex _).obj I.cocomplex) (F.map (I.ι.f 0))
      (by dsimp; rw [← F.map_comp, I.ι_f_zero_comp_complex_d, F.map_zero])).mp hi
  have : Mono (((moduleCechColumnAugmentation X α U I).f p).f 0) := by
    rw [moduleCechColumnAugmentation_f_zero]
    exact hh.2
  apply CochainComplex.quasiIsoAtZero_of_augmentation_exact
  simpa [F, moduleCechDegreeFunctor, moduleCechResolution, HomologicalComplex₂.flip,
    Functor.mapHomologicalComplex, HomologicalComplex.eval] using hh.1

/-- Products of the actual affine-open module-resolution columns are exact in positive degree. -/
theorem moduleCechResolution_column_exact_succ [M.IsQuasicoherent]
    (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k ↦ U (a k)))
    (p n : ℕ) : ((moduleCechResolution X α U I).X p).ExactAt (n + 1) := by
  let G := moduleCechSectionFamilyFunctor X α U p
  let T := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let : HasExactLimitsOfShape (Discrete (Fin (p + 1) → ι)) (ModuleCat.{u} R) :=
    HasExactLimitsOfShape.domain_of_functor _ F
  have hT : T.ExactAt (n + 1) := by
    rw [exactAt_iff_isZero_homology]
    apply Functor.isZero
    intro a
    let E := (CategoryTheory.evaluation (Discrete (Fin (p + 1) → ι))
      (ModuleCat.{u} R)).obj a
    have he : ((T.sc (n + 1)).map E).Exact := by
      apply (ShortComplex.exact_map_iff_of_faithful _ F).mp
      exact Scheme.Modules.isAffineOpen_injectiveResolution_exact_succ
        (∏ᶜ fun k ↦ U (a.as k)) (haff p a.as) M I n
    have he' : ((E.mapHomologicalComplex _).obj T).ExactAt (n + 1) := he
    exact he'.isZero_homology.of_iso ((T.sc (n + 1)).mapHomologyIso E).symm
  have hprod : ((lim.mapHomologicalComplex (.up ℕ)).obj T).ExactAt (n + 1) :=
    hT.map (lim (J := Discrete (Fin (p + 1) → ι)) (C := ModuleCat.{u} R))
  let e : (((moduleCechDegreeFunctor X α U p).mapHomologicalComplex _).obj I.cocomplex) ≅
      ((lim.mapHomologicalComplex (.up ℕ)).obj T) :=
    (NatIso.mapHomologicalComplex (moduleCechDegreeIsoLimit X α U p) _).app I.cocomplex ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ lim)) _).app I.cocomplex).symm
  exact hprod.of_iso e.symm

/-- Affine tuple intersections give quasi-isomorphisms of the original column augmentations. -/
theorem moduleCechColumnAugmentation_quasiIso [M.IsQuasicoherent]
    (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k ↦ U (a k)))
    (p : ℕ) : QuasiIso ((moduleCechColumnAugmentation X α U I).f p) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => exact moduleCechColumnAugmentation_quasiIsoAt_zero X α U I p
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ n)]
    exact moduleCechResolution_column_exact_succ X α U I haff p n

/-- A cover makes every original injective-module row augmentation a quasi-isomorphism. -/
theorem moduleCechRowAugmentation_quasiIso (hcover : iSup U = ⊤) (q : ℕ) :
    QuasiIso ((moduleCechRowAugmentation X α U I).f q) :=
  moduleInjectiveCechAugmentation_quasiIso X α U (I.cocomplex.X q) hcover

/-- Actual global sections of the actual module resolution compute the same native total. -/
theorem moduleResolutionSectionsToTotal_quasiIso (hcover : iSup U = ⊤) :
    QuasiIso (moduleResolutionSectionsToTotal X α U I) := by
  let := quasiIso_totalAugmentationFlip _ (moduleCechRowAugmentation_quasiIso X α U I hcover)
  exact inferInstanceAs (QuasiIso ((moduleResolutionTopSectionsIso X α I).inv ≫
    totalAugmentationFlip (moduleCechRowAugmentation X α U I)))

/-- The original Cech complex computes that total for quasicoherent affine-intersection data. -/
theorem moduleCechToTotal_quasiIso [M.IsQuasicoherent]
    (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k ↦ U (a k))) :
    QuasiIso (moduleCechToTotal X α U I) :=
  quasiIso_totalAugmentation _ (moduleCechColumnAugmentation_quasiIso X α U I haff)

end AlgebraicGeometry.Scheme.Cohomology
