/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ScalarMate
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineSheaf
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Isomorphisms

/-!
# The actual nonflat higher-image comparison over affine bases

The local comparison is formed from the original geometric cohomology arrow,
the original affine higher-image section equivalences, and the native scalar
adjunction on the small section modules. Native associated-sheaf counits then
give an actual morphism of the original higher direct images. Its normalization
is the unchanged cohomology tensor map, for arbitrary scalar change.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

open Cohomology

section Affine

variable {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
  (p : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R) (σ : R ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b] [QuasiSeparated b]
  (w : p ≫ f = b ≫ Spec.map σ)
  {M : X.Modules} {N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  (ψ : M ⟶ (pushforward p).obj N) (n : ℕ)

/-- The native small tensor mate of the original geometric cohomology arrow. -/
def higherDirectImageAffineSectionsTensorMap :
    (ModuleCat.extendScalars σ.hom).obj
        (moduleSpecΓFunctor.obj (((pushforward f).rightDerived n).obj M)) ⟶
      moduleSpecΓFunctor.obj (((pushforward b).rightDerived n).obj N) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
  letI := moduleCohomologyModuleOfHom X α M n
  letI := moduleCohomologyModuleOfHom Y β N n
  exact Nonflat.smallTensorMap σ.hom
    (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n)
    (moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) n)
    (moduleCohomologyRestrictionMap p σ.hom α β
      (moduleSectionsBaseChangeScalars p b f σ.hom w) ψ n)

set_option maxRecDepth 2000 in
-- The original cohomology module action crosses the native and Ext universes here.
/-- The actual small tensor mate carries a unit pure tensor to the original geometric
cohomology arrow through the original affine higher-image section comparisons. -/
theorem higherDirectImageAffineSectionsTensorMap_one_tmul
    (x : moduleSpecΓFunctor.obj (((pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) n
        (higherDirectImageAffineSectionsTensorMap p b f σ w ψ n
          ((1 : S) ⊗ₜ[R,σ.hom] x)) =
      moduleCohomologyMapAlong p ψ n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n x) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y β N n
  exact Nonflat.smallTensorMap_one_tmul σ.hom
    (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n)
    (moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) n)
    (moduleCohomologyRestrictionMap p σ.hom α β
      (moduleSectionsBaseChangeScalars p b f σ.hom w) ψ n) x

/-- Invertibility of the actual small section mate is exactly invertibility of the original
geometric cohomology tensor map. No flatness or finite-generation hypothesis is used. -/
theorem higherDirectImageAffineSectionsTensorMap_isIso_iff :
    IsIso (higherDirectImageAffineSectionsTensorMap p b f σ w ψ n) ↔
      IsIso (moduleCohomologyTensorMap p σ.hom
        (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
        (b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom)
        (moduleSectionsBaseChangeScalars p b f σ.hom w) ψ n) := by
  exact Nonflat.smallTensorMap_isIso_iff σ.hom _ _ _

/-- Surjectivity of the actual small section mate is exactly surjectivity of the original
geometric cohomology tensor map. -/
theorem higherDirectImageAffineSectionsTensorMap_epi_iff :
    Epi (higherDirectImageAffineSectionsTensorMap p b f σ w ψ n) ↔
      Epi (moduleCohomologyTensorMap p σ.hom
        (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
        (b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom)
        (moduleSectionsBaseChangeScalars p b f σ.hom w) ψ n) := by
  exact Nonflat.smallTensorMap_epi_iff σ.hom _ _ _

/-- The actual affine sheaf comparison obtained from the small scalar mate and the native
pullback and associated-sheaf counits. -/
def higherDirectImageAffineMap :
    (pullback (Spec.map σ)).obj (((pushforward f).rightDerived n).obj M) ⟶
      ((pushforward b).rightDerived n).obj N := by
  let E := ((pushforward f).rightDerived n).obj M
  let F := ((pushforward b).rightDerived n).obj N
  letI : E.IsQuasicoherent := moduleHigherDirectImageAffine_isQuasicoherent f M n
  exact Nonflat.affineMapFromTensor σ E F
    (higherDirectImageAffineSectionsTensorMap p b f σ w ψ n)

/-- The actual affine sheaf comparison has exactly the original small tensor mate as its
global-section map through the installed native affine pullback comparison. -/
@[reassoc]
theorem higherDirectImageAffineMap_sections :
    let := moduleHigherDirectImageAffine_isQuasicoherent f M n
    (affinePullbackGlobalSectionsIso σ (((pushforward f).rightDerived n).obj M)).hom ≫
      moduleSpecΓFunctor.map (higherDirectImageAffineMap p b f σ w ψ n) =
        higherDirectImageAffineSectionsTensorMap p b f σ w ψ n := by
  let E := ((pushforward f).rightDerived n).obj M
  let F := ((pushforward b).rightDerived n).obj N
  let t := higherDirectImageAffineSectionsTensorMap p b f σ w ψ n
  let : E.IsQuasicoherent := moduleHigherDirectImageAffine_isQuasicoherent f M n
  exact Nonflat.affineMapFromTensor_sections σ E F t

/-- The actual affine sheaf comparison sends a geometric unit pure tensor to the original
geometric cohomology arrow under the original affine section equivalences. -/
theorem higherDirectImageAffineMap_one_tmul
    (x : moduleSpecΓFunctor.obj (((pushforward f).rightDerived n).obj M)) :
    let := moduleHigherDirectImageAffine_isQuasicoherent f M n
    moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) n
      (moduleSpecΓFunctor.map (higherDirectImageAffineMap p b f σ w ψ n)
        ((affinePullbackGlobalSectionsIso σ
          (((pushforward f).rightDerived n).obj M)).hom ((1 : S) ⊗ₜ[R,σ.hom] x))) =
      moduleCohomologyMapAlong p ψ n
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n x) := by
  let := moduleHigherDirectImageAffine_isQuasicoherent f M n
  dsimp only
  have hs := ConcreteCategory.congr_hom (higherDirectImageAffineMap_sections p b f σ w ψ n)
    ((1 : S) ⊗ₜ[R,σ.hom] x)
  change moduleSpecΓFunctor.map (higherDirectImageAffineMap p b f σ w ψ n)
      ((affinePullbackGlobalSectionsIso σ
        (((pushforward f).rightDerived n).obj M)).hom ((1 : S) ⊗ₜ[R,σ.hom] x)) =
    higherDirectImageAffineSectionsTensorMap p b f σ w ψ n ((1 : S) ⊗ₜ[R,σ.hom] x) at hs
  rw [hs]
  exact higherDirectImageAffineSectionsTensorMap_one_tmul p b f σ w ψ n x

/-- An isomorphism of the original geometric cohomology tensor map makes the actual affine
higher-image sheaf comparison an isomorphism. -/
theorem higherDirectImageAffineMap_isIso
    (h : IsIso (moduleCohomologyTensorMap p σ.hom
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
      (b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom)
      (moduleSectionsBaseChangeScalars p b f σ.hom w) ψ n)) :
    IsIso (higherDirectImageAffineMap p b f σ w ψ n) := by
  let := (higherDirectImageAffineSectionsTensorMap_isIso_iff p b f σ w ψ n).mpr h
  let := moduleHigherDirectImageAffine_isQuasicoherent f M n
  let := moduleHigherDirectImageAffine_isQuasicoherent b N n
  dsimp only [higherDirectImageAffineMap, Nonflat.affineMapFromTensor]
  infer_instance

/-- The actual affine sheaf comparison is invertible exactly when its original geometric
cohomology tensor mate is invertible. -/
theorem higherDirectImageAffineMap_isIso_iff :
    IsIso (higherDirectImageAffineMap p b f σ w ψ n) ↔
      IsIso (moduleCohomologyTensorMap p σ.hom
        (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
        (b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom)
        (moduleSectionsBaseChangeScalars p b f σ.hom w) ψ n) := by
  constructor
  · intro h
    let := h
    let := moduleHigherDirectImageAffine_isQuasicoherent f M n
    have ht : IsIso
        ((affinePullbackGlobalSectionsIso σ (((pushforward f).rightDerived n).obj M)).hom ≫
          moduleSpecΓFunctor.map (higherDirectImageAffineMap p b f σ w ψ n)) := inferInstance
    rw [higherDirectImageAffineMap_sections] at ht
    exact (higherDirectImageAffineSectionsTensorMap_isIso_iff p b f σ w ψ n).mp ht
  · exact higherDirectImageAffineMap_isIso p b f σ w ψ n

/-- Surjectivity on actual global sections is equivalent to surjectivity of the original
cohomology tensor mate, including for residue-field changes of scalars. -/
theorem higherDirectImageAffineMap_sections_epi_iff :
    Epi (moduleSpecΓFunctor.map (higherDirectImageAffineMap p b f σ w ψ n)) ↔
      Epi (moduleCohomologyTensorMap p σ.hom
        (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
        (b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom)
        (moduleSectionsBaseChangeScalars p b f σ.hom w) ψ n) := by
  let := moduleHigherDirectImageAffine_isQuasicoherent f M n
  rw [← epi_comp_iff_of_epi
    (affinePullbackGlobalSectionsIso σ (((pushforward f).rightDerived n).obj M)).hom,
    higherDirectImageAffineMap_sections]
  exact higherDirectImageAffineSectionsTensorMap_epi_iff p b f σ w ψ n

/-- The geometric unit-pure-tensor formula uniquely determines the actual affine sheaf
comparison. This is uniqueness of the forward map, not a choice of an object isomorphism. -/
theorem higherDirectImageAffineMap_eq_of_one_tmul
    (k : (pullback (Spec.map σ)).obj (((pushforward f).rightDerived n).obj M) ⟶
      ((pushforward b).rightDerived n).obj N)
    (hk : let := moduleHigherDirectImageAffine_isQuasicoherent f M n
      ∀ x : moduleSpecΓFunctor.obj (((pushforward f).rightDerived n).obj M),
        moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) n
          (moduleSpecΓFunctor.map k
            ((affinePullbackGlobalSectionsIso σ
              (((pushforward f).rightDerived n).obj M)).hom ((1 : S) ⊗ₜ[R,σ.hom] x))) =
          moduleCohomologyMapAlong p ψ n
            (moduleHigherDirectImageAffineSectionsLinearEquiv f M
              (injectiveResolution M) n x)) :
    k = higherDirectImageAffineMap p b f σ w ψ n := by
  let E := ((pushforward f).rightDerived n).obj M
  let : E.IsQuasicoherent := moduleHigherDirectImageAffine_isQuasicoherent f M n
  let : ((pullback (Spec.map σ)).obj E).IsQuasicoherent :=
    isQuasicoherent_pullback σ E
  apply hom_eq_of_globalSections_eq
  apply (cancel_epi (affinePullbackGlobalSectionsIso σ E).hom).mp
  rw [higherDirectImageAffineMap_sections]
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  apply (moduleHigherDirectImageAffineSectionsLinearEquiv b N
    (injectiveResolution N) n).injective
  exact (hk x).trans (higherDirectImageAffineSectionsTensorMap_one_tmul p b f σ w ψ n x).symm

end Affine

section FibreProduct

variable {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}

variable (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
  (σ : R →+* S) (n : ℕ) (M : X.Modules) [M.IsQuasicoherent]

/-- The actual affine higher-image comparison on the genuine fibre product, for arbitrary
change of scalars. -/
def higherDirectImageAffineBaseChangeMap :
    (pullback (Spec.map (CommRingCat.ofHom σ))).obj
        (((pushforward f).rightDerived n).obj M) ⟶
      ((pushforward (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom σ)))).rightDerived n).obj
        ((pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M) :=
  higherDirectImageAffineMap (M := M)
    (N := (pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ)))
    (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom σ))) f (CommRingCat.ofHom σ)
    Limits.pullback.condition
    ((pullbackPushforwardAdjunction
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).unit.app M) n

/-- The original affine scalar cohomology criterion applies to the actual affine sheaf map. -/
theorem higherDirectImageAffineBaseChangeMap_isIso
    (h : IsIso (moduleCohomologyBaseChangeMap f σ M n)) :
    IsIso (higherDirectImageAffineBaseChangeMap f σ n M) :=
  higherDirectImageAffineMap_isIso (M := M)
    (N := (pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)
    _ _ f (CommRingCat.ofHom σ) _ _ n h

/-- The actual affine sheaf comparison is invertible exactly when the original scalar
cohomology base-change map on the genuine fibre product is invertible. -/
theorem higherDirectImageAffineBaseChangeMap_isIso_iff :
    IsIso (higherDirectImageAffineBaseChangeMap f σ n M) ↔
      IsIso (moduleCohomologyBaseChangeMap f σ M n) :=
  higherDirectImageAffineMap_isIso_iff (M := M)
    (N := (pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)
    _ _ f (CommRingCat.ofHom σ) _ _ n

/-- Surjectivity on actual affine sections is precisely surjectivity of the original scalar
cohomology base-change map, including an arbitrary residue-field change of scalars. -/
theorem higherDirectImageAffineBaseChangeMap_sections_epi_iff :
    Epi (moduleSpecΓFunctor.map (higherDirectImageAffineBaseChangeMap f σ n M)) ↔
      Epi (moduleCohomologyBaseChangeMap f σ M n) :=
  higherDirectImageAffineMap_sections_epi_iff (M := M)
    (N := (pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)
    _ _ f (CommRingCat.ofHom σ) _ _ n

end FibreProduct

end AlgebraicGeometry.Scheme.Modules
