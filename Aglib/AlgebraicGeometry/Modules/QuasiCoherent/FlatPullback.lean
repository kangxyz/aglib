/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
/-!
# Flat exactness for the actual coherent pullback

The affine comparison identifies actual sheaf pullback with extension of
scalars. Genuine flatness gives exactness of extension of scalars. Local
affine charts and stalk detection of zero kernels globalize monomorphisms.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- An actual open cover detects sheaf monomorphisms, by stalkwise
vanishing of the actual kernel. -/
theorem mono_of_schemeOpenCover {X : Scheme.{u}} {M N : X.Modules}
    (p : M ⟶ N) (𝒰 : Scheme.OpenCover.{u} X)
    (hp : ∀ i, Mono ((Scheme.Modules.restrictFunctor (𝒰.f i)).map p)) : Mono p := by
  apply Preadditive.mono_of_isZero_kernel
  apply (isZero_iff_stalks _).mpr
  intro x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  have := hp (𝒰.idx x)
  have hK : supportedAway (𝒰.f (𝒰.idx x)) (kernel p) :=
    (isZero_kernel_of_mono ((Scheme.Modules.restrictFunctor (𝒰.f (𝒰.idx x))).map p)).of_iso
      (PreservesKernel.iso (Scheme.Modules.restrictFunctor (𝒰.f (𝒰.idx x))) p)
  simpa only [hy] using (supportedAway_iff_stalks (𝒰.f (𝒰.idx x)) (kernel p)).mp hK y

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Affine quasicoherent pullback is actual extension of scalars under tilde. -/
def affineQuasicoherentPullbackIso {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (Spec.map φ) ≅
      (tildeEquiv (R := R)).inverse ⋙ ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  Functor.isoWhiskerRight (affineQuasicoherentToSheavesIso R).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.tildePullbackIso φ)

/-- Flatness of the actual affine ring map proves left exactness of sheaf
pullback on the actual quasicoherent category. -/
theorem affineQuasicoherentPullback_preservesFiniteLimits {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (hφ : φ.hom.Flat) :
    PreservesFiniteLimits ((SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι ⋙
      Scheme.Modules.pullback (Spec.map φ)) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact preservesFiniteLimits_of_natIso (affineQuasicoherentPullbackIso φ).symm

/-- A flat affine pullback preserves any monomorphism between actual
quasicoherent module sheaves. No ambient left-exactness assumption is made. -/
theorem mono_pullback_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : φ.hom.Flat) {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (p : M ⟶ N) [Mono p] :
    Mono ((Scheme.Modules.pullback (Spec.map φ)).map p) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let M' : P.FullSubcategory := ⟨M, inferInstance⟩
  let N' : P.FullSubcategory := ⟨N, inferInstance⟩
  let p' : M' ⟶ N' := ObjectProperty.homMk p
  have : Mono p' := P.ι.mono_of_mono_map (by exact inferInstanceAs (Mono p))
  have := affineQuasicoherentPullback_preservesFiniteLimits φ hφ
  exact inferInstanceAs (Mono ((P.ι ⋙ Scheme.Modules.pullback (Spec.map φ)).map p'))

/-- A flat morphism between spectra preserves monomorphisms of actual
quasicoherent sheaves, using its genuine flat ring map. -/
theorem mono_pullback_affine {R S : CommRingCat.{u}} (f : Spec S ⟶ Spec R)
    [Flat f] {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (p : M ⟶ N) [Mono p] : Mono ((Scheme.Modules.pullback f).map p) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  exact mono_pullback_specMap φ (Flat.SpecMap_iff.mp inferInstance) p

/-- Flat pullback from an affine target preserves monomorphisms between
actual quasicoherent sheaves, detected on affine source charts. -/
theorem mono_pullback_affineTarget {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [Flat f] {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (p : M ⟶ N) [Mono p] :
    Mono ((Scheme.Modules.pullback f).map p) := by
  apply Scheme.Modules.mono_of_schemeOpenCover _ X.affineOpenCover.openCover
  intro i
  let a := X.affineOpenCover.f i
  let e : Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor a ≅
      Scheme.Modules.pullback (a ≫ f) :=
    Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback a) ≪≫
      Scheme.Modules.pullbackComp a f
  have := mono_pullback_affine (a ≫ f) p
  have : Mono ((Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor a).map p ≫
      e.hom.app N) := by
    rw [e.hom.naturality]
    infer_instance
  exact mono_of_mono
    ((Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor a).map p) (e.hom.app N)

/-- Genuine scheme-theoretic flatness preserves monomorphisms between
quasicoherent module sheaves. The proof passes to affine target charts and
then affine source charts, where flat extension of scalars applies. -/
theorem mono_pullback_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (p : M ⟶ N) [Mono p] : Mono ((Scheme.Modules.pullback f).map p) := by
  let 𝒰 := Y.affineOpenCover.openCover.pullback₁ f
  apply Scheme.Modules.mono_of_schemeOpenCover _ 𝒰
  intro i
  let a := Y.affineOpenCover.f i
  let q := pullback.snd f a
  let b := pullback.fst f a
  let e := Scheme.Modules.pullbackOpenSquare b q f a (pullback.condition (f := f) (g := a))
  have hmono : Mono ((Scheme.Modules.restrictFunctor a ⋙ Scheme.Modules.pullback q).map p) :=
    mono_pullback_affineTarget q ((Scheme.Modules.restrictFunctor a).map p)
  have : Mono ((Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor b).map p ≫
      e.hom.app N) := by
    rw [e.hom.naturality]
    exact mono_comp _ _
  exact mono_of_mono
    ((Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor b).map p) (e.hom.app N)

/-- Actual flat pullback preserves a short exact sequence of quasicoherent
sheaves. Right exactness is geometric adjointness; monicity is affine-local
flat tensor exactness proved above. -/
theorem shortExact_pullback_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {S : ShortComplex Y.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    (S.map (Scheme.Modules.pullback f)).ShortExact := by
  have := hS.mono_f
  have hmono := mono_pullback_of_flat f S.f
  have hr := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (Scheme.Modules.pullback f)).mp inferInstance S hS
  exact { exact := hr.1, mono_f := hmono, epi_g := hr.2 }

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
