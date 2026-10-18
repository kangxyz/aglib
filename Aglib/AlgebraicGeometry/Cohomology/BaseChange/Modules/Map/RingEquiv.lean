/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec

/-!
# Original cohomology base change under an isomorphism of target rings

The actual two fibre products are related by the native pullback map induced
by the ring isomorphism. Native module pullback composition identifies the
ordinary pulled coefficients. The original geometric cohomology arrows form
a commuting triangle, through their unchanged adjunction units.

Consequently epimorphy and invertibility of the original scalar comparison
are invariant under an isomorphism of the target ring. No flatness,
quasicoherence, Noetherianity, properness or finiteness is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The native ordinary-coefficient comparison for a commuting triangle. -/
private def ordinaryPullbackCoefficientIso
    {V W Z : Scheme.{u}} (p : W ⟶ V) (q : Z ⟶ W) (r : Z ⟶ V) (h : q ≫ p = r)
    (M : V.Modules) :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback r).obj M :=
  (Scheme.Modules.pullbackComp q p).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

/-- The original unit followed by the native triangle coefficient comparison. -/
private def ordinaryPullbackCoefficientMap
    {V W Z : Scheme.{u}} (p : W ⟶ V) (q : Z ⟶ W) (r : Z ⟶ V) (h : q ≫ p = r)
    (M : V.Modules) :
    (Scheme.Modules.pullback p).obj M ⟶
      (Scheme.Modules.pushforward q).obj ((Scheme.Modules.pullback r).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app _ ≫
    (Scheme.Modules.pushforward q).map (ordinaryPullbackCoefficientIso p q r h M).hom

/-- Native pullback composition and an opaque equality of scheme arrows give
the original geometric cohomology triangle. -/
private theorem ordinaryPullbackCohomologyTriangle
    {V W Z : Scheme.{u}} (p : W ⟶ V) (q : Z ⟶ W) (r : Z ⟶ V) (h : q ≫ p = r)
    (M : V.Modules) (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf V M) n) :
    moduleCohomologyMapAlong q (ordinaryPullbackCoefficientMap p q r h M) n
        (moduleCohomologyPullback p M n x) = moduleCohomologyPullback r M n x := by
  let C₁ := (Scheme.Modules.pullbackComp q p).hom.app M
  let C₂ := (Scheme.Modules.pullbackCongr h).hom.app M
  let F := SheafOfModules.toSheaf Z.ringCatSheaf
  let z := moduleCohomologyPullback q ((Scheme.Modules.pullback p).obj M) n
    (moduleCohomologyPullback p M n x)
  dsimp only [ordinaryPullbackCoefficientMap]
  erw [moduleCohomologyMapAlong_postcomp]
  change Sheaf.H.map (F.map (C₁ ≫ C₂)) n z = moduleCohomologyPullback r M n x
  rw [F.map_comp C₁ C₂]
  exact (Sheaf.H.map_comp_apply (f := F.map C₁) (g := F.map C₂) (n := n) z).trans
    ((congrArg (Sheaf.H.map (F.map C₂) n) (moduleCohomologyPullback_comp p q M n x)).trans
      (moduleCohomologyPullback_congr (q ≫ p) r h M n x))

variable {X : Scheme.{u}} {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : X ⟶ Spec (CommRingCat.of R)) (σ : R →+* S) (e : S ≃+* T)

/-- The actual geometric comparison between the two original fibre products. -/
private def ringEquivPullbackMap :
    pullback f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom σ)) :=
  pullback.map f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ)))
    f (Spec.map (CommRingCat.ofHom σ)) (𝟙 X) (Spec.map (CommRingCat.ofHom e.toRingHom))
    (𝟙 _) (by simp) (by simp [← Spec.map_comp])

private instance ringEquivPullbackMap_isIso : IsIso (ringEquivPullbackMap f σ e) := by
  let : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
  dsimp only [ringEquivPullbackMap]
  infer_instance

/-- The fibre-product comparison preserves the original map to the source scheme. -/
private theorem ringEquivPullbackMap_fst :
    ringEquivPullbackMap f σ e ≫ pullback.fst f (Spec.map (CommRingCat.ofHom σ)) =
      pullback.fst f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ))) := by
  simp [ringEquivPullbackMap]

/-- The same comparison preserves the actual structural map through the given ring isomorphism. -/
private theorem ringEquivPullbackMap_snd :
    ringEquivPullbackMap f σ e ≫ pullback.snd f (Spec.map (CommRingCat.ofHom σ)) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ))) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) := by
  simp [ringEquivPullbackMap]

/-- The original coefficient arrow is the native pullback unit followed by the comparison. -/
private def ringEquivCoefficientMap (M : X.Modules) :
    (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M ⟶
      (Scheme.Modules.pushforward (ringEquivPullbackMap f σ e)).obj
        ((Scheme.Modules.pullback
          (pullback.fst f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ))))).obj M) :=
  ordinaryPullbackCoefficientMap
    (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) (ringEquivPullbackMap f σ e)
    (pullback.fst f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ))))
    (ringEquivPullbackMap_fst f σ e) M

private instance ringEquivCoefficientMap_isIso (M : X.Modules) :
    IsIso (ringEquivCoefficientMap f σ e M) := by
  let : (Scheme.Modules.pullback (ringEquivPullbackMap f σ e)).IsEquivalence :=
    Scheme.Modules.pullback_isEquivalence_of_isIso _
  dsimp only [ringEquivCoefficientMap, ordinaryPullbackCoefficientMap]
  infer_instance

/-- The actual geometric cohomology triangle follows from the original module pullback units. -/
private theorem ringEquivCohomologyTriangle (M : X.Modules) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyMapAlong (ringEquivPullbackMap f σ e) (ringEquivCoefficientMap f σ e M) n
        (moduleCohomologyPullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) M n x) =
      moduleCohomologyPullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ)))) M n x := by
  exact ordinaryPullbackCohomologyTriangle
    (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) (ringEquivPullbackMap f σ e)
    (pullback.fst f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ))))
    (ringEquivPullbackMap_fst f σ e) M n x

/-- Changing the target ring by an isomorphism preserves epimorphy of the
original affine cohomology comparison, with its original ordinary coefficients. -/
theorem moduleCohomologyBaseChangeMap_epi_iff_ringEquiv (M : X.Modules) (n : ℕ) :
    Epi (moduleCohomologyBaseChangeMap f (e.toRingHom.comp σ) M n) ↔
      Epi (moduleCohomologyBaseChangeMap f σ M n) := by
  let a := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let b := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let a' := pullback.fst f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ)))
  let b' := pullback.snd f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ)))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let γ := b'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  exact moduleCohomologyTensorMap_epi_iff_of_ringEquiv_triangle
    a (ringEquivPullbackMap f σ e) a' σ e α β γ
    (moduleSectionsBaseChangeScalars a b f σ pullback.condition)
    (moduleSectionsBaseChangeScalars (ringEquivPullbackMap f σ e) b' b e.toRingHom
      (ringEquivPullbackMap_snd f σ e))
    (moduleSectionsBaseChangeScalars a' b' f (e.toRingHom.comp σ) pullback.condition)
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M)
    (ringEquivCoefficientMap f σ e M)
    ((Scheme.Modules.pullbackPushforwardAdjunction a').unit.app M) n
    (ringEquivCohomologyTriangle f σ e M n)

/-- Changing the target ring by an isomorphism preserves invertibility of the
original affine cohomology comparison, with its original ordinary coefficients. -/
theorem moduleCohomologyBaseChangeMap_isIso_iff_ringEquiv (M : X.Modules) (n : ℕ) :
    IsIso (moduleCohomologyBaseChangeMap f (e.toRingHom.comp σ) M n) ↔
      IsIso (moduleCohomologyBaseChangeMap f σ M n) := by
  let a := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let b := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let a' := pullback.fst f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ)))
  let b' := pullback.snd f (Spec.map (CommRingCat.ofHom (e.toRingHom.comp σ)))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let γ := b'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  exact moduleCohomologyTensorMap_isIso_iff_of_ringEquiv_triangle
    a (ringEquivPullbackMap f σ e) a' σ e α β γ
    (moduleSectionsBaseChangeScalars a b f σ pullback.condition)
    (moduleSectionsBaseChangeScalars (ringEquivPullbackMap f σ e) b' b e.toRingHom
      (ringEquivPullbackMap_snd f σ e))
    (moduleSectionsBaseChangeScalars a' b' f (e.toRingHom.comp σ) pullback.condition)
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M)
    (ringEquivCoefficientMap f σ e M)
    ((Scheme.Modules.pullbackPushforwardAdjunction a').unit.app M) n
    (ringEquivCohomologyTriangle f σ e M n)

end AlgebraicGeometry.Scheme.Cohomology
