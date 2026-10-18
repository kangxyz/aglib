/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec

/-!
# Original scalar comparisons on actual Cartesian affine-base squares

The native isomorphism from an actual Cartesian square to the chosen fibre
product identifies the original geometric cohomology arrows. Its coefficient
comparison uses the ordinary module pullback unit and the native composition
and equality isomorphisms. Epimorphy and invertibility therefore agree with
the original affine base-change map, without geometric finiteness assumptions.

For a genuine coefficient arrow whose original pullback adjoint is invertible,
coefficient naturality gives the same two criteria. The actual adjoint and the
actual coefficient arrow remain in these statements; no object-only comparison
or compatibility family is substituted for them.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The native ordinary-coefficient comparison for an actual commuting triangle. -/
private def cartesianTriangleCoefficientIso
    {V W Z : Scheme.{u}} (p : W ⟶ V) (q : Z ⟶ W) (r : Z ⟶ V) (h : q ≫ p = r)
    (M : V.Modules) :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback r).obj M :=
  (Scheme.Modules.pullbackComp q p).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

/-- The original unit followed by the same native triangle coefficient comparison. -/
private def cartesianTriangleCoefficientMap
    {V W Z : Scheme.{u}} (p : W ⟶ V) (q : Z ⟶ W) (r : Z ⟶ V) (h : q ≫ p = r)
    (M : V.Modules) :
    (Scheme.Modules.pullback p).obj M ⟶
      (Scheme.Modules.pushforward q).obj ((Scheme.Modules.pullback r).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app _ ≫
    (Scheme.Modules.pushforward q).map (cartesianTriangleCoefficientIso p q r h M).hom

/-- The shared coefficient-map head retains the original geometric cohomology triangle. -/
private theorem cartesianTriangleCohomology
    {V W Z : Scheme.{u}} (p : W ⟶ V) (q : Z ⟶ W) (r : Z ⟶ V) (h : q ≫ p = r)
    (M : V.Modules) (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf V M) n) :
    moduleCohomologyMapAlong q (cartesianTriangleCoefficientMap p q r h M) n
        (moduleCohomologyPullback p M n x) = moduleCohomologyPullback r M n x := by
  let C₁ := (Scheme.Modules.pullbackComp q p).hom.app M
  let C₂ := (Scheme.Modules.pullbackCongr h).hom.app M
  let F := SheafOfModules.toSheaf Z.ringCatSheaf
  let z := moduleCohomologyPullback q ((Scheme.Modules.pullback p).obj M) n
    (moduleCohomologyPullback p M n x)
  dsimp only [cartesianTriangleCoefficientMap]
  erw [moduleCohomologyMapAlong_postcomp]
  change Sheaf.H.map (F.map (C₁ ≫ C₂)) n z = moduleCohomologyPullback r M n x
  rw [F.map_comp C₁ C₂]
  exact (Sheaf.H.map_comp_apply (f := F.map C₁) (g := F.map C₂) (n := n) z).trans
    ((congrArg (Sheaf.H.map (F.map C₂) n) (moduleCohomologyPullback_comp p q M n x)).trans
      (moduleCohomologyPullback_congr (q ≫ p) r h M n x))

section Coefficients

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
  (p : Y ⟶ X) (σ : R →+* S) (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
  (hsc : p.appTop.hom.comp α = β.comp σ)
  {M : X.Modules} {N : Y.Modules} (ψ : M ⟶ (Scheme.Modules.pushforward p).obj N)

/-- The genuine coefficient map factors through the original pullback unit by its own adjoint. -/
private theorem tensorMap_eq_unit_comp_adjoint (n : ℕ) :
    moduleCohomologyTensorMap p σ α β hsc ψ n =
      moduleCohomologyTensorMap p σ α β hsc
          ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n ≫
        (moduleCohomologyFunctorOfHom Y β n).map
          (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).symm ψ) := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y β ((Scheme.Modules.pullback p).obj M) n
  let := moduleCohomologyModuleOfHom Y β N n
  let θ := ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).symm ψ
  have hη : (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M ≫
      (Scheme.Modules.pushforward p).map θ = ψ :=
    Equiv.apply_symm_apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N) ψ
  have hcoeff : (𝟙 M) ≫ ψ =
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M ≫
        (Scheme.Modules.pushforward p).map θ := by
    rw [Category.id_comp]
    exact hη.symm
  have ht := moduleCohomologyTensorMap_naturality p σ α β hsc
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) ψ (𝟙 M) θ hcoeff n
  erw [(moduleCohomologyFunctorOfHom X α n).map_id M,
    (ModuleCat.extendScalars.{u, u, u + 1} σ).map_id] at ht
  simpa only [Category.id_comp] using ht

/-- An invertible original adjoint preserves epimorphy of the original tensor comparison. -/
private theorem tensorMap_epi_iff_unit_of_isIso_adjoint
    (hψ : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).symm ψ))
    (n : ℕ) :
    Epi (moduleCohomologyTensorMap p σ α β hsc ψ n) ↔
      Epi (moduleCohomologyTensorMap p σ α β hsc
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n) := by
  let := hψ
  rw [tensorMap_eq_unit_comp_adjoint p σ α β hsc ψ n]
  exact epi_comp_iff_of_isIso _ _

/-- An invertible original adjoint preserves invertibility of the original tensor comparison. -/
private theorem tensorMap_isIso_iff_unit_of_isIso_adjoint
    (hψ : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).symm ψ))
    (n : ℕ) :
    IsIso (moduleCohomologyTensorMap p σ α β hsc ψ n) ↔
      IsIso (moduleCohomologyTensorMap p σ α β hsc
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n) := by
  let := hψ
  rw [tensorMap_eq_unit_comp_adjoint p σ α β hsc ψ n]
  exact isIso_comp_right_iff _ _

end Coefficients

section Cartesian

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
  (p : Y ⟶ X) (b : Y ⟶ Spec (CommRingCat.of S)) (f : X ⟶ Spec (CommRingCat.of R))
  (σ : R →+* S) (h : IsPullback p b f (Spec.map (CommRingCat.ofHom σ)))

/-- The original coefficient arrow through the native Cartesian comparison isomorphism. -/
private def cartesianCoefficientMap (M : X.Modules) :
    (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M ⟶
      (Scheme.Modules.pushforward h.isoPullback.hom).obj ((Scheme.Modules.pullback p).obj M) :=
  cartesianTriangleCoefficientMap (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))
    h.isoPullback.hom p h.isoPullback_hom_fst M

private instance cartesianCoefficientMap_isIso (M : X.Modules) :
    IsIso (cartesianCoefficientMap p b f σ h M) := by
  let : (Scheme.Modules.pullback h.isoPullback.hom).IsEquivalence :=
    Scheme.Modules.pullback_isEquivalence_of_isIso _
  dsimp only [cartesianCoefficientMap, cartesianTriangleCoefficientMap]
  infer_instance

/-- The actual Cartesian comparison and its original coefficient arrow give the native triangle. -/
private theorem cartesianCohomologyTriangle (M : X.Modules) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    moduleCohomologyMapAlong h.isoPullback.hom (cartesianCoefficientMap p b f σ h M) n
        (moduleCohomologyPullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) M n x) =
      moduleCohomologyPullback p M n x :=
  cartesianTriangleCohomology (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))
    h.isoPullback.hom p h.isoPullback_hom_fst M n x

/-- On any actual Cartesian affine-base square, epimorphy of the original unit-coefficient
tensor comparison is exactly epimorphy of the original chosen-fibre-product comparison. -/
theorem moduleCohomologyTensorMap_epi_iff_baseChangeMap_of_isPullback
    (M : X.Modules) (n : ℕ) :
    Epi (moduleCohomologyTensorMap p σ
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      (b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
      (moduleSectionsBaseChangeScalars p b f σ h.w)
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n) ↔
        Epi (moduleCohomologyBaseChangeMap f σ M n) := by
  let a := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let b₀ := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let t := h.isoPullback.hom
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β₀ := b₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let : IsIso t := inferInstanceAs (IsIso h.isoPullback.hom)
  exact moduleCohomologyTensorMap_epi_iff_of_ringEquiv_triangle a t p σ (RingEquiv.refl S)
    α β₀ β (moduleSectionsBaseChangeScalars a b₀ f σ pullback.condition)
    (moduleSectionsBaseChangeScalars t b b₀ (RingEquiv.refl S).toRingHom
      (by
        simp only [RingEquiv.toRingHom_refl, CommRingCat.ofHom_id, Spec.map_id,
          Category.comp_id]
        exact h.isoPullback_hom_snd))
    (moduleSectionsBaseChangeScalars p b f σ h.w)
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M)
    (cartesianCoefficientMap p b f σ h M)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n
    (cartesianCohomologyTriangle p b f σ h M n)

/-- On any actual Cartesian affine-base square, invertibility of the original unit-coefficient
tensor comparison is exactly invertibility of the original chosen-fibre-product comparison. -/
theorem moduleCohomologyTensorMap_isIso_iff_baseChangeMap_of_isPullback
    (M : X.Modules) (n : ℕ) :
    IsIso (moduleCohomologyTensorMap p σ
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      (b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
      (moduleSectionsBaseChangeScalars p b f σ h.w)
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n) ↔
        IsIso (moduleCohomologyBaseChangeMap f σ M n) := by
  let a := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let b₀ := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let t := h.isoPullback.hom
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β₀ := b₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let β := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let : IsIso t := inferInstanceAs (IsIso h.isoPullback.hom)
  exact moduleCohomologyTensorMap_isIso_iff_of_ringEquiv_triangle a t p σ (RingEquiv.refl S)
    α β₀ β (moduleSectionsBaseChangeScalars a b₀ f σ pullback.condition)
    (moduleSectionsBaseChangeScalars t b b₀ (RingEquiv.refl S).toRingHom
      (by
        simp only [RingEquiv.toRingHom_refl, CommRingCat.ofHom_id, Spec.map_id,
          Category.comp_id]
        exact h.isoPullback_hom_snd))
    (moduleSectionsBaseChangeScalars p b f σ h.w)
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M)
    (cartesianCoefficientMap p b f σ h M)
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n
    (cartesianCohomologyTriangle p b f σ h M n)

/-- A genuine coefficient arrow with invertible original pullback adjoint gives the same
epimorphy criterion as the original affine base-change map on the actual Cartesian square. -/
theorem moduleCohomologyTensorMap_epi_iff_baseChangeMap_of_isPullback_of_isIso_adjoint
    {M : X.Modules} {N : Y.Modules} (ψ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (hψ : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).symm ψ))
    (n : ℕ) :
    Epi (moduleCohomologyTensorMap p σ
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      (b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
      (moduleSectionsBaseChangeScalars p b f σ h.w) ψ n) ↔
        Epi (moduleCohomologyBaseChangeMap f σ M n) :=
  (tensorMap_epi_iff_unit_of_isIso_adjoint p σ _ _
      (moduleSectionsBaseChangeScalars p b f σ h.w) ψ hψ n).trans
    (moduleCohomologyTensorMap_epi_iff_baseChangeMap_of_isPullback p b f σ h M n)

/-- A genuine coefficient arrow with invertible original pullback adjoint gives the same
invertibility criterion as the original affine base-change map on the actual Cartesian square. -/
theorem moduleCohomologyTensorMap_isIso_iff_baseChangeMap_of_isPullback_of_isIso_adjoint
    {M : X.Modules} {N : Y.Modules} (ψ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (hψ : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M N).symm ψ))
    (n : ℕ) :
    IsIso (moduleCohomologyTensorMap p σ
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      (b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
      (moduleSectionsBaseChangeScalars p b f σ h.w) ψ n) ↔
        IsIso (moduleCohomologyBaseChangeMap f σ M n) :=
  (tensorMap_isIso_iff_unit_of_isIso_adjoint p σ _ _
      (moduleSectionsBaseChangeScalars p b f σ h.w) ψ hψ n).trans
    (moduleCohomologyTensorMap_isIso_iff_baseChangeMap_of_isPullback p b f σ h M n)

end Cartesian

end AlgebraicGeometry.Scheme.Cohomology
