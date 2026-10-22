/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding.Map

/-!
# Gluing original projective chart maps

Coordinate ring maps on an actual open cover glue when their normalized ratios
rescale on overlaps. Exact coordinate-open preimages and surjective affine
chart maps then prove that the resulting original morphism is closed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.ChartGluing

variable {R : Type u} [CommRing R] {α : Type u} {X : Scheme.{u}}
  (U : α → X.Opens) (φ : ∀ a, coordinateRing R α a →+* Γ(X, U a))

/-- The actual chart map, evaluated in the original source sections. -/
def chartMap (a : α) : (U a).toScheme ⟶ (coordinateOpen R α a).toScheme :=
  (U a).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (φ a)) ≫
    (Proj.basicOpenIsoSpec (homogeneousSubmodule α R) (MvPolynomial.X a)
      (isHomogeneous_X R a) Nat.zero_lt_one).inv

/-- The original local morphism into projective space. -/
def localMap (a : α) : (U a).toScheme ⟶ ProjectiveSpace R α :=
  (U a).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (φ a)) ≫
    Proj.awayι (homogeneousSubmodule α R) (MvPolynomial.X a)
      (isHomogeneous_X R a) Nat.zero_lt_one

theorem chartMap_ι (a : α) :
    chartMap U φ a ≫ (coordinateOpen R α a).ι = localMap U φ a := by
  rfl

/-- Original restriction of the coordinate-ring map. -/
def restrict {a : α} {V : X.Opens} (h : V ≤ U a) :
    coordinateRing R α a →+* Γ(X, V) :=
  (sectionRestrict X h).comp (φ a)

theorem localMap_restrict (a : α) {V : X.Opens} (h : V ≤ U a) :
    X.homOfLE h ≫ localMap U φ a =
      V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (restrict U φ h)) ≫
        Proj.awayι (homogeneousSubmodule α R) (MvPolynomial.X a)
          (isHomogeneous_X R a) Nat.zero_lt_one := by
  rw [localMap]
  simp only [← Category.assoc]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc]
  rfl

/-- The actual coefficient and normalized-ratio equations on each double overlap. -/
structure Compatible : Prop where
  coefficient : ∀ a b r,
    restrict U φ (inf_le_left : U a ⊓ U b ≤ U a)
        (coordinateRingCoefficient R α a r) =
      restrict U φ (inf_le_right : U a ⊓ U b ≤ U b)
        (coordinateRingCoefficient R α b r)
  ratio : ∀ a b k,
    restrict U φ (inf_le_left : U a ⊓ U b ≤ U a) (coordinateRatio R α a k) =
      restrict U φ (inf_le_left : U a ⊓ U b ≤ U a) (coordinateRatio R α a b) *
        restrict U φ (inf_le_right : U a ⊓ U b ≤ U b) (coordinateRatio R α b k)

variable (hφ : Compatible U φ)

include hφ in
theorem localMap_agree (a b : α) :
    X.homOfLE (inf_le_left : U a ⊓ U b ≤ U a) ≫ localMap U φ a =
      X.homOfLE (inf_le_right : U a ⊓ U b ≤ U b) ≫ localMap U φ b := by
  let f := restrict U φ (inf_le_left : U a ⊓ U b ≤ U a)
  let g := restrict U φ (inf_le_right : U a ⊓ U b ≤ U b)
  have hinv : f (coordinateRatio R α a b) * g (coordinateRatio R α b a) = 1 := by
    simpa only [coordinateRatio_self, map_one] using (hφ.ratio a b a).symm
  have hu : IsUnit (f (coordinateRatio R α a b)) :=
    isUnit_iff_exists_inv.mpr ⟨_, hinv⟩
  rw [localMap_restrict, localMap_restrict]
  exact congrArg (fun q => (U a ⊓ U b).toSpecΓ ≫ q)
    (FiniteEmbedding.chart_maps_eq_of_rescaling a b f g (hφ.coefficient a b)
      hu (hφ.ratio a b))

variable (hcover : (⨆ a, U a) = ⊤)

/-- The original opens, not a replacement source or product, form the gluing cover. -/
abbrev cover : X.OpenCover := X.openCoverOfIsOpenCover U (.mk hcover)

include hφ in
theorem localMap_compatible (a b : α) :
    pullback.fst ((cover U hcover).f a) ((cover U hcover).f b) ≫ localMap U φ a =
      pullback.snd ((cover U hcover).f a) ((cover U hcover).f b) ≫ localMap U φ b := by
  change pullback.fst (U a).ι (U b).ι ≫ localMap U φ a =
    pullback.snd (U a).ι (U b).ι ≫ localMap U φ b
  let h := isPullback_opens_inf (U a) (U b)
  apply (cancel_epi h.isoPullback.hom).mp
  simp only [← Category.assoc]
  rw [h.isoPullback_hom_fst, h.isoPullback_hom_snd]
  exact localMap_agree U φ hφ a b

/-- The actual projective-coordinate morphism glued from the original chart maps. -/
def map : X ⟶ ProjectiveSpace R α :=
  (cover U hcover).glueMorphisms (localMap U φ) (localMap_compatible U φ hφ hcover)

@[reassoc (attr := simp)]
theorem ι_map (a : α) : (U a).ι ≫ map U φ hφ hcover = localMap U φ a :=
  (cover U hcover).ι_glueMorphisms _ _ a

variable (hbasic : ∀ a b, X.basicOpen (φ a (coordinateRatio R α a b)) = U a ⊓ U b)

include hbasic in
theorem localMap_preimage_coordinateOpen (a b : α) :
    localMap U φ a ⁻¹ᵁ coordinateOpen R α b = (U a).ι ⁻¹ᵁ U b := by
  rw [localMap, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    coordinateChart_preimage_coordinateOpen, SpecMap_preimage_basicOpen]
  change (U a).toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen
    (φ a (coordinateRatio R α a b)) = _
  rw [Scheme.Opens.toSpecΓ_preimage_basicOpen, hbasic,
    Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]

include hbasic in
theorem map_preimage_coordinateOpen (b : α) :
    map U φ hφ hcover ⁻¹ᵁ coordinateOpen R α b = U b := by
  ext x
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ a, U a by rw [hcover]; trivial)
  have h := congrArg (fun V : (U a).toScheme.Opens => (⟨x, ha⟩ : U a) ∈ V)
    ((congrArg (fun q => q ⁻¹ᵁ coordinateOpen R α b) (ι_map U φ hφ hcover a)).trans
      (localMap_preimage_coordinateOpen U φ hbasic a b))
  exact eq_iff_iff.mp h

theorem chartMap_isClosedImmersion (haffine : ∀ a, IsAffineOpen (U a))
    (hsurj : ∀ a, Function.Surjective (φ a)) (a : α) :
    IsClosedImmersion (chartMap U φ a) := by
  let : IsIso (U a).toSpecΓ := by
    change IsIso (haffine a).isoSpec.hom
    infer_instance
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (φ a))) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (φ a)) (hsurj a)
  have : IsIso (Proj.basicOpenIsoSpec (homogeneousSubmodule α R)
      (MvPolynomial.X a) (isHomogeneous_X R a) Nat.zero_lt_one).inv :=
    Iso.isIso_inv _
  have hinner : IsClosedImmersion (Spec.map (CommRingCat.ofHom (φ a)) ≫
      (Proj.basicOpenIsoSpec (homogeneousSubmodule α R)
        (MvPolynomial.X a) (isHomogeneous_X R a) Nat.zero_lt_one).inv) :=
    IsClosedImmersion.comp _ _
  unfold chartMap
  exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance hinner

include hbasic in
/-- Surjective affine chart maps with exact chart preimages give a genuine closed
embedding, without any additional properness or finite-index premise. -/
theorem map_isClosedImmersion (haffine : ∀ a, IsAffineOpen (U a))
    (hsurj : ∀ a, Function.Surjective (φ a)) :
    IsClosedImmersion (map U φ hφ hcover) := by
  let V := fun a => coordinateOpen R α a
  have hlocal (a : α) : IsClosedImmersion (map U φ hφ hcover ∣_ V a) := by
    let e := X.isoOfEq (map_preimage_coordinateOpen U φ hφ hcover hbasic a)
    have hfac : map U φ hφ hcover ∣_ V a = e.hom ≫ chartMap U φ a := by
      apply (cancel_mono (V a).ι).mp
      rw [morphismRestrict_ι, Category.assoc, chartMap_ι]
      rw [← ι_map U φ hφ hcover a, ← Category.assoc]
      simp only [e, Scheme.isoOfEq_hom_ι]
      rfl
    rw [hfac]
    have := chartMap_isClosedImmersion U φ haffine hsurj a
    infer_instance
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) V
    (iSup_coordinateOpen_eq_top R α) hlocal

end AlgebraicGeometry.ProjectiveSpace.ChartGluing
