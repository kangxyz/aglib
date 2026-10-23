/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.Regularity.Projective
public import Aglib.AlgebraicGeometry.Surfaces.Contraction.PointBlowup
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Scheme
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Integral

/-!
# Regularity of the original projective image

The actual image of the original exceptional-curve section system is regular
when its source is regular. At the full residue-field point this follows from
the original first-order lifts and local structure-map comparison. Elsewhere
the original complement isomorphism transfers regularity. The same image is
integral when the original source is integral.

The existence theorem retains the original image, point, complement triangle
and inverse-image ideal. For an integral source the original proper map is
identified with the actual point blowup by its canonical Cartier lift.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood

universe u

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {ι : Type u} {X : Scheme.{u}} {p : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion p]
  {k : Type u} [Field k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i)) (H : LineBundle X)
  {eP : H.val ≅ (Scheme.Modules.pullback p).obj (twistingSheaf A ι 1)} (d : ℕ)

namespace CartierProjectivePresentation

variable {n : ℕ} {hn : 1 ≤ n}
  (F : CartierProjectivePresentation p i hI H eP d n hn)
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (eH : (Scheme.Modules.pullback i).obj H.val ≅
    twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))

omit [IsNoetherianRing A] [IsClosedImmersion p] in
/-- The original projective embedding supplies the actual line bundle on its image. -/
def imageLineBundle : LineBundle F.image :=
  pullbackLineBundle F.imageInclusion (twistingLineBundle A F.index 1)

omit [IsNoetherianRing A] [IsClosedImmersion p] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same image line pulls back to the original corrected Cartier power,
through the original projective-map triangle and section-system comparison. -/
def imageLineBundlePullbackIso :
    (Scheme.Modules.pullback F.toImage).obj (F.imageLineBundle i hI H d).val ≅
      (cartierPowerTwist i hI H n (n * d)).val :=
  ((Scheme.Modules.pullbackComp F.toImage F.imageInclusion).app
    (twistingSheaf A F.index 1)) ≪≫
    ((Scheme.Modules.pullbackCongr F.toImage_imageInclusion).app
      (twistingSheaf A F.index 1)) ≪≫ F.twistingPullbackIso

omit [IsNoetherianRing A] in
/-- The original schematic image is integral whenever the original source is integral. -/
theorem image_isIntegral [IsIntegral X] (r : ℕ) (eι : ι ≃ Fin (r + 1)) :
    IsIntegral F.image := by
  let _ : IsProper F.toProjective := F.toProjective_isProper r eι
  exact Scheme.schemeImage_isIntegral F.toProjective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Regularity of the original source gives regularity at every point of its actual
projective image. The regularity at the exceptional image point is derived from
the same first-order coordinates, without a regularity premise on the image. -/
theorem regularStalks_image (hX : RegularStalks X)
    (r : ℕ) (eι : ι ≃ Fin (r + 1)) (hn2 : 2 ≤ n * d) (j₀ : F.index)
    (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
    (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤)))
    (t : ULift.{u} (Fin 2) → (𝟙_ X.Modules ⟶
      (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
    (ht : ∀ a, t a ≫ (cartierStepSequence i hI
      (cartierPowerTwist i hI H n (n * d - 2))).g =
        firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
    (q : ULift.{u} (Fin 2) → F.index)
    (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a)) :
    RegularStalks F.image := by
  let c := F.residueToImage eI eH j₀ h₀
  have hnd : 1 ≤ n * d := by omega
  let V := F.imageComplementOpen
  let _ : IsIso (F.toImage ∣_ V) :=
    F.imageComplement_restrict_isIso eI eH r eι hnd j₀ h₀
  have hV : RegularStalks V.toScheme :=
    (hX.of_isOpenImmersion (F.toImage ⁻¹ᵁ V).ι).of_isOpenImmersion
      (asIso (F.toImage ∣_ V)).inv
  intro y
  by_cases hy : y = imagePoint c
  · subst y
    exact (F.pointLocalRing_regularLocal_dimension_two i hI H d eI eH
      r eι hn2 j₀ h₀ hρ t ht q hq).2
  · have hyV : y ∈ V := by
      apply (Set.ext_iff.mp (F.imageComplement_carrier eI eH r eι hnd j₀ h₀) y).mpr
      rintro ⟨z, hz⟩
      apply hy
      exact hz.symm.trans (congrArg c (Subsingleton.elim z (IsLocalRing.closedPoint k)))
    let yV : V.toScheme := ⟨y, hyV⟩
    let _ : IsRegularLocalRing (V.toScheme.presheaf.stalk yV) := hV yV
    exact IsRegularLocalRing.of_ringEquiv
      (asIso (V.ι.stalkMap yV)).commRingCatIsoToRingEquiv.symm

section PointBlowup

variable (r : ℕ) (eι : ι ≃ Fin (r + 1)) (hn2 : 2 ≤ n * d) (j₀ : F.index)
  (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
  (hρ : Function.Surjective ((cartierResidueMap i hI H d eI eH n).val.app (op ⊤)))
  (t : ULift.{u} (Fin 2) → (𝟙_ X.Modules ⟶
    (cartierPowerTwist i hI H n (n * d - 2 + 1)).val))
  (ht : ∀ a, t a ≫ (cartierStepSequence i hI
    (cartierPowerTwist i hI H n (n * d - 2))).g =
      firstOrderQuotientCoordinate i hI H d eI eH n hn2 a)
  (q : ULift.{u} (Fin 2) → F.index)
  (hq : ∀ a, F.sections (q a) = firstOrderCartierImage i hI H d n hn2 (t a))

include r eι hn2 hρ t ht q hq in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original inverse-image point ideal is Cartier as an embedded ideal,
using its proved equality with the original exceptional kernel. -/
theorem pointIdeal_cartierPullback :
    Blowup.cartierPullback (F.pointIdeal eI eH j₀ h₀) F.toImage := by
  change IsLocallyRankOne X
    (Hom.idealModule (((F.pointIdeal eI eH j₀ h₀).comap F.toImage).subschemeι))
  rw [F.pointIdeal_comap_eq eI eH r eι (Field.toIsField k) hn2 j₀ h₀ hρ t ht q hq]
  let e := Blowup.RegularPoint.closedImmersionImageIso i
  have he : e.inv ≫ i = i.ker.subschemeι := by
    calc
      e.inv ≫ i = e.inv ≫ (e.hom ≫ i.ker.subschemeι) :=
        congrArg (fun f => e.inv ≫ f)
          (Blowup.RegularPoint.closedImmersionImageIso_hom_ι i).symm
      _ = i.ker.subschemeι := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact isLocallyRankOne_of_iso X
    (Blowup.RegularPoint.identityBaseIdealIso i i.ker.subschemeι e.symm he) hI

include r eι hn2 hρ t ht q hq in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For an integral source the actual original image map is the point
blowup: its canonical lift to that same point-ideal blowup is an isomorphism. -/
theorem toImage_isBlowup [IsIntegral X] :
    ∃ hf : Blowup.cartierPullback (F.pointIdeal eI eH j₀ h₀) F.toImage,
      IsIso ((Blowup.blowupDatum (F.pointIdeal eI eH j₀ h₀)).lift F.toImage hf) := by
  let _ : Finite F.index := F.finiteIndex
  let _ : IsProper F.toImage := F.toImage_isProper r eι
  let _ : IsIntegral F.image := F.image_isIntegral i hI H d r eι
  let _ : IsLocallyNoetherian F.image :=
    LocallyOfFiniteType.isLocallyNoetherian F.imageInclusion
  let c := F.residueToImage eI eH j₀ h₀
  let _ : IsClosedImmersion c :=
    F.residueToImage_isClosedImmersion eI eH (Field.toIsField k) j₀ h₀ hρ
  have hker : c.ker.comap F.toImage = i.ker :=
    F.pointIdeal_comap_eq eI eH r eι (Field.toIsField k) hn2 j₀ h₀ hρ t ht q hq
  have hpb : IsPullback i (toSpec k (ULift.{u} (Fin 2))) F.toImage c :=
    AlgebraicGeometry.isPullback_of_isClosedImmersion i c
      (toSpec k (ULift.{u} (Fin 2))) F.toImage
      (F.exceptional_toImage_eq eI eH j₀ h₀) hker
  let ε := hpb.isoPullback
  let _ : IsIntegral (pullback F.toImage c) := IsIntegral.of_isIso ε.hom
  have hdim : topologicalKrullDim (pullback F.toImage c : Scheme.{u}) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ ε.hom.homeomorph.isHomeomorph).symm.trans
      (ProjectiveSpace.Line.nativeDimension k)
  have hnd : 1 ≤ n * d := by omega
  have hU : Blowup.centreComplement c.ker = F.imageComplementOpen := by
    apply TopologicalSpace.Opens.ext
    change (c.ker.support : Set F.image)ᶜ = (F.imageComplementOpen : Set F.image)
    rw [Hom.support_ker, c.isClosedEmbedding.isClosed_range.closure_eq]
    exact (F.imageComplement_carrier eI eH r eι hnd j₀ h₀).symm
  let _ : IsIso (F.toImage ∣_ Blowup.centreComplement c.ker) := by
    rw [hU]
    exact F.imageComplement_restrict_isIso eI eH r eι hnd j₀ h₀
  have hlocal := F.pointLocalRing_regularLocal_dimension_two i hI H d eI eH
    r eι hn2 j₀ h₀ hρ t ht q hq
  let _ : IsRegularLocalRing (F.image.presheaf.stalk (c (IsLocalRing.closedPoint k))) :=
    hlocal.2
  let hf := F.pointIdeal_cartierPullback i hI H d eI eH
    r eι hn2 j₀ h₀ hρ t ht q hq
  exact ⟨hf, Blowup.RegularPoint.isIso_lift_of_integral_pointFibre_of_regularLocal c hlocal.1
    F.toImage hf hdim⟩

end PointBlowup

end CartierProjectivePresentation

include p eP hI in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For every sufficiently large exponent, a constructed section system contracts
the exceptional Cartier line on an integral projective scheme. The image point
is required to be regular, and that regularity is proved here. Singularities
away from the exceptional curve are allowed. The same presentation retains its
actual projective image line and corrected pullback comparison. -/
theorem exists_cartier_projective_pointBlowup [IsIntegral X]
    (r : ℕ) (eι : ι ≃ Fin (r + 1))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (hd : 0 < d) :
    ∃ (B : ℕ) (hB : 1 ≤ B), ∀ (n : ℕ) (hn : B ≤ n),
      ∃ (_hn2 : 2 ≤ n * d)
        (F : CartierProjectivePresentation p i hI H eP d n (hB.trans hn))
        (j₀ : F.index)
        (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
        (hf : Blowup.cartierPullback (F.pointIdeal eI eH j₀ h₀) F.toImage)
        (ε : (exceptionalComplement i).toScheme ≅ F.imageComplementOpen.toScheme),
        IsProper F.toImage ∧
        IsClosedImmersion (F.residueToImage eI eH j₀ h₀) ∧
        IsRegularLocalRing (pointLocalRing (F.residueToImage eI eH j₀ h₀)) ∧
        ringKrullDim (pointLocalRing (F.residueToImage eI eH j₀ h₀)) = 2 ∧
        IsIso ((Blowup.blowupDatum (F.pointIdeal eI eH j₀ h₀)).lift F.toImage hf) ∧
        (F.pointIdeal eI eH j₀ h₀).comap F.toImage = i.ker ∧
        ε.hom ≫ F.imageComplementOpen.ι = (exceptionalComplement i).ι ≫ F.toImage ∧
        (F.imageComplementOpen : Set F.image) =
          (Set.range (F.residueToImage eI eH j₀ h₀))ᶜ ∧
        i ≫ F.toImage =
          toSpec k (ULift.{u} (Fin 2)) ≫ F.residueToImage eI eH j₀ h₀ := by
  obtain ⟨B, hB, h⟩ := exists_cartier_projective_complement
    p i hI H eP d r eι eI eH (Field.toIsField k) hd
  refine ⟨B, hB, fun n hn => ?_⟩
  obtain ⟨hn2, F, t, q, j₀, h₀, ε, ht, hq, hρ, hc, hε, hcomp, htri⟩ := h n hn
  obtain ⟨hf, hbl⟩ := F.toImage_isBlowup i hI H d eI eH
    r eι hn2 j₀ h₀ hρ t ht q hq
  have hlocal := F.pointLocalRing_regularLocal_dimension_two i hI H d eI eH
    r eι hn2 j₀ h₀ hρ t ht q hq
  exact ⟨hn2, F, j₀, h₀, hf, ε, F.toImage_isProper r eι, hc,
    hlocal.2, hlocal.1, hbl,
    F.pointIdeal_comap_eq eI eH r eι (Field.toIsField k) hn2 j₀ h₀ hρ t ht q hq,
    hε, hcomp, htri⟩

include p eP in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For every sufficiently large exponent, a constructed section system gives a regular image
with the original full residue-field point, complement isomorphism and Cartier
inverse-image ideal. The image-point stalk is regular of dimension two. -/
theorem exists_cartier_projective_regular_image (hX : RegularStalks X)
    (r : ℕ) (eι : ι ≃ Fin (r + 1))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (hd : 0 < d) :
    ∃ (B : ℕ) (hB : 1 ≤ B), ∀ (n : ℕ) (hn : B ≤ n),
      ∃ (_hn2 : 2 ≤ n * d)
        (F : CartierProjectivePresentation p i hI H eP d n (hB.trans hn))
        (j₀ : F.index)
        (h₀ : IsUnit (cartierResidueCoefficient i hI H d eI eH n (F.sections j₀)))
        (ε : (exceptionalComplement i).toScheme ≅ F.imageComplementOpen.toScheme),
        IsProper F.toImage ∧
        IsClosedImmersion (F.residueToImage eI eH j₀ h₀) ∧
        RegularStalks F.image ∧
        ringKrullDim (pointLocalRing (F.residueToImage eI eH j₀ h₀)) = 2 ∧
        (F.pointIdeal eI eH j₀ h₀).comap F.toImage = i.ker ∧
        ε.hom ≫ F.imageComplementOpen.ι = (exceptionalComplement i).ι ≫ F.toImage ∧
        (F.imageComplementOpen : Set F.image) =
          (Set.range (F.residueToImage eI eH j₀ h₀))ᶜ ∧
        i ≫ F.toImage =
          toSpec k (ULift.{u} (Fin 2)) ≫ F.residueToImage eI eH j₀ h₀ := by
  obtain ⟨B, hB, h⟩ := exists_cartier_projective_complement
    p i hI H eP d r eι eI eH (Field.toIsField k) hd
  refine ⟨B, hB, fun n hn => ?_⟩
  obtain ⟨hn2, F, t, q, j₀, h₀, ε, ht, hq, hρ, hc, hε, hcomp, htri⟩ := h n hn
  refine ⟨hn2, F, j₀, h₀, ε, F.toImage_isProper r eι, hc,
    F.regularStalks_image i hI H d eI eH hX r eι hn2 j₀ h₀ hρ t ht q hq,
    (F.pointLocalRing_regularLocal_dimension_two i hI H d eI eH
      r eι hn2 j₀ h₀ hρ t ht q hq).1,
    F.pointIdeal_comap_eq eI eH r eι (Field.toIsField k) hn2 j₀ h₀ hρ t ht q hq,
    hε, hcomp, htri⟩

include p eP hI in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An exceptional Cartier projective line on an integral regular projective scheme
has an actual contraction. The original map is the blowup of the original full
residue-field point; the target remains regular, integral and projective over
the same base, with its actual structural and complement comparisons. -/
theorem exists_cartier_projective_contraction [IsIntegral X] (hX : RegularStalks X)
    (r : ℕ) (eι : ι ≃ Fin (r + 1))
    (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1)
    (eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ))
    (hd : 0 < d) :
    ∃ (Y : Scheme.{u}) (b : X ⟶ Y) (c : Spec (.of k) ⟶ Y)
      (s : Y ⟶ Spec (.of A)) (hf : Blowup.cartierPullback c.ker b),
      Surjective b ∧ IsProper b ∧ IsClosedImmersion c ∧ IsProper s ∧ IsNoetherian Y ∧
      RegularStalks Y ∧ IsIntegral Y ∧
      ringKrullDim (Y.presheaf.stalk (c (IsLocalRing.closedPoint k))) = 2 ∧
      IsIso ((Blowup.blowupDatum c.ker).lift b hf) ∧
      c.ker.comap b = i.ker ∧
      i ≫ b = toSpec k (ULift.{u} (Fin 2)) ≫ c ∧
      b ≫ s = p ≫ toSpec A ι ∧
      (∃ (J : Type u) (j : Y ⟶ ProjectiveSpace A J),
        Finite J ∧ IsClosedImmersion j ∧ j ≫ toSpec A J = s) ∧
      ∃ (V : Y.Opens) (ε : (exceptionalComplement i).toScheme ≅ V.toScheme),
        (V : Set Y) = (Set.range c)ᶜ ∧
        b ⁻¹ᵁ V = exceptionalComplement i ∧
        IsIso (b ∣_ V) ∧
        ε.hom ≫ V.ι = (exceptionalComplement i).ι ≫ b := by
  obtain ⟨B, hB, h⟩ := exists_cartier_projective_complement
    p i hI H eP d r eι eI eH (Field.toIsField k) hd
  obtain ⟨hn2, F, t, q, j₀, h₀, ε, ht, hq, hρ, hc, hε, hcomp, htri⟩ := h B le_rfl
  let _ : Finite F.index := F.finiteIndex
  let _ : IsProper F.imageStructureMap := F.imageStructureMap_isProper
  let _ : IsLocallyNoetherian F.image :=
    LocallyOfFiniteType.isLocallyNoetherian F.imageInclusion
  let _ : CompactSpace F.image :=
    QuasiCompact.compactSpace_of_compactSpace F.imageStructureMap
  have hY : IsNoetherian F.image := ⟨⟩
  obtain ⟨hf, hbl⟩ := F.toImage_isBlowup i hI H d eI eH
    r eι hn2 j₀ h₀ hρ t ht q hq
  have hnd : 1 ≤ B * d := by omega
  refine ⟨F.image, F.toImage, F.residueToImage eI eH j₀ h₀, F.imageStructureMap,
    hf, F.toImage_surjective r eι, F.toImage_isProper r eι, hc,
    F.imageStructureMap_isProper, hY,
    F.regularStalks_image i hI H d eI eH hX r eι hn2 j₀ h₀ hρ t ht q hq,
    F.image_isIntegral i hI H d r eι,
    (F.pointLocalRing_regularLocal_dimension_two i hI H d eI eH
      r eι hn2 j₀ h₀ hρ t ht q hq).1,
    hbl, F.pointIdeal_comap_eq eI eH r eι (Field.toIsField k) hn2 j₀ h₀ hρ t ht q hq,
    htri, F.toImage_toSpec, ⟨F.index, F.imageInclusion, F.finiteIndex,
      inferInstance, rfl⟩,
    F.imageComplementOpen, ε, hcomp,
    F.toImage_preimage_imageComplement eI eH hnd j₀ h₀,
    F.imageComplement_restrict_isIso eI eH r eι hnd j₀ h₀, hε⟩

end AlgebraicGeometry.Scheme.Surfaces.Contraction
