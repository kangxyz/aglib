/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.NoetherianDescent

/-!
# Actual closed-image models for property descent

A quasi-compact morphism is schematically dominant onto its native closed
image. If a flat base change of that morphism is a closed immersion, the same
base change of its image factor is an isomorphism. Thus an already descended
map into a proper scheme supplies an actual proper closed-image model, with
its prescribed flat-fibre comparison. Finite-presentation limit arguments can
then detect the image-factor isomorphism at a later stage.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TensorProduct Topology TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The native map to the scheme-theoretic image is schematically dominant
for every quasi-compact morphism. -/
theorem isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  have hinj (U : f.image.Opens) : Function.Injective (f.toImage.app U) :=
    TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
      (F := f.image.sheaf) f.toImage.c U
        (fun x _ => f.stalkFunctor_toImage_injective x)
  constructor
  apply Scheme.IdealSheafData.ext
  funext U
  simpa only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using
    ((RingHom.injective_iff_ker_eq_bot (f.toImage.app U.1).hom).mp (hinj U.1))

/-- The actual map from a base change to the same base change of its native
closed image. -/
def pullbackToImage {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) :
    pullback f g ⟶ pullback f.imageι g :=
  pullback.map f g f.imageι g f.toImage (𝟙 T) (𝟙 Y) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem pullbackToImage_fst {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) :
    pullbackToImage f g ≫ pullback.fst f.imageι g = pullback.fst f g ≫ f.toImage := by
  simp [pullbackToImage]

@[reassoc (attr := simp)]
theorem pullbackToImage_snd {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) :
    pullbackToImage f g ≫ pullback.snd f.imageι g = pullback.snd f g := by
  simp [pullbackToImage]

/-- The image comparison is itself the literal base change of the original
map to the image. -/
theorem isPullback_pullbackToImage {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) :
    IsPullback (pullback.fst f g) (pullbackToImage f g)
      f.toImage (pullback.fst f.imageι g) := by
  apply IsPullback.flip
  refine IsPullback.of_right (h₁₂ := pullback.snd f.imageι g) ?_ ?_
    (IsPullback.of_hasPullback f.imageι g).flip
  · simpa only [pullbackToImage_snd, Scheme.Hom.toImage_imageι] using
      (IsPullback.of_hasPullback f g).flip
  · exact pullbackToImage_fst f g

/-- Flat base change which makes the original morphism a closed immersion
identifies its literal source pullback with its literal closed-image pullback. -/
theorem isIso_pullbackToImage_of_flat {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : T ⟶ Y) [QuasiCompact f] [Flat g]
    [IsClosedImmersion (pullback.snd f g)] : IsIso (pullbackToImage f g) := by
  let : IsSchemeTheoreticallyDominant f.toImage := isSchemeTheoreticallyDominant_toImage f
  let : IsSchemeTheoreticallyDominant (pullbackToImage f g) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_pullbackToImage f g)
  let : IsClosedImmersion (pullbackToImage f g ≫ pullback.snd f.imageι g) := by
    rw [pullbackToImage_snd]
    infer_instance
  let : IsClosedImmersion (pullbackToImage f g) :=
    IsClosedImmersion.of_comp_isClosedImmersion _ (pullback.snd f.imageι g)
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (pullbackToImage f g).ker_eq_bot

/-- A map into an actual proper model constructs an actual proper closed-image
model. Over a locally Noetherian base this model is finitely presented. -/
theorem proper_finitePresentation_image {X P S : Scheme.{u}} [IsLocallyNoetherian S]
    (a : X ⟶ P) (p : P ⟶ S) [IsProper p] :
    IsProper (a.imageι ≫ p) ∧ LocallyOfFinitePresentation (a.imageι ≫ p) ∧
      QuasiCompact (a.imageι ≫ p) ∧ QuasiSeparated (a.imageι ≫ p) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The native closed image of a descended map has the original fibre when
that fibre map is a closed immersion. Both displayed squares and both
structural triangles remain the actual original maps. -/
def imageModelBaseChangeIso
    {X P S XK PK T : Scheme.{u}}
    (f : X ⟶ S) (p : P ⟶ S) (a : X ⟶ P) (ha : a ≫ p = f)
    (g : T ⟶ S) [Flat g] [QuasiCompact a]
    (iX : XK ⟶ X) (fK : XK ⟶ T) (hX : IsPullback iX fK f g)
    (iP : PK ⟶ P) (pK : PK ⟶ T) (hP : IsPullback iP pK p g)
    (aK : XK ⟶ PK) [IsClosedImmersion aK]
    (haK : iX ≫ a = aK ≫ iP) (hbase : aK ≫ pK = fK) :
    (Over.pullback g).obj (Over.mk (a.imageι ≫ p)) ≅ Over.mk fK := by
  have hA : IsPullback iX aK a iP := by
    refine IsPullback.of_bot ?_ haK hP
    simpa only [ha, hbase] using hX
  let : Flat iP := MorphismProperty.of_isPullback hP.flip inferInstance
  let : IsClosedImmersion (pullback.snd a iP) := by
    rw [← hA.isoPullback_inv_snd]
    infer_instance
  let : IsIso (pullbackToImage a iP) := isIso_pullbackToImage_of_flat a iP
  let hI : IsPullback (pullback.fst a.imageι iP)
      (pullback.snd a.imageι iP ≫ pK) (a.imageι ≫ p) g :=
    (IsPullback.of_hasPullback a.imageι iP).paste_vert hP
  let e : XK ≅ pullback (a.imageι ≫ p) g :=
    hA.isoPullback ≪≫ asIso (pullbackToImage a iP) ≪≫ hI.isoPullback
  have he : e.hom ≫ pullback.snd (a.imageι ≫ p) g = fK := by
    simp only [e, Iso.trans_hom, Category.assoc, hI.isoPullback_hom_snd,
      asIso_hom, pullbackToImage_snd_assoc, hA.isoPullback_hom_snd_assoc]
    exact hbase
  exact (Over.isoMk e he).symm

/-- A standard-smooth affine field algebra, in its original relative
 dimension, has an actual finite-base affine model above any prescribed finite
 integer subalgebra. The comparison is the literal over-category pullback. -/
theorem exists_standardSmooth_affine_model_above
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n K B]
    (A : Subalgebra ℤ K) (hA : A.FG) :
    ∃ (S : Subalgebra ℤ K) (D : Type u) (_ : CommRing D) (_ : Algebra S D),
      A ≤ S ∧ S.FG ∧ Algebra.IsStandardSmoothOfRelativeDimension n S D ∧
      SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap S D))) ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap S K)))).obj
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap S D)))) ≅
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))) := by
  obtain ⟨S₀, D, hD, hSD, hS₀, hsm, ⟨e⟩⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg A K B n
  let := hD
  let := hSD
  let := hsm
  let S := S₀.restrictScalars ℤ
  let : Algebra A S := S₀.algebra
  let : Algebra S D := hSD
  let : Algebra.IsStandardSmoothOfRelativeDimension n S D := hsm
  have hle : A ≤ S := fun a ha => S₀.algebraMap_mem (⟨a, ha⟩ : A)
  have hS : S.FG := S.fg_iff_finiteType.mpr
    (Algebra.FiniteType.trans (A.fg_iff_finiteType.mp hA) (S₀.fg_iff_finiteType.mp hS₀))
  have hSpec : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap S D))) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr hsm
  let E : K ⊗[S] D ≃ₐ[K] B := e.symm
  let eSpec : Spec (CommRingCat.of (K ⊗[S] D)) ≅ Spec (CommRingCat.of B) :=
    (Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op).symm
  have heSpec : eSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[S] D))) := by
    change Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext x
    exact E.symm.commutes x
  let ePullback := pullbackSymmetry
      (Spec.map (CommRingCat.ofHom (algebraMap S D)))
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) ≪≫
    pullbackSpecIso S K D ≪≫ eSpec
  refine ⟨S, D, hD, hSD, hle, hS, hsm, hSpec, ⟨Over.isoMk ePullback ?_⟩⟩
  change ePullback.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) = _
  simp only [ePullback, Iso.trans_hom, Category.assoc, heSpec]
  rw [pullbackSpecIso_hom_fst']
  exact pullbackSymmetry_hom_comp_fst _ _

/-- Under flat base change, the actual changed map and the actual changed
closed-image inclusion have the same kernel ideal sheaf. -/
theorem ker_pullback_snd_eq_image_of_flat {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : T ⟶ Y) [QuasiCompact f] [Flat g] :
    (pullback.snd f g).ker = (pullback.snd f.imageι g).ker := by
  let : IsSchemeTheoreticallyDominant f.toImage := isSchemeTheoreticallyDominant_toImage f
  let : IsSchemeTheoreticallyDominant (pullbackToImage f g) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_pullbackToImage f g)
  rw [← pullbackToImage_snd f g, Scheme.Hom.ker_comp,
    (pullbackToImage f g).ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- A schematically dense piece of the original closed fibre suffices to
identify the entire fibre of the actual proper closed-image model. This
applies to a descended nonempty affine open in an integral projective curve. -/
def imageModelBaseChangeIsoOfSchematicFactor
    {X P S XK PK T C : Scheme.{u}}
    (f : X ⟶ S) (p : P ⟶ S) (a : X ⟶ P) (ha : a ≫ p = f)
    (g : T ⟶ S) [Flat g] [QuasiCompact a]
    (iX : XK ⟶ X) (fK : XK ⟶ T) (hX : IsPullback iX fK f g)
    (iP : PK ⟶ P) (pK : PK ⟶ T) (hP : IsPullback iP pK p g)
    (aK : XK ⟶ PK) (haK : iX ≫ a = aK ≫ iP) (hbase : aK ≫ pK = fK)
    (j : XK ⟶ C) [IsSchemeTheoreticallyDominant j]
    (i : C ⟶ PK) [IsClosedImmersion i] (hji : j ≫ i = aK)
    (q : C ⟶ T) (hi : i ≫ pK = q) :
    (Over.pullback g).obj (Over.mk (a.imageι ≫ p)) ≅ Over.mk q := by
  have hA : IsPullback iX aK a iP := by
    refine IsPullback.of_bot ?_ haK hP
    simpa only [ha, hbase] using hX
  let : Flat iP := MorphismProperty.of_isPullback hP.flip inferInstance
  have hker : i.ker = (pullback.snd a.imageι iP).ker := by
    calc
      i.ker = (j ≫ i).ker := by
        rw [Scheme.Hom.ker_comp, j.ker_eq_bot, Scheme.IdealSheafData.map_bot]
      _ = aK.ker := by rw [hji]
      _ = (pullback.snd a iP).ker := by
        rw [← hA.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso]
      _ = _ := ker_pullback_snd_eq_image_of_flat a iP
  let k : C ⟶ pullback a.imageι iP :=
    IsClosedImmersion.lift (pullback.snd a.imageι iP) i hker.symm.le
  let : IsIso k := IsClosedImmersion.isIso_lift _ _ hker.symm
  let hI : IsPullback (pullback.fst a.imageι iP)
      (pullback.snd a.imageι iP ≫ pK) (a.imageι ≫ p) g :=
    (IsPullback.of_hasPullback a.imageι iP).paste_vert hP
  let e : C ≅ pullback (a.imageι ≫ p) g := asIso k ≪≫ hI.isoPullback
  have he : e.hom ≫ pullback.snd (a.imageι ≫ p) g = q := by
    simp only [e, Iso.trans_hom, Category.assoc, hI.isoPullback_hom_snd, asIso_hom]
    rw [← Category.assoc, IsClosedImmersion.lift_fac]
    exact hi
  exact (Over.isoMk e he).symm

/-- A smooth pullback along a flat preimmersion lies over the original smooth
locus. Both projection stalk maps are the actual localization isomorphisms. -/
theorem pullback_fst_mem_smoothLocus_of_flat_preimmersion
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat g] [IsPreimmersion g]
    [Smooth (pullback.snd f g)] (x : (pullback f g : Scheme.{u})) :
    pullback.fst f g x ∈ f.smoothLocus := by
  let a := pullback.fst f g
  let b := pullback.snd f g
  let : Flat a := inferInstanceAs (Flat (pullback.fst f g))
  let : IsPreimmersion a := inferInstanceAs (IsPreimmersion (pullback.fst f g))
  let : Smooth b := inferInstanceAs (Smooth (pullback.snd f g))
  let : IsIso (a.stalkMap x) :=
    Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks a x
  let : IsIso (g.stalkMap (b x)) :=
    Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks g (b x)
  have hb : ((b ≫ g).stalkMap x).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.FormallySmooth.respectsIso.cancel_left_isIso]
    exact b.smoothLocus_eq_top.ge (Set.mem_univ x)
  rw [← show a ≫ f = b ≫ g from pullback.condition, Scheme.Hom.stalkMap_comp,
    CommRingCat.hom_comp, RingHom.FormallySmooth.respectsIso.cancel_right_isIso] at hb
  exact hb

/-- For a proper finitely presented morphism, smoothness after a flat
preimmersion spreads to an actual open neighbourhood of each point in its
image. Properness is used to remove the closed image of the nonsmooth locus. -/
theorem exists_open_smooth_of_isProper_of_flat_preimmersion
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    [IsProper f] [LocallyOfFinitePresentation f] [Flat g] [IsPreimmersion g]
    [Smooth (pullback.snd f g)] (s : Y) (hs : s ∈ Set.range g) :
    ∃ U : Y.Opens, s ∈ U ∧ Smooth (f ∣_ U) := by
  classical
  let U : Y.Opens :=
    ⟨(f '' (f.smoothLocus : Set X)ᶜ)ᶜ,
      (f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩
  have hU : s ∈ U := by
    rintro ⟨x, hx, hxs⟩
    have ha : x ∈ Set.range (pullback.fst f g) :=
      (Scheme.Pullback.range_fst f g).ge (by
        change f x ∈ Set.range g
        rw [hxs]
        exact hs)
    obtain ⟨z, rfl⟩ := ha
    exact hx (pullback_fst_mem_smoothLocus_of_flat_preimmersion f g z)
  refine ⟨U, hU, ?_⟩
  apply (Scheme.Hom.smoothLocus_eq_top_iff (f := f ∣_ U)).mp
  apply top_unique
  intro x _
  apply (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (morphismRestrictStalkMap f U x)).mpr
  by_contra hx
  exact x.2 ⟨x.1, hx, rfl⟩

/-- A quasi-compact field scheme smooth of relative dimension `n` has a
finite affine atlas of standard-smooth algebras in that same dimension.
Every chart map retains the original structural triangle. -/
theorem exists_finite_standardSmooth_affine_atlas
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (n : ℕ) [SmoothOfRelativeDimension n f] [QuasiCompact f] :
    ∃ (s : Finset X) (V : s → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
      (φ : ∀ i, CommRingCat.of K ⟶ Γ(X, V i)),
      IsOpenCover V ∧ ∀ i, (hV i).fromSpec ≫ f = Spec.map (φ i) ∧
        (φ i).hom.IsStandardSmoothOfRelativeDimension n := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hlocal (x : X) : ∃ (V : X.Opens) (hV : IsAffineOpen V)
      (φ : CommRingCat.of K ⟶ Γ(X, V)),
      x ∈ V ∧ hV.fromSpec ≫ f = Spec.map φ ∧
        φ.hom.IsStandardSmoothOfRelativeDimension n := by
    obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (f := f) (n := n) x
    have hUt : U = ⊤ := by
      apply top_unique
      intro z _
      exact (Subsingleton.elim z (f x)) ▸ e hx
    subst U
    let φ := (Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ V e
    refine ⟨V, hV, φ, hx, ?_, ?_⟩
    · rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV e,
        IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    · dsimp only [φ]
      rw [CommRingCat.hom_comp,
        (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso]
      exact hf
  choose V hV φ hx hφ hsmooth using hlocal
  have hcover : IsOpenCover V := by
    apply IsOpenCover.mk
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _
    (fun i => (V i).isOpen) hcover.iSup_set_eq_univ.ge
  have hfinite : IsOpenCover (fun i : s => V i.1) := by
    simpa only [IsOpenCover, eq_top_iff, ← SetLike.coe_subset_coe,
      TopologicalSpace.Opens.coe_top, TopologicalSpace.Opens.iSup_mk,
      TopologicalSpace.Opens.carrier_eq_coe, TopologicalSpace.Opens.coe_mk,
      Set.iUnion_subtype] using hs
  exact ⟨s, fun i => V i.1, fun i => hV i.1, fun i => φ i.1,
    hfinite, fun i => ⟨hφ i.1, hsmooth i.1⟩⟩

/-- The relative dimension of a smooth family is detected after a dominant
field base change. Every nonempty standard-smooth chart meets that fibre,
where the two native field-dimension formulas identify its dimension. -/
theorem smoothOfRelativeDimension_of_dominant_fieldBaseChange
    {X Y : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Y) (g : Spec (.of K) ⟶ Y) [Smooth f] [IsDominant g]
    (n : ℕ) [SmoothOfRelativeDimension n (pullback.snd f g)] :
    SmoothOfRelativeDimension n f := by
  let a := pullback.fst f g
  let b := pullback.snd f g
  have hdense : DenseRange a := by
    change Dense (Set.range (pullback.fst f g))
    rw [Scheme.Pullback.range_fst]
    exact g.denseRange.preimage f.isOpenMap
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  let φ := (f.appLE U V e).hom
  let : Algebra Γ(Y, U) Γ(X, V) := φ.toAlgebra
  have hstd : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := hf
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hstd.out
  let m := P.dimension
  have hrel : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m :=
    ⟨ι, σ, hσ, hι, P, rfl⟩
  let : IsAffine U := hU
  let : IsAffine V := hV
  let p := f.resLE U V e
  let : SmoothOfRelativeDimension m p := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension m)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U V e)).mpr hrel
  obtain ⟨z, hz⟩ := hdense.exists_mem_open V.isOpen ⟨x, hx⟩
  have htop : (⊤ : (Spec (.of K)).Opens) ≤ g ⁻¹ᵁ U := by
    intro t _
    change g t ∈ U
    have hpoint : f (a z) = g (b z) :=
      congrArg (fun q : pullback f g ⟶ Y => q z) pullback.condition
    have hzU : g (b z) ∈ U := hpoint ▸ e hz
    simpa only [Subsingleton.elim t (b z)] using hzU
  let W := a ⁻¹ᵁ V
  let q : W.toScheme ⟶ Spec (.of K) := W.ι ≫ b
  let : Nonempty W := ⟨⟨z, hz⟩⟩
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g) htop e
    (show W = a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ (⊤ : (Spec (.of K)).Opens) by simp [W])
  let qU := b.resLE (⊤ : (Spec (.of K)).Opens) W (by simp)
  let : SmoothOfRelativeDimension m qU := MorphismProperty.of_isPullback H inferInstance
  have hqm : SmoothOfRelativeDimension m q := by
    have hc : SmoothOfRelativeDimension (m + 0)
        (qU ≫ (⊤ : (Spec (.of K)).Opens).ι) := by infer_instance
    rw [Nat.add_zero] at hc
    have hq : qU ≫ (⊤ : (Spec (.of K)).Opens).ι = q :=
      Scheme.Hom.resLE_comp_ι b _
    rw [hq] at hc
    exact hc
  let : SmoothOfRelativeDimension n b :=
    inferInstanceAs (SmoothOfRelativeDimension n (pullback.snd f g))
  have hqn : SmoothOfRelativeDimension n q := by
    have hq : SmoothOfRelativeDimension (0 + n) q := by
      change SmoothOfRelativeDimension (0 + n) (W.ι ≫ b)
      infer_instance
    rw [Nat.zero_add] at hq
    exact hq
  have hm := smoothFieldDimension K W q m hqm inferInstance
  have hn := smoothFieldDimension K W q n hqn inferInstance
  have hmn : m = n := by exact_mod_cast hm.symm.trans hn
  exact ⟨U, hU, V, hV, hx, e, by simpa only [hmn] using hrel⟩

/-- The canonical map from an affine coefficient model to its given scalar
extension makes the literal original structural square cartesian. -/
theorem isPullback_affineModelMap
    (A K D B : Type u) [CommRing A] [CommRing K] [CommRing D] [CommRing B]
    [Algebra A K] [Algebra A D] [Algebra K B]
    (e : K ⊗[A] D ≃ₐ[K] B) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : D →ₐ[A] K ⊗[A] D).toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap K B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A D)))
      (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  have H : IsPushout (CommRingCat.ofHom (algebraMap A K))
      (CommRingCat.ofHom (algebraMap A D))
      (CommRingCat.ofHom (algebraMap K B))
      (CommRingCat.ofHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : D →ₐ[A] K ⊗[A] D).toRingHom)) := by
    refine (CommRingCat.isPushout_tensorProduct A K D).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
      (by simp) (by simp) ?_ ?_
    · ext r
      exact e.commutes r
    · rfl
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ H).flip

end AlgebraicGeometry.Scheme
