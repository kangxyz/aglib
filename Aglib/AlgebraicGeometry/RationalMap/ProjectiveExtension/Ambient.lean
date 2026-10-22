/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Extension.AmbientFiniteCover
public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.Global

/-!
# Projective extension over an open part of a larger ambient scheme

Coordinate centres are extended to the ambient scheme, where the entire
specified larger open is protected. The projective map and schematic-density
conclusion are local to the given open part of that ambient scheme.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace.FromSections

universe u v

namespace AlgebraicGeometry.Scheme.RationalCoordinates

variable {R I : Type u} [CommRing R] [Finite I]

/-- Principal affine coordinates on an open part yield a projective map on
its base change after an actual ambient finite refinement. -/
theorem exists_ambient_extension_of_principal_affine_cover {X Z : Scheme.{u}}
    [IsLocallyNoetherian X] (q : Z ⟶ X) [IsOpenImmersion q] [QuasiCompact q]
    (C : Z.AffineOpenCover.{v}) [Finite C.I₀] (V : X.Opens) (U : Z.Opens)
    (hU : q ⁻¹ᵁ V = U) [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι]
    (f : ∀ i, C.X i) (hf : ∀ i, C.f i ⁻¹ᵁ U = PrimeSpectrum.basicOpen (f i))
    (p : X ⟶ Spec (.of R)) (pZ : Z ⟶ Spec (.of R)) (hpZ : q ≫ p = pZ)
    (s : I → Γ(U.toScheme, ⊤)) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X)
      (G : pullback β q ⟶ ProjectiveSpace R (Option I)),
      Blowup.AdmissibleSequence V β ∧ IsProper β ∧ IsIso (β ∣_ V) ∧
      (Dense (V : Set X) → Dense ((β ⁻¹ᵁ V : Y.Opens) : Set Y)) ∧
      IsSchemeTheoreticallyDominant ((pullback.snd β q) ⁻¹ᵁ U).ι ∧
      G ≫ ProjectiveSpace.toSpec R (Option I) = pullback.snd β q ≫ pZ ∧
      ((pullback.snd β q) ⁻¹ᵁ U).ι ≫ G =
        ((pullback.snd β q) ∣_ U) ≫ AffineTuple.map (U.ι ≫ pZ) s := by
  subst U pZ
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian q
  have hlocal := fun i ↦ exists_principalRestriction_extension (C.X i)
    (C.f i ⁻¹ᵁ q ⁻¹ᵁ V) (f i) (hf i) (C.f i ≫ q ≫ p)
      ((C.f i ∣_ q ⁻¹ᵁ V).appTop ∘ s)
  choose J B F hJ hbase hagree using hlocal
  let : Finite C.openCover.I₀ := inferInstanceAs (Finite C.I₀)
  apply Blowup.exists_ambient_extension_of_finite_cover q C.openCover V p
    (ProjectiveSpace.toSpec R (Option I))
    (AffineTuple.map ((q ⁻¹ᵁ V).ι ≫ q ≫ p) s) J B F hJ
  · intro i
    exact hbase i
  · intro i
    exact (hagree i).trans
      (congrArg (fun k ↦ ((B i).map ∣_ (C.f i ⁻¹ᵁ q ⁻¹ᵁ V)) ≫ k)
        (affineTuple_map_restrict (C.f i) (q ⁻¹ᵁ V) (q ≫ p) s))

/-- Transporting an extension across an actual source isomorphism retains
both its protected-open agreement and the local schematic-density assertion. -/
private theorem transport_open_extension {A B Z P : Scheme.{u}} (e : A ≅ B)
    (f : A ⟶ Z) (g : B ⟶ Z) (he : e.hom ≫ g = f) (U : Z.Opens)
    [IsSchemeTheoreticallyDominant (f ⁻¹ᵁ U).ι]
    (F : A ⟶ P) (a : U.toScheme ⟶ P)
    (hF : (f ⁻¹ᵁ U).ι ≫ F = (f ∣_ U) ≫ a) :
    IsSchemeTheoreticallyDominant (g ⁻¹ᵁ U).ι ∧
      (g ⁻¹ᵁ U).ι ≫ e.inv ≫ F = (g ∣_ U) ≫ a := by
  subst f
  let : IsSchemeTheoreticallyDominant (e.hom ⁻¹ᵁ g ⁻¹ᵁ U).ι := by
    simpa only [Scheme.Hom.comp_preimage] using
      (inferInstance : IsSchemeTheoreticallyDominant ((e.hom ≫ g) ⁻¹ᵁ U).ι)
  let r := e.hom ∣_ g ⁻¹ᵁ U
  have hd : IsSchemeTheoreticallyDominant (r ≫ (g ⁻¹ᵁ U).ι) := by
    dsimp only [r]
    rw [morphismRestrict_ι]
    infer_instance
  refine ⟨IsSchemeTheoreticallyDominant.of_comp_right r (g ⁻¹ᵁ U).ι, ?_⟩
  apply (cancel_epi r).mp
  calc
    r ≫ (g ⁻¹ᵁ U).ι ≫ e.inv ≫ F = ((e.hom ≫ g) ⁻¹ᵁ U).ι ≫ F := by
      dsimp only [r]
      rw [← Category.assoc (e.hom ∣_ g ⁻¹ᵁ U) (g ⁻¹ᵁ U).ι,
        morphismRestrict_ι]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.comp_preimage]
    _ = ((e.hom ≫ g) ∣_ U) ≫ a := hF
    _ = r ≫ (g ∣_ U) ≫ a := by rw [morphismRestrict_comp, Category.assoc]

/-- A finite tuple on the intersection with a protected ambient open extends
projectively over the given open part after a proper ambient morphism that
is an isomorphism on the whole protected open. Density is asserted only in
that open part. No density hypothesis on either original ambient open is needed. -/
theorem exists_ambient_projective_extension {X : Scheme.{u}} [IsNoetherian X]
    (W V : X.Opens) (p : X ⟶ Spec (.of R))
    (s : I → Γ((W.ι ⁻¹ᵁ V).toScheme, ⊤)) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X)
      (G : pullback β W.ι ⟶ ProjectiveSpace R (Option I)),
      Blowup.AdmissibleSequence V β ∧ IsProper β ∧ IsIso (β ∣_ V) ∧
      (Dense (V : Set X) → Dense ((β ⁻¹ᵁ V : Y.Opens) : Set Y)) ∧
      IsSchemeTheoreticallyDominant ((pullback.snd β W.ι) ⁻¹ᵁ W.ι ⁻¹ᵁ V).ι ∧
      G ≫ ProjectiveSpace.toSpec R (Option I) = pullback.snd β W.ι ≫ W.ι ≫ p ∧
      ((pullback.snd β W.ι) ⁻¹ᵁ W.ι ⁻¹ᵁ V).ι ≫ G =
        ((pullback.snd β W.ι) ∣_ W.ι ⁻¹ᵁ V) ≫
          AffineTuple.map ((W.ι ⁻¹ᵁ V).ι ≫ W.ι ≫ p) s := by
  classical
  let : CompactSpace W.toScheme := by
    change CompactSpace (W : Set X)
    infer_instance
  let : IsNoetherian W.toScheme := ⟨⟩
  let T := W.ι ⁻¹ᵁ V
  let J := IdealSheafData.vanishingIdeal T.compl
  have hJ : J.comap T.ι = ⊤ :=
    Blowup.BlowupDatum.comap_eq_top_of_disjoint T
      (by
        change Disjoint (T : Set W.toScheme) (T.compl : Set W.toScheme)
        exact Set.disjoint_left.mpr (fun _ hx hnot ↦ hnot hx))
  let K := J.map W.ι
  have hKV : K.comap V.ι = ⊤ :=
    J.map_comap_eq_top_of_comap_eq_top W.ι V hJ
  have hK : K.comap W.ι = J := J.comap_map_of_isOpenImmersion W.ι
  let B := Blowup.blowupDatum K
  let L := K.comap W.ι
  let BL := Blowup.flatPullbackDatum B W.ι
  let q := pullback.fst B.map W.ι
  have hq : q ≫ B.map = BL.map ≫ W.ι := pullback.condition
  have hsupp : L.support.compl = T := by
    rw [show L = J from hK]
    change T.compl.compl = T
    exact TopologicalSpace.Opens.compl_compl T
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
  let : IsProper BL.map := BL.isProper_of_isLocallyNoetherian
  let : IsLocallyNoetherian BL.Y := LocallyOfFiniteType.isLocallyNoetherian BL.map
  let : CompactSpace BL.Y := QuasiCompact.compactSpace_of_compactSpace BL.map
  let : IsNoetherian BL.Y := ⟨⟩
  let U := BL.map ⁻¹ᵁ T
  let V₁ := B.map ⁻¹ᵁ V
  have hU : q ⁻¹ᵁ V₁ = U := congrArg (fun z ↦ z ⁻¹ᵁ V) hq
  let : IsSchemeTheoreticallyDominant U.ι := by
    have h := BL.exceptionalComplement_isSchemeTheoreticallyDominant
    change IsSchemeTheoreticallyDominant (BL.map ⁻¹ᵁ L.support.compl).ι at h
    rwa [hsupp] at h
  obtain ⟨t, ht⟩ := Blowup.BoundaryCover.exists_finite_cover_of_isNoetherian L BL
  choose idx hidx hcover using ht
  let C : BL.Y.AffineOpenCover := {
    I₀ := {k // k ∈ t}
    X := fun k ↦ Blowup.BoundaryCover.ring L k.val
    f := fun k ↦ Blowup.BoundaryCover.chart L BL k.val
    idx := fun y ↦ ⟨idx y, hidx y⟩
    covers := hcover }
  let f : ∀ i, C.X i := fun i ↦ algebraMap Γ(W.toScheme, i.val.1) (C.X i) i.val.2
  have hf : ∀ i, C.f i ⁻¹ᵁ U = PrimeSpectrum.basicOpen (f i) := by
    intro i
    have h := Blowup.BoundaryCover.chart_preimage_complement L BL i.val
    rw [hsupp, Scheme.Hom.comp_preimage] at h
    exact h
  obtain ⟨Y, β, F, hseq, hβ, hβV, htop, hd, hFp, hF⟩ :=
    exists_ambient_extension_of_principal_affine_cover q C V₁ U hU f hf
      (B.map ≫ p) (BL.map ≫ W.ι ≫ p)
      (by simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ p) hq)
      ((BL.map ∣_ T).appTop ∘ s)
  let : IsProper β := hβ
  let : IsSchemeTheoreticallyDominant ((pullback.snd β q) ⁻¹ᵁ U).ι := hd
  let e := pullbackRightPullbackFstIso B.map W.ι β
  have he : e.hom ≫ pullback.snd (β ≫ B.map) W.ι =
      pullback.snd β q ≫ BL.map := pullbackRightPullbackFstIso_hom_snd B.map W.ι β
  have hF' : ((pullback.snd β q ≫ BL.map) ⁻¹ᵁ T).ι ≫ F =
      ((pullback.snd β q ≫ BL.map) ∣_ T) ≫
        AffineTuple.map (T.ι ≫ W.ι ≫ p) s := by
    rw [morphismRestrict_comp]
    exact hF.trans (congrArg (fun z ↦ ((pullback.snd β q) ∣_ U) ≫ z)
      (affineTuple_map_restrict BL.map T (W.ι ≫ p) s))
  let : IsSchemeTheoreticallyDominant ((pullback.snd β q ≫ BL.map) ⁻¹ᵁ T).ι := by
    simpa only [Scheme.Hom.comp_preimage] using hd
  obtain ⟨hd', hF'⟩ := transport_open_extension e (pullback.snd β q ≫ BL.map)
    (pullback.snd (β ≫ B.map) W.ι) he T F
    (AffineTuple.map (T.ι ≫ W.ι ≫ p) s) hF'
  refine ⟨Y, β ≫ B.map, e.inv ≫ F,
    (Blowup.AdmissibleSequence.single B V hKV).comp hseq,
    inferInstance, ?_, ?_, hd', ?_, hF'⟩
  · rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' hβV (B.restrict_isIso_of_comap_eq_top V hKV)
  · intro hV
    exact htop (B.preimage_open_dense V hV)
  · rw [Category.assoc, hFp]
    dsimp only [e, q, BL, Blowup.flatPullbackDatum]
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ W.ι ≫ p)
      (pullbackRightPullbackFstIso_inv_snd_snd B.map W.ι β)

end AlgebraicGeometry.Scheme.RationalCoordinates
