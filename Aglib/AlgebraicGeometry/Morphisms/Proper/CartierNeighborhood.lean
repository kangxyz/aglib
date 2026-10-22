/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.QuasiFinite
public import Aglib.AlgebraicGeometry.Morphisms.Proper.ConnectedFibres
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Detection
public import Aglib.AlgebraicGeometry.IdealSheaf.Restriction
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Nakayama
public import Aglib.AlgebraicGeometry.Modules.Coherent.StalkFinite
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Support
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# A Cartier first-order test for a proper birational isomorphism neighborhood

For the original square, epimorphy of the original ideal map after pullback to
its closed source spreads to a source neighborhood by finite-type cokernel
support and local Nakayama. The canonical inclusion detects the original
inverse-image ideal there. The resulting isolated point of every relevant
fiber is clopen; connected proper birational fibers make it the whole fiber.
The original morphism is therefore an isomorphism over a target neighborhood
of the entire original divisor. No flat pullback of kernels is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme

private theorem finiteType_of_rankOne {X : Scheme.{u}} (M : X.Modules)
    (hM : IsLocallyRankOne X M) : affineLocallyFiniteType X M := by
  obtain ⟨q, hq, hI⟩ := hM
  let : IsFiniteLocallyFree X M := ⟨q, hq, ⟨fun i ↦
    ⟨Finite.of_equiv PUnit (hI i).some.symm⟩⟩⟩
  exact coherent_of_finiteLocallyFree M

private theorem finite_stalk_of_locallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (M : X.Modules) (hM : affineLocallyFiniteType X M) (x : X) :
    Module.Finite (X.presheaf.stalk x) ((moduleStalk X x).obj M) := by
  obtain ⟨i, y, rfl⟩ := X.affineOpenCover.openCover.exists_eq x
  let j := X.affineOpenCover.f i
  let : IsNoetherianRing (X.affineOpenCover.X i) :=
    isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion j)
  let N := (finiteTypeSheavesRestriction j).obj ⟨M, hM⟩
  let P := (moduleStalk (Spec (X.affineOpenCover.X i)) y).obj N.obj
  let : Module.Finite ((Spec (X.affineOpenCover.X i)).presheaf.stalk y) P :=
    Modules.Stalk.coherent_affine_stalk_finite _ N y
  let : Module.Finite (X.presheaf.stalk (j y))
      ((ModuleCat.restrictScalars (j.stalkMap y).hom).obj P) :=
    Modules.Stalk.finite_restrictScalars (j.stalkMap y).hom
      (ConcreteCategory.bijective_of_isIso _).2 P
  let e := (restrictModuleStalkIso j y).app M
  exact Module.Finite.of_surjective
    (hM := Modules.Stalk.finite_restrictScalars (j.stalkMap y).hom
      (ConcreteCategory.bijective_of_isIso _).2 P)
    e.hom.hom e.toLinearEquiv.surjective

private theorem epi_of_closed_scalarExtension
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S)
    (hr : Function.Surjective r) (hJ : RingHom.ker r ≤ (⊥ : Ideal R).jacobson)
    {M N : ModuleCat.{u} R} (p : M ⟶ N) [Module.Finite R N]
    [Epi ((ModuleCat.extendScalars r).map p)] : Epi p := by
  let I := RingHom.ker r
  let P : Submodule R N := I • ⊤
  let Q : ModuleCat.{u} R := ModuleCat.of R (N ⧸ P)
  have hQ : RingHom.ker r ≤ Module.annihilator R Q := by
    intro a ha
    rw [Module.mem_annihilator]
    intro n
    exact Module.isTorsionBySet_quotient_ideal_smul N I (x := n) (a := ⟨a, ha⟩)
  obtain ⟨Q', ⟨e⟩⟩ :=
    (ModuleCat.mem_essImage_restrictScalars_iff_ker_le_annihilator r hr Q).mpr hQ
  let q : N ⟶ (ModuleCat.restrictScalars r).obj Q' := ModuleCat.ofHom P.mkQ ≫ e.inv
  let : Epi (ModuleCat.ofHom P.mkQ) :=
    (ModuleCat.epi_iff_surjective _).mpr P.mkQ_surjective
  let : Epi q := by dsimp [q]; infer_instance
  let adj := ModuleCat.extendRestrictScalarsAdj r
  let q' : (ModuleCat.extendScalars r).obj N ⟶ Q' := (adj.homEquiv N Q').symm q
  have hq : adj.unit.app N ≫ (ModuleCat.restrictScalars r).map q' = q := by
    change adj.homEquiv N Q' q' = q
    exact (adj.homEquiv N Q').apply_symm_apply q
  have : Epi (adj.unit.app N ≫ (ModuleCat.restrictScalars r).map q') := by
    rw [hq]
    infer_instance
  let : Epi ((ModuleCat.restrictScalars r).map q') := epi_of_epi (adj.unit.app N) _
  let : Epi (adj.unit.app M) := ModuleCat.extendRestrictScalarsAdj_unit_epi r hr M
  have hnat : p ≫ adj.unit.app N = adj.unit.app M ≫
      (ModuleCat.restrictScalars r).map ((ModuleCat.extendScalars r).map p) :=
    adj.unit.naturality p
  have hpq : Epi (p ≫ q) := by
    rw [← hq, ← Category.assoc, hnat]
    infer_instance
  have hcomp : Epi ((p ≫ ModuleCat.ofHom P.mkQ) ≫ e.inv) := by
    simpa only [q, Category.assoc] using hpq
  have hquot : Epi (p ≫ ModuleCat.ofHom P.mkQ) := (epi_comp_iff_of_isIso _ _).mp hcomp
  apply (ModuleCat.epi_iff_surjective p).mpr
  exact LinearMap.surjective_of_surjective_comp_mkQ p.hom I hJ
    ((ModuleCat.epi_iff_surjective _).mp hquot)

private theorem exists_open_epi_of_closedPullback_epi
    {E X : Scheme.{u}} [IsLocallyNoetherian X]
    (i : E ⟶ X) [IsClosedImmersion i] {M N : X.Modules} (φ : M ⟶ N)
    (hM : affineLocallyFiniteType X M) (hN : affineLocallyFiniteType X N)
    [Epi ((Modules.pullback i).map φ)] :
    ∃ U : X.Opens, Set.range i ⊆ U ∧ Epi ((Modules.restrictFunctor U.ι).map φ) := by
  have hepi (y : E) : Epi ((moduleStalk X (i y)).map φ) := by
    let : Module.Finite (X.presheaf.stalk (i y)) ((moduleStalk X (i y)).obj N) :=
      finite_stalk_of_locallyNoetherian N hN (i y)
    let e := pullbackModuleStalkIso i y
    have hscalar : Epi (e.hom.app M ≫
        (ModuleCat.extendScalars (i.stalkMap y).hom).map ((moduleStalk X (i y)).map φ)) := by
      change Epi (e.hom.app M ≫
        (moduleStalk X (i y) ⋙ ModuleCat.extendScalars (i.stalkMap y).hom).map φ)
      rw [← e.hom.naturality]
      change Epi ((moduleStalk E y).map ((Modules.pullback i).map φ) ≫ e.hom.app N)
      infer_instance
    let : Epi ((ModuleCat.extendScalars (i.stalkMap y).hom).map
        ((moduleStalk X (i y)).map φ)) := epi_of_epi (e.hom.app M) _
    apply epi_of_closed_scalarExtension (i.stalkMap y).hom (i.stalkMap_surjective y)
      ?_ ((moduleStalk X (i y)).map φ)
    exact (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)).trans
      (IsLocalRing.maximalIdeal_le_jacobson _)
  let Q := cokernel φ
  have hQ : affineLocallyFiniteType X Q := (affineLocallyFiniteType X).prop_cokernel φ hM hN
  let U : X.Opens := ⟨(Modules.support Q)ᶜ,
    (isClosed_support_of_affineLocallyFiniteType hQ).isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    let : Epi ((moduleStalk X (i y)).map φ) := hepi y
    have hz : IsZero ((moduleStalk X (i y)).obj Q) :=
      (isZero_cokernel_of_epi ((moduleStalk X (i y)).map φ)).of_iso
        (PreservesCokernel.iso (moduleStalk X (i y)) φ)
    have ha := (forget₂ (ModuleCat (X.presheaf.stalk (i y))) AddCommGrpCat.{u}).map_isZero hz
    change ¬ ¬ IsZero ((stalkFunctor X (i y)).obj Q)
    exact not_not.mpr (ha.of_iso ((moduleStalkForgetIso X (i y)).app Q).symm)
  · have hz : IsZero ((Modules.restrictFunctor U.ι).obj Q) := by
      change supportedAway U.ι Q
      apply (supportedAway_iff_stalks U.ι Q).mpr
      intro x
      exact not_not.mp x.property
    exact Preadditive.epi_of_isZero_cokernel _
      (hz.of_iso (PreservesCokernel.iso (Modules.restrictFunctor U.ι) φ).symm)

private theorem restricted_idealPullback_epi
    {E D W B : Scheme.{u}} (i : E ⟶ W) (j : D ⟶ B) (q : W ⟶ B) (a : E ⟶ D)
    (h : a ≫ j = i ≫ q) (U : W.Opens)
    [Epi ((Modules.restrictFunctor U.ι).map (idealPullbackMap j i q a h))] :
    Epi (idealPullbackMap j (i ∣_ U) (U.ι ≫ q) ((i ⁻¹ᵁ U).ι ≫ a)
      (by rw [Category.assoc, h, ← Category.assoc, ← morphismRestrict_ι, Category.assoc])) := by
  let φ := idealPullbackMap j i q a h
  let e := Modules.restrictFunctorIsoPullback U.ι
  have : Epi (e.hom.app _ ≫ (Modules.pullback U.ι).map φ) := by
    rw [← e.hom.naturality]
    infer_instance
  let : Epi ((Modules.pullback U.ι).map φ) := epi_of_epi (e.hom.app _) _
  rw [← idealPullbackMap_comp j i (i ∣_ U) q U.ι a (i ⁻¹ᵁ U).ι h
    (morphismRestrict_ι i U).symm]
  infer_instance

private theorem preimage_range_eq_of_idealPullback_epi
    {E D W B : Scheme.{u}} (i : E ⟶ W) (j : D ⟶ B) (q : W ⟶ B) (a : E ⟶ D)
    (h : a ≫ j = i ≫ q) [IsClosedImmersion i] [IsClosedImmersion j]
    [Epi (idealPullbackMap j i q a h)] : q ⁻¹' Set.range j = Set.range i := by
  have hk := ker_comap_eq_of_idealPullbackMap_epi j i q a h
  have hs := congrArg (fun J : W.IdealSheafData ↦ (J.support : Set W)) hk
  simpa only [IdealSheafData.support_comap, Closeds.coe_preimage,
    Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq,
    i.isClosedEmbedding.isClosed_range.closure_eq] using hs

private theorem quasiFiniteAt_of_isolating_open
    {E D W B : Scheme.{u}} (i : E ⟶ W) (j : D ⟶ B) (q : W ⟶ B)
    (e : E ≅ D) (h : e.hom ≫ j = i ≫ q)
    [IsClosedImmersion j] [LocallyOfFiniteType q]
    (U : W.Opens) (hiU : Set.range i ⊆ U)
    (hpre : (U.ι ≫ q) ⁻¹' Set.range j = Set.range (i ∣_ U)) (a : E) :
    q.QuasiFiniteAt (i a) := by
  have hisolate (x : W) (hx : x ∈ U) (hq : q x = q (i a)) : x = i a := by
    have hqa : j (e.hom a) = q (i a) := congrArg (fun k : E ⟶ B ↦ k a) h
    have hxpre : (⟨x, hx⟩ : U.toScheme) ∈ (U.ι ≫ q) ⁻¹' Set.range j :=
      ⟨e.hom a, hqa.trans hq.symm⟩
    rw [hpre] at hxpre
    obtain ⟨b, hb⟩ := hxpre
    have hix : i b.val = x := by
      calc
        _ = ((i ∣_ U) b).val :=
          (congrArg (fun k ↦ k b) (morphismRestrict_ι i U)).symm
        _ = _ := congrArg Subtype.val hb
    have he : e.hom b.val = e.hom a := j.injective (by
      calc
        _ = q (i b.val) := congrArg (fun k : E ⟶ B ↦ k b.val) h
        _ = q x := congrArg q hix
        _ = q (i a) := hq
        _ = _ := hqa.symm)
    exact hix.symm.trans (congrArg i (e.hom.injective he))
  have hset : (q.fiberι (q (i a))) ⁻¹' (U : Set W) = {q.asFiber (i a)} := by
    ext z
    constructor
    · intro hz
      apply Set.mem_singleton_iff.mpr
      apply (q.fiberι _).isEmbedding.injective
      rw [q.fiberι_asFiber]
      exact hisolate _ hz (q.fiberHomeo _ z).property
    · intro hz
      rw [Set.mem_singleton_iff.mp hz]
      change q.fiberι _ (q.asFiber (i a)) ∈ U
      rw [q.fiberι_asFiber]
      exact hiU ⟨a, rfl⟩
  apply (Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber (f := q)).mpr
  rw [← hset]
  exact U.isOpen.preimage (q.fiberι _).continuous

private theorem finite_fibre_of_connected_of_quasiFiniteAt
    {W B : Scheme.{u}} (q : W ⟶ B) [LocallyOfFiniteType q]
    [GeometricallyConnected q] (x : W) (hx : q.QuasiFiniteAt x) :
    (q ⁻¹' {q x}).Finite := by
  have hall : ({q.asFiber x} : Set (q.fiber (q x))) = Set.univ :=
    hx.isClopen_singleton_asFiber.eq_univ ⟨q.asFiber x, rfl⟩
  apply (Set.finite_singleton x).subset
  intro y hy
  let z := (q.fiberHomeo (q x)).symm ⟨y, hy⟩
  have hz : z = q.asFiber x := by
    apply Set.mem_singleton_iff.mp
    rw [hall]
    exact Set.mem_univ _
  have hval : y = x := by
    calc
      _ = q.fiberι (q x) z := (q.fiberι_fiberHomeo_symm (q x) ⟨y, hy⟩).symm
      _ = _ := by rw [hz, q.fiberι_asFiber]
  exact hval

private theorem isIso_restrict_iSup
    {W B : Scheme.{u}} (q : W ⟶ B) {D : Type u} (V : D → B.Opens)
    (hV : ∀ d, IsIso (q ∣_ V d)) : IsIso (q ∣_ iSup V) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro y
  obtain ⟨d, hyd⟩ := Opens.mem_iSup.mp y.property
  let L := iSup V
  let U : L.toScheme.Opens := L.ι ⁻¹ᵁ V d
  refine ⟨U, hyd, ?_⟩
  have himage : L.ι ''ᵁ U = V d := by
    rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι,
      inf_eq_right.mpr (le_iSup V d)]
  have hs : IsIso (q ∣_ L.ι ''ᵁ U) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictEq q himage)).mpr (hV d)
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict q L U)).mpr hs

/-- First-order epimorphy of the original canonical ideal comparison along
isomorphic actual Cartier divisors forces the original proper birational map
to be an isomorphism on a target neighborhood of the original divisor. -/
theorem exists_isIso_restrict_of_isProper_birational_of_cartier_pullback_epi
    {E D W B : Scheme.{u}} [IsIntegral W] [IsIntegral B] [IsLocallyNoetherian B]
    (q : W ⟶ B) [IsProper q] [IsDominant q] (hB : NormalStalks B)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (i : E ⟶ W) (j : D ⟶ B) (hE : Hom.IsEffectiveCartier i)
    (hD : Hom.IsEffectiveCartier j) (e : E ≅ D) (h : e.hom ≫ j = i ≫ q)
    [Epi ((Modules.pullback i).map (idealPullbackMap j i q e.hom h))] :
    ∃ V : B.Opens, Set.range j ⊆ V ∧ IsIso (q ∣_ V) := by
  let : IsClosedImmersion i := hE.isClosedImmersion
  let : IsClosedImmersion j := hD.isClosedImmersion
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian q
  let : GeometricallyConnected q := geometricallyConnected_of_isProper_birational q hB hff
  let φ := idealPullbackMap j i q e.hom h
  have hM := finiteType_of_rankOne ((Modules.pullback q).obj (idealModule j))
    (pullback_locallyRankOne q _ hD.isLocallyRankOne)
  have hN := finiteType_of_rankOne (idealModule i) hE.isLocallyRankOne
  obtain ⟨U, hiU, hU⟩ := exists_open_epi_of_closedPullback_epi i φ hM hN
  let : Epi ((Modules.restrictFunctor U.ι).map φ) := hU
  have hrestrict : ((i ⁻¹ᵁ U).ι ≫ e.hom) ≫ j = (i ∣_ U) ≫ (U.ι ≫ q) := by
    rw [Category.assoc, h, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  let : Epi (idealPullbackMap j (i ∣_ U) (U.ι ≫ q) ((i ⁻¹ᵁ U).ι ≫ e.hom)
      hrestrict) := restricted_idealPullback_epi i j q e.hom h U
  have hpre := preimage_range_eq_of_idealPullback_epi (i ∣_ U) j (U.ι ≫ q)
    ((i ⁻¹ᵁ U).ι ≫ e.hom) hrestrict
  have hpoint (d : D) : ∃ V : B.Opens, j d ∈ V ∧ IsIso (q ∣_ V) := by
    let a := e.inv d
    have hqa : q (i a) = j d := by
      have hh := congrArg (fun k : E ⟶ B ↦ k a) h
      change j (e.hom a) = q (i a) at hh
      have he := congrArg (fun k : D ⟶ D ↦ k d) e.inv_hom_id
      change e.hom (e.inv d) = d at he
      exact hh.symm.trans (congrArg j he)
    have hf := finite_fibre_of_connected_of_quasiFiniteAt q (i a)
      (quasiFiniteAt_of_isolating_open i j q e h U hiU hpre a)
    obtain ⟨V, hxV, hV⟩ :=
      exists_isIso_restrict_of_isProper_birational_of_finite_preimage_singleton q hB hff
        (q (i a)) hf
    exact ⟨V, hqa ▸ hxV, hV⟩
  choose V hjV hV using hpoint
  refine ⟨iSup V, ?_, isIso_restrict_iSup q V hV⟩
  rintro _ ⟨d, rfl⟩
  exact Opens.mem_iSup.mpr ⟨d, hjV d⟩

/-- Isomorphy after the original closed pullback suffices for the same
neighborhood, with no assumed inverse-image ideal equality or flatness. -/
theorem exists_isIso_restrict_of_isProper_birational_of_cartier_pullback_isIso
    {E D W B : Scheme.{u}} [IsIntegral W] [IsIntegral B] [IsLocallyNoetherian B]
    (q : W ⟶ B) [IsProper q] [IsDominant q] (hB : NormalStalks B)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (i : E ⟶ W) (j : D ⟶ B) (hE : Hom.IsEffectiveCartier i)
    (hD : Hom.IsEffectiveCartier j) (e : E ≅ D) (h : e.hom ≫ j = i ≫ q)
    [IsIso ((Modules.pullback i).map (idealPullbackMap j i q e.hom h))] :
    ∃ V : B.Opens, Set.range j ⊆ V ∧ IsIso (q ∣_ V) :=
  exists_isIso_restrict_of_isProper_birational_of_cartier_pullback_epi
    q hB hff i j hE hD e h

end AlgebraicGeometry.Scheme
