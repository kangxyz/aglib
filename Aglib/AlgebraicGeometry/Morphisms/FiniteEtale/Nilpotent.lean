/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperResidue.Existence
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.Fullness
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.Isomorphism
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalLocalCoverMaps
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalOpenCoverColimits
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalGluedCover
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.SpecKernel
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.RingTheory.Descent.Nilpotent

/-!
# Finite étale covers across nilpotent thickenings

Formal étaleness gives the actual tensor-Hom bijection across a nilpotent
quotient. Together with the constructed affine cover lifts, this proves an
equivalence for the literal affine quotient pullback. The auxiliary uniqueness
lemma applies to actual unramified targets after any surjective base change.

No Noetherian, Henselian or completeness assumption is used. The fixed affine
object-existence provider is temporarily imported from ProperResidue.Existence;
its construction is not duplicated. Local object lifts, unique overlap maps
and Cartesian transition squares supply the actual global nilpotent cover.
Proper formal algebraization remains a separate obligation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.Nilpotent

universe u

-- The proof keeps the actual diagonal pullback and its first projection.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unramified_hom_ext
    {X X₀ Z S : Scheme.{u}} (i : X₀ ⟶ X) [Surjective i]
    (p : Z ⟶ S) [FormallyUnramified p] [LocallyOfFiniteType p]
    (g h : X ⟶ Z) (hbase : g ≫ p = h ≫ p) (heq : i ≫ g = i ≫ h) : g = h := by
  let a : X ⟶ pullback p p := pullback.lift g h hbase
  let j : pullback a (pullback.diagonal p) ⟶ X := pullback.fst _ _
  have hjopen : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hia : i ≫ a = (i ≫ g) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · simp [a]
    · simpa [a] using heq.symm
  let l : X₀ ⟶ pullback a (pullback.diagonal p) := pullback.lift i (i ≫ g) hia
  have hlj : l ≫ j = i := by simp [l, j]
  have hjsurj : Surjective j := by
    constructor
    intro x
    obtain ⟨z, hz⟩ := i.surjective x
    exact ⟨l z, (congrArg (fun k : X₀ ⟶ X ↦ k z) hlj).trans hz⟩
  have : IsIso j :=
    (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨hjopen, hjsurj⟩
  apply (cancel_epi j).mp
  have hj : j ≫ a = pullback.snd a (pullback.diagonal p) ≫ pullback.diagonal p :=
    pullback.condition
  calc
    j ≫ g = (j ≫ a) ≫ pullback.fst p p := by simp [a]
    _ = pullback.snd a (pullback.diagonal p) := by rw [hj]; simp
    _ = (j ≫ a) ≫ pullback.snd p p := by rw [hj]; simp
    _ = j ≫ h := by simp [a]

private theorem overPullback_map_injective_of_unramified
    {S T : Scheme.{u}} (f : T ⟶ S) [Surjective f]
    {A B : Over S} [FormallyUnramified B.hom] [LocallyOfFiniteType B.hom]
    {g h : A ⟶ B} (he : (Over.pullback f).map g = (Over.pullback f).map h) : g = h := by
  apply Over.OverMorphism.ext
  apply unramified_hom_ext (pullback.fst A.hom f) B.hom g.left h.left
    ((Over.w g).trans (Over.w h).symm)
  calc
    pullback.fst A.hom f ≫ g.left =
        ((Over.pullback f).map g).left ≫ pullback.fst B.hom f :=
      (pullback.lift_fst _ _ _).symm
    _ = ((Over.pullback f).map h).left ≫ pullback.fst B.hom f :=
      congrArg (fun k ↦ k.left ≫ pullback.fst B.hom f) he
    _ = pullback.fst A.hom f ≫ h.left := pullback.lift_fst _ _ _

private theorem baseChange_faithful_of_surjective
    {S T : Scheme.{u}} (f : T ⟶ S) [Surjective f] : (baseChange f).Faithful where
  map_injective := by
    intro X Y g h he
    apply ObjectProperty.hom_ext
    apply overPullback_map_injective_of_unramified f
    exact congrArg (fun k ↦ k.hom) he

private theorem nilpotent_tensorMap_bijective
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallyEtale R A]
    (I : Ideal R) (hI : IsNilpotent I) :
    Function.Bijective
      (fun g : A →ₐ[R] B ↦
        (Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I)) g :
          (R ⧸ I) ⊗[R] A →ₐ[R ⧸ I] (R ⧸ I) ⊗[R] B)) := by
  let J := I.map (algebraMap R B)
  have hJ : IsNilpotent J := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    change (I.map (algebraMap R B)) ^ n = ⊥
    rw [← Ideal.map_pow, show I ^ n = ⊥ from hn, Ideal.map_bot]
  let eB := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  constructor
  · intro g₁ g₂ h
    apply Algebra.FormallyUnramified.ext J hJ
    intro x
    apply eB.injective
    have h' := congrArg (fun f ↦ f (1 ⊗ₜ[R] x)) h
    simpa only [eB, J, Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply] using h'
  · intro f
    let f' : A →ₐ[R] B ⧸ J :=
      (eB.symm.toAlgHom.restrictScalars R).comp
        ((f.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J hJ f'
    refine ⟨g, ?_⟩
    apply Algebra.TensorProduct.ext_ring
    ext a
    have h := congrArg eB (AlgHom.congr_fun hg a)
    simpa [f', eB, J] using h

variable (R : Type u) [CommRing R] (I : Ideal R)

-- The affine coordinate comparisons retain their original scalar structures.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nilpotent_affine_fibre_hom_lift (hI : IsNilpotent I)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.FormallyEtale R A]
    (φ : pullback (Spec.algebraMap R B) (Spec.algebraMap R (R ⧸ I)) ⟶
      pullback (Spec.algebraMap R A) (Spec.algebraMap R (R ⧸ I)))
    (hφ : φ ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ g : A →ₐ[R] B, Adic.fibreMap (T := R ⧸ I) g = φ := by
  let ψ := (Adic.fibreIso R (R ⧸ I) B).inv ≫ φ ≫ (Adic.fibreIso R (R ⧸ I) A).hom
  have hψ : ψ ≫ Spec.algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] A) =
      Spec.algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] B) := by
    simp only [ψ, Category.assoc, Adic.fibreIso_hom_base, hφ, Adic.fibreIso_inv_base]
  let q : (R ⧸ I) ⊗[R] A →ₐ[R ⧸ I] (R ⧸ I) ⊗[R] B :=
    Spec.homEquivAlgHom ⟨ψ, hψ⟩
  have hq : Spec.map (CommRingCat.ofHom q.toRingHom) = ψ :=
    congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨ψ, hψ⟩)
  obtain ⟨g, hg⟩ := (nilpotent_tensorMap_bijective I hI).surjective q
  dsimp only at hg
  refine ⟨g, ?_⟩
  apply (cancel_epi (Adic.fibreIso R (R ⧸ I) B).inv).mp
  rw [Adic.fibreIso_inv_fibreMap, hg, hq]
  simp [ψ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual morphism between nilpotent affine restrictions lifts over
its original base. No arrow-lifting hypothesis is assumed. -/
theorem quotient_baseChange_full (hI : IsNilpotent I) :
    (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Full where
  map_surjective {Y Z} φ := by
    let F := baseChange (Spec.algebraMap R (R ⧸ I))
    let eY := Adic.specCoverIso R Y
    let eZ := Adic.specCoverIso R Z
    let φ' : F.obj (Adic.specCover R Y) ⟶ F.obj (Adic.specCover R Z) :=
      F.map eY.hom ≫ φ ≫ F.map eZ.inv
    let : Algebra R (Adic.sections R Y) := Adic.sectionsAlgebra R Y
    let : Algebra R (Adic.sections R Z) := Adic.sectionsAlgebra R Z
    have : Algebra.Etale R (Adic.sections R Z) := Adic.sections_etale R Z
    obtain ⟨g, hg⟩ := nilpotent_affine_fibre_hom_lift R I hI
      (A := Adic.sections R Z) (B := Adic.sections R Y) φ'.hom.left (Over.w φ'.hom)
    let gC : Adic.specCover R Y ⟶ Adic.specCover R Z :=
      ⟨Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (Spec.map_algHom_algebraMap g)⟩
    have hgc : F.map gC = φ' := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      change Adic.fibreMap (T := R ⧸ I) g = φ'.hom.left
      exact hg
    refine ⟨eY.inv ≫ gC ≫ eZ.hom, ?_⟩
    change F.map (eY.inv ≫ gC ≫ eZ.hom) = φ
    rw [Functor.map_comp, Functor.map_comp, hgc]
    calc
      _ = φ ≫ 𝟙 (F.obj Z) := by
        simp only [φ', Category.assoc, Iso.map_inv_hom_id_assoc, Iso.map_inv_hom_id]
      _ = φ := Category.comp_id φ

/-- The literal affine quotient pullback is an equivalence for every
nilpotent ideal in every commutative base ring. -/
theorem quotient_baseChange_isEquivalence (hI : IsNilpotent I) :
    (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).IsEquivalence := by
  have hnil : I ≤ _root_.nilradical R := by
    intro x hx
    rw [_root_.mem_nilradical]
    obtain ⟨n, hn⟩ := hI
    have hn' : I ^ n = ⊥ := hn
    exact ⟨n, by simpa only [hn', Submodule.mem_bot] using Ideal.pow_mem_pow hx n⟩
  let : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hnil).surjective⟩
  let : (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Faithful :=
    baseChange_faithful_of_surjective _
  let : (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Full :=
    quotient_baseChange_full R I hI
  let : (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).EssSurj :=
    quotient_baseChange_essSurj R I hI
  exact { }

/-- The actual affine cover Hom map is bijective, with the forward map given
by the unchanged native base-change functor. -/
theorem quotient_baseChange_hom_bijective (hI : IsNilpotent I)
    (X Y : FiniteEtale (Spec (.of R))) :
    Function.Bijective ((baseChange (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map :
      (X ⟶ Y) → _) := by
  let : (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).IsEquivalence :=
    quotient_baseChange_isEquivalence R I hI
  exact ⟨Functor.map_injective _, Functor.map_surjective _⟩

private theorem baseChange_isEquivalence_of_isIso
    {X T : Scheme.{u}} (j : T ⟶ X) [IsIso j] : (baseChange j).IsEquivalence := by
  let : (baseChange j).Full := baseChange_full_of_isIso j
  let : (baseChange j).Faithful := baseChange_faithful_of_isIso j
  let e : baseChange (inv j) ⋙ baseChange j ≅ 𝟭 (FiniteEtale T) :=
    (baseChangeComp (inv j) j).symm ≪≫
      eqToIso (congrArg baseChange (IsIso.hom_inv_id j)) ≪≫ baseChangeId T
  let : (baseChange j).EssSurj :=
    ⟨fun C ↦ ⟨(baseChange (inv j)).obj C, ⟨e.app C⟩⟩⟩
  exact { }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem subscheme_chart_isPullback {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) :
    IsPullback (I.glueDataObjι U) (I.subschemeCover.f U) U.1.ι I.subschemeι := by
  apply IsOpenImmersion.isPullback
  · exact I.subschemeCover_map_subschemeι U
  · simp

private theorem ideal_nilpotent_on_affine {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : IsNilpotent I) (U : X.affineOpens) :
    IsNilpotent (I.ideal U) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  change (I.ideal U) ^ n = ⊥
  have hn' : I ^ n = ⊥ := hn
  have h := congrArg (fun J : X.IdealSheafData ↦ J.ideal U) hn'
  simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using h

private theorem subscheme_surjective_of_nilpotent {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : IsNilpotent I) : Surjective I.subschemeι := by
  obtain ⟨n, hn⟩ := hI
  have hp' : I ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  have hp : I ^ (n + 1) = ⊥ := hp'
  have hs : I.support = ⊤ := by
    rw [← I.support_pow_succ n, hp, Scheme.IdealSheafData.support_bot]
  constructor
  apply Set.range_eq_univ.mp
  simp [I.range_subschemeι, hs]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem subscheme_chart_baseChange_isEquivalence {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : IsNilpotent I) (U : X.affineOpens) :
    (baseChange (I.glueDataObjι U)).IsEquivalence := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))
  let : (baseChange q).IsEquivalence :=
    quotient_baseChange_isEquivalence Γ(X, U) (I.ideal U)
      (ideal_nilpotent_on_affine I hI U)
  let : (baseChange U.2.isoSpec.inv).IsEquivalence := baseChange_isEquivalence_of_isIso _
  change (baseChange (q ≫ U.2.isoSpec.inv)).IsEquivalence
  exact Functor.isEquivalence_of_iso (baseChangeComp U.2.isoSpec.inv q).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem subscheme_local_baseChange_isEquivalence {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : IsNilpotent I) (U : X.affineOpens) :
    (baseChange (pullback.fst U.1.ι I.subschemeι)).IsEquivalence := by
  let e := (subscheme_chart_isPullback I U).isoPullback
  have he : e.hom ≫ pullback.fst U.1.ι I.subschemeι = I.glueDataObjι U :=
    (subscheme_chart_isPullback I U).isoPullback_hom_fst
  let : (baseChange e.hom).IsEquivalence := baseChange_isEquivalence_of_isIso _
  let : (baseChange (I.glueDataObjι U)).IsEquivalence :=
    subscheme_chart_baseChange_isEquivalence I hI U
  let : (baseChange (pullback.fst U.1.ι I.subschemeι) ⋙ baseChange e.hom).IsEquivalence := by
    apply (Functor.isEquivalence_iff_of_iso
      (baseChangeComp (pullback.fst U.1.ι I.subschemeι) e.hom)).mp
    rw [he]
    infer_instance
  exact Functor.isEquivalence_of_comp_right _ (baseChange e.hom)

open PurelyInseparable.Global in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem baseChange_full_of_local_full
    {X T : Scheme.{u}} (f : T ⟶ X) [Surjective f]
    (𝒰 : X.OpenCover) [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected]
    [∀ i, (baseChange (pullback.fst (𝒰.f i) f)).Full] : (baseChange f).Full where
  map_surjective {Y Z} q := by
    let G := Over.pullback f
    let 𝒱 := 𝒰.pullback₁ Y.obj.hom
    let D := overCoverDiagram Y.obj 𝒱
    let c := overCoverCocone Y.obj 𝒱
    let hc := overCoverCoconeIsColimit Y.obj 𝒱
    have h (i : 𝒰.I₀) : ∃ g : D.obj i ⟶ Z.obj,
        G.map g = G.map (c.ι.app i) ≫ q.hom := by
      let A := (baseChange (𝒰.f i)).obj Y
      let e : D.obj i ≅ (Over.map (𝒰.f i)).obj A.obj :=
        Over.isoMk (Iso.refl _) (by
          change (𝟙 (pullback Y.obj.hom (𝒰.f i))) ≫
              (pullback.snd Y.obj.hom (𝒰.f i) ≫ 𝒰.f i) =
            pullback.fst Y.obj.hom (𝒰.f i) ≫ Y.obj.hom
          rw [Category.id_comp]
          exact pullback.condition.symm)
      let eZ : (Over.map (𝟙 X)).obj Z.obj ≅ Z.obj := (Over.mapId X).app Z.obj
      let q' := (G.mapIso e).inv ≫ (G.map (c.ι.app i) ≫ q.hom) ≫ (G.mapIso eZ).inv
      obtain ⟨g, hg⟩ := local_overMap_surjective f (𝒰.f i) (𝟙 X) (𝒰.f i)
        (Category.comp_id _) A Z q'
      refine ⟨e.hom ≫ g ≫ eZ.hom, ?_⟩
      rw [Functor.map_comp, Functor.map_comp, hg]
      simp only [q', Functor.mapIso_inv, Functor.const_obj_obj, Category.assoc,
        ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Iso.map_hom_inv_id_assoc]
      change G.map (c.ι.app i) ≫ (q.hom ≫ 𝟙 (G.obj Z.obj)) = G.map (c.ι.app i) ≫ q.hom
      exact congrArg (fun k : G.obj Y.obj ⟶ G.obj Z.obj ↦ G.map (c.ι.app i) ≫ k)
        (Category.comp_id q.hom)
    choose g hg using h
    let s : Cocone D :=
      { pt := Z.obj
        ι :=
          { app := g
            naturality i j d := by
              change D.map d ≫ g j = g i ≫ 𝟙 Z.obj
              apply overPullback_map_injective_of_unramified f (B := Z.obj)
              change G.map (D.map d ≫ g j) = G.map (g i ≫ 𝟙 Z.obj)
              rw [Category.comp_id, Functor.map_comp, hg j, hg i,
                ← Category.assoc, ← Functor.map_comp, c.w d] } }
    let g₀ : Y.obj ⟶ Z.obj := hc.desc s
    refine ⟨ObjectProperty.homMk g₀, ?_⟩
    apply ObjectProperty.hom_ext
    apply (pullbackOverCoverCoconeIsColimit Y.obj 𝒱 f).hom_ext
    intro i
    change G.map (c.ι.app i) ≫ G.map g₀ = G.map (c.ι.app i) ≫ q.hom
    rw [← Functor.map_comp, hc.fac s i]
    exact hg i

/-- Actual finite étale cover morphisms lift across a nilpotent ideal-sheaf
closed immersion on any scheme. The affine lifts are glued through unique
original overlap arrows; no flatness of the immersion is used. -/
theorem subscheme_baseChange_full {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : IsNilpotent I) : (baseChange I.subschemeι).Full := by
  let : Surjective I.subschemeι := subscheme_surjective_of_nilpotent I hI
  let (U : X.directedAffineCover.I₀) :
      (baseChange (pullback.fst (X.directedAffineCover.f U) I.subschemeι)).IsEquivalence :=
    subscheme_local_baseChange_isEquivalence I hI U
  exact baseChange_full_of_local_full I.subschemeι X.directedAffineCover

open PurelyInseparable.Global in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def localPullbackPushforwardNatIso {X T U : Scheme.{u}}
    (f : T ⟶ X) (i : U ⟶ X) :
    Over.map i ⋙ Over.pullback f ≅
      Over.pullback (pullback.fst i f) ⋙ Over.map (pullback.snd i f) :=
  NatIso.ofComponents (localPullbackPushforwardIso f i) (by
    intro A B k
    let a := localPullbackPushforwardIso f i A
    let b := localPullbackPushforwardIso f i B
    let l := (Over.pullback f).map ((Over.map i).map k)
    let r := (Over.pullback (pullback.fst i f)).map k
    have hlf : l.left ≫ pullback.fst (B.hom ≫ i) f =
        pullback.fst (A.hom ≫ i) f ≫ k.left := pullback.lift_fst _ _ _
    have hrf : r.left ≫ pullback.fst B.hom (pullback.fst i f) =
        pullback.fst A.hom (pullback.fst i f) ≫ k.left := pullback.lift_fst _ _ _
    have haf : a.hom.left ≫ pullback.fst A.hom (pullback.fst i f) =
        pullback.fst (A.hom ≫ i) f := localPullbackPushforwardIso_hom_fst f i A
    have hbf : b.hom.left ≫ pullback.fst B.hom (pullback.fst i f) =
        pullback.fst (B.hom ≫ i) f := localPullbackPushforwardIso_hom_fst f i B
    have hf : (l.left ≫ b.hom.left) ≫ pullback.fst B.hom (pullback.fst i f) =
        (a.hom.left ≫ r.left) ≫ pullback.fst B.hom (pullback.fst i f) := by
      calc
        _ = l.left ≫ pullback.fst (B.hom ≫ i) f := by rw [Category.assoc, hbf]
        _ = pullback.fst (A.hom ≫ i) f ≫ k.left := hlf
        _ = _ := by rw [Category.assoc, hrf, ← Category.assoc, haf]
    have haw : a.hom.left ≫ pullback.snd A.hom (pullback.fst i f) ≫
        pullback.snd i f = pullback.snd (A.hom ≫ i) f := Over.w a.hom
    have hbw : b.hom.left ≫ pullback.snd B.hom (pullback.fst i f) ≫
        pullback.snd i f = pullback.snd (B.hom ≫ i) f := Over.w b.hom
    have hlw : l.left ≫ pullback.snd (B.hom ≫ i) f =
        pullback.snd (A.hom ≫ i) f := Over.w l
    have hrw : r.left ≫ pullback.snd B.hom (pullback.fst i f) =
        pullback.snd A.hom (pullback.fst i f) := Over.w r
    apply Over.OverMorphism.ext
    change l.left ≫ b.hom.left = a.hom.left ≫ r.left
    apply pullback.hom_ext hf
    apply pullback.hom_ext
    · calc
        _ = ((l.left ≫ b.hom.left) ≫
            pullback.fst B.hom (pullback.fst i f)) ≫ B.hom := by
          simpa only [Category.assoc] using
            (congrArg (fun k : pullback B.hom (pullback.fst i f) ⟶ U ↦
              (l.left ≫ b.hom.left) ≫ k)
              (pullback.condition (f := B.hom) (g := pullback.fst i f))).symm
        _ = ((a.hom.left ≫ r.left) ≫
            pullback.fst B.hom (pullback.fst i f)) ≫ B.hom := by rw [hf]
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun k : pullback B.hom (pullback.fst i f) ⟶ U ↦
              (a.hom.left ≫ r.left) ≫ k)
              (pullback.condition (f := B.hom) (g := pullback.fst i f))
    · calc
        _ = l.left ≫ pullback.snd (B.hom ≫ i) f := by
          simpa only [Category.assoc] using congrArg (fun k ↦ l.left ≫ k) hbw
        _ = pullback.snd (A.hom ≫ i) f := hlw
        _ = a.hom.left ≫ pullback.snd A.hom (pullback.fst i f) ≫ pullback.snd i f := haw.symm
        _ = _ := by
          simpa only [Category.assoc] using
            (congrArg (fun k ↦ a.hom.left ≫ k ≫ pullback.snd i f) hrw).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_map_isIso_of_global_map_isIso {X T U : Scheme.{u}}
    (f : T ⟶ X) (i : U ⟶ X)
    [(baseChange (pullback.fst i f)).ReflectsIsomorphisms]
    {A B : FiniteEtale U} (k : A ⟶ B)
    (hk : IsIso ((Over.pullback f).map ((Over.map i).map k.hom))) : IsIso k := by
  let G := Over.map i ⋙ Over.pullback f
  let H := Over.pullback (pullback.fst i f) ⋙ Over.map (pullback.snd i f)
  let e := localPullbackPushforwardNatIso f i
  let : IsIso (G.map k.hom) := hk
  have hn : G.map k.hom ≫ (e.app B.obj).hom =
      (e.app A.obj).hom ≫ H.map k.hom := e.hom.naturality k.hom
  have he : H.map k.hom = (e.app A.obj).inv ≫ G.map k.hom ≫ (e.app B.obj).hom := by
    calc
      H.map k.hom = (e.app A.obj).inv ≫ (e.app A.obj).hom ≫ H.map k.hom := by simp
      _ = (e.app A.obj).inv ≫ G.map k.hom ≫ (e.app B.obj).hom := by
        rw [← hn]
  let : IsIso (H.map k.hom) := by rw [he]; infer_instance
  let : IsIso ((Over.forget (pullback i f)).map
      ((Over.pullback (pullback.fst i f)).map k.hom)) := by
    change IsIso ((Over.forget T).map (H.map k.hom))
    infer_instance
  let : IsIso ((Over.pullback (pullback.fst i f)).map k.hom) :=
    isIso_of_reflects_iso _ (Over.forget (pullback i f))
  let : IsIso ((FiniteEtale.forget (pullback i f)).map
      ((baseChange (pullback.fst i f)).map k)) := by
    change IsIso ((Over.pullback (pullback.fst i f)).map k.hom)
    infer_instance
  let : IsIso ((baseChange (pullback.fst i f)).map k) :=
    isIso_of_reflects_iso _ (FiniteEtale.forget (pullback i f))
  exact isIso_of_reflects_iso k (baseChange (pullback.fst i f))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_square_isPullback_of_pulled_square
    {X T U V : Scheme.{u}} (f : T ⟶ X) (i : U ⟶ X) (j : V ⟶ X)
    (d : U ⟶ V) (hd : d ≫ j = i)
    [(baseChange (pullback.fst i f)).ReflectsIsomorphisms]
    (A : FiniteEtale U) (B : FiniteEtale V)
    (g : (Over.map i).obj A.obj ⟶ (Over.map j).obj B.obj)
    (hw : g.left ≫ B.obj.hom = A.obj.hom ≫ d)
    (hr : IsPullback ((Over.pullback f).map g)
      ((Over.pullback f).map (Over.homMk A.obj.hom rfl :
        (Over.map i).obj A.obj ⟶ Over.mk i))
      ((Over.pullback f).map (Over.homMk B.obj.hom rfl :
        (Over.map j).obj B.obj ⟶ Over.mk j))
      ((Over.pullback f).map (Over.homMk d hd : Over.mk i ⟶ Over.mk j))) :
    IsPullback g.left A.obj.hom B.obj.hom d := by
  let G := Over.pullback f
  let P := (baseChange d).obj B
  let r : (Over.map i).obj P.obj ⟶ (Over.map j).obj B.obj :=
    Over.homMk (pullback.fst B.obj.hom d) (by
      change pullback.fst B.obj.hom d ≫ B.obj.hom ≫ j =
        pullback.snd B.obj.hom d ≫ i
      rw [pullback.condition_assoc, hd])
  let s : (Over.map i).obj P.obj ⟶ Over.mk i :=
    Over.homMk (pullback.snd B.obj.hom d) rfl
  let a : (Over.map i).obj A.obj ⟶ Over.mk i := Over.homMk A.obj.hom rfl
  let b : (Over.map j).obj B.obj ⟶ Over.mk j := Over.homMk B.obj.hom rfl
  let d' : Over.mk i ⟶ Over.mk j := Over.homMk d hd
  have hpb : IsPullback r s b d' := by
    apply IsPullback.of_map (Over.forget X)
      (show r ≫ b = s ≫ d' from Over.OverMorphism.ext pullback.condition)
    exact IsPullback.of_hasPullback B.obj.hom d
  let k : A ⟶ P := ObjectProperty.homMk
    (Over.homMk (pullback.lift g.left A.obj.hom hw) (pullback.lift_snd _ _ _))
  let k' := (Over.map i).map k.hom
  have hkr : k' ≫ r = g := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have hks : k' ≫ s = a := Over.OverMorphism.ext (pullback.lift_snd _ _ _)
  have hpb' := hpb.map G
  let e := hr.isoPullback ≪≫ hpb'.isoPullback.symm
  have he : G.map k' = e.hom := by
    apply hpb'.hom_ext
    · rw [← G.map_comp, hkr]
      dsimp only [e, Iso.trans_hom, Iso.symm_hom]
      rw [Category.assoc, hpb'.isoPullback_inv_fst, hr.isoPullback_hom_fst]
    · rw [← G.map_comp, hks]
      dsimp only [e, Iso.trans_hom, Iso.symm_hom]
      rw [Category.assoc, hpb'.isoPullback_inv_snd, hr.isoPullback_hom_snd]
  have hk : IsIso (G.map k') := by rw [he]; infer_instance
  have : IsIso k := local_map_isIso_of_global_map_isIso f i k hk
  have : IsIso k.hom.left := inferInstanceAs
    (IsIso (((FiniteEtale.forget U) ⋙ Over.forget U).map k))
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso k.hom.left)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

namespace Gluing

open PurelyInseparable.Global

variable {X T : Scheme.{u}} (f : T ⟶ X) [Surjective f]
  (𝒰 : X.OpenCover) [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected]
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  [∀ i, (baseChange (pullback.fst (𝒰.f i) f)).IsEquivalence]
  (C : FiniteEtale T) (A : ∀ i, FiniteEtale (𝒰.X i))
  (e : ∀ i, (baseChange (pullback.fst (𝒰.f i) f)).obj (A i) ≅
    (baseChange (pullback.snd (𝒰.f i) f)).obj C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def object (i : 𝒰.I₀) : Over X := (Over.map (𝒰.f i)).obj (A i).obj

private instance object_etale (i : 𝒰.I₀) : Etale (object 𝒰 A i).hom := by
  change Etale ((A i).obj.hom ≫ 𝒰.f i)
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def structureMap (i : 𝒰.I₀) : object 𝒰 A i ⟶ (chartDiagram 𝒰).obj i :=
  Over.homMk (A i).obj.hom rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def comparison (i : 𝒰.I₀) :
    (Over.pullback f).obj (object 𝒰 A i) ≅ (geometricLocalDiagram f 𝒰 C).obj i :=
  localObjectIso f (𝒰.f i) (A i).obj C.obj ((FiniteEtale.forget _).mapIso (e i))

omit [Surjective f] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    [∀ i, (baseChange (pullback.fst (𝒰.f i) f)).IsEquivalence] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_structure (i : 𝒰.I₀) :
    (Over.pullback f).map (structureMap 𝒰 A i) =
      (comparison f 𝒰 C A e i).hom ≫ (geometricLocalStructure f 𝒰 C).app i := by
  let α : (Over.pullback (pullback.fst (𝒰.f i) f)).obj (A i).obj ≅
      (Over.pullback (pullback.snd (𝒰.f i) f)).obj C.obj :=
    (FiniteEtale.forget _).mapIso (e i)
  let L := localPullbackPushforwardIso f (𝒰.f i) (A i).obj
  let S := localTargetSymmetryIso C.obj (Over.mk (pullback.snd (𝒰.f i) f))
  have H : α.hom.left ≫ pullback.snd C.obj.hom (pullback.snd (𝒰.f i) f) =
      pullback.snd (A i).obj.hom (pullback.fst (𝒰.f i) f) := Over.w α.hom
  have HS : S.hom.left ≫ pullback.fst (pullback.snd (𝒰.f i) f) C.obj.hom =
      pullback.snd C.obj.hom (pullback.snd (𝒰.f i) f) :=
    localTargetSymmetryIso_hom_fst C.obj (Over.mk (pullback.snd (𝒰.f i) f))
  apply Over.OverMorphism.ext
  change ((Over.pullback f).map (Over.homMk (A i).obj.hom rfl :
      (Over.map (𝒰.f i)).obj (A i).obj ⟶ Over.mk (𝒰.f i))).left =
    L.hom.left ≫ α.hom.left ≫ S.hom.left ≫
      pullback.fst (pullback.snd (𝒰.f i) f) C.obj.hom
  calc
    _ = L.hom.left ≫ pullback.snd (A i).obj.hom (pullback.fst (𝒰.f i) f) :=
      localPullbackPushforwardIso_structure f (𝒰.f i) (A i).obj
    _ = L.hom.left ≫ α.hom.left ≫
        pullback.snd C.obj.hom (pullback.snd (𝒰.f i) f) := by rw [H]
    _ = _ := by rw [HS]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def transition {i j : 𝒰.I₀} (d : i ⟶ j) : object 𝒰 A i ⟶ object 𝒰 A j :=
  (local_overMap_surjective f (𝒰.f i) (𝒰.f j) (𝒰.trans d) (𝒰.trans_map d)
    (A i) (A j) ((comparison f 𝒰 C A e i).hom ≫
      (geometricLocalDiagram f 𝒰 C).map d ≫ (comparison f 𝒰 C A e j).inv)).choose

omit [Surjective f] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem map_transition {i j : 𝒰.I₀} (d : i ⟶ j) :
    (Over.pullback f).map (transition f 𝒰 C A e d) =
      (comparison f 𝒰 C A e i).hom ≫ (geometricLocalDiagram f 𝒰 C).map d ≫
        (comparison f 𝒰 C A e j).inv :=
  (local_overMap_surjective f (𝒰.f i) (𝒰.f j) (𝒰.trans d) (𝒰.trans_map d)
    (A i) (A j) _).choose_spec

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def diagram : 𝒰.I₀ ⥤ Over X where
  obj := object 𝒰 A
  map := transition f 𝒰 C A e
  map_id i := by
    apply overPullback_map_injective_of_unramified f
    rw [map_transition, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    simp
  map_comp d d' := by
    apply overPullback_map_injective_of_unramified f
    rw [Functor.map_comp, map_transition, map_transition, map_transition, Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def diagramIso : diagram f 𝒰 C A e ⋙ Over.pullback f ≅
    geometricLocalDiagram f 𝒰 C :=
  NatIso.ofComponents (comparison f 𝒰 C A e) (by
    intro i j d
    change (Over.pullback f).map (transition f 𝒰 C A e d) ≫
        (comparison f 𝒰 C A e j).hom = _
    rw [map_transition]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def structureNat : diagram f 𝒰 C A e ⟶ chartDiagram 𝒰 where
  app := structureMap 𝒰 A
  naturality i j d := by
    let : Etale ((chartDiagram 𝒰).obj j).hom := by
      change Etale (𝒰.f j)
      infer_instance
    apply overPullback_map_injective_of_unramified f
    change (Over.pullback f).map (transition f 𝒰 C A e d ≫ structureMap 𝒰 A j) =
      (Over.pullback f).map (structureMap 𝒰 A i ≫ (chartDiagram 𝒰).map d)
    simp only [Functor.map_comp, map_transition]
    rw [comparison_structure f 𝒰 C A e i, comparison_structure f 𝒰 C A e j]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (fun k ↦ (comparison f 𝒰 C A e i).hom ≫ k)
      ((geometricLocalStructure f 𝒰 C).naturality d)

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pulled_structure_isPullback {i j : 𝒰.I₀} (d : i ⟶ j) :
    IsPullback ((Over.pullback f).map ((diagram f 𝒰 C A e).map d))
      ((Over.pullback f).map ((structureNat f 𝒰 C A e).app i))
      ((Over.pullback f).map ((structureNat f 𝒰 C A e).app j))
      ((Over.pullback f).map ((chartDiagram 𝒰).map d)) := by
  have h : (geometricLocalStructure f 𝒰 C).Equifibered := by
    intro i j d
    apply IsPullback.of_map (Over.forget T)
      ((geometricLocalStructure f 𝒰 C).naturality d)
    exact overPullback_map_isPullback C.obj.hom
      ((Over.pullback f).map ((chartDiagram 𝒰).map d))
  apply (h d).of_iso (comparison f 𝒰 C A e i).symm
    (comparison f 𝒰 C A e j).symm (Iso.refl _) (Iso.refl _)
  · change (geometricLocalDiagram f 𝒰 C).map d ≫ (comparison f 𝒰 C A e j).inv =
      (comparison f 𝒰 C A e i).inv ≫ (Over.pullback f).map (transition f 𝒰 C A e d)
    rw [map_transition]
    simp only [Iso.inv_hom_id_assoc]
  · change (geometricLocalStructure f 𝒰 C).app i =
      (comparison f 𝒰 C A e i).inv ≫ (Over.pullback f).map (structureMap 𝒰 A i)
    rw [comparison_structure f 𝒰 C A e i]
    simp
  · change (geometricLocalStructure f 𝒰 C).app j =
      (comparison f 𝒰 C A e j).inv ≫ (Over.pullback f).map (structureMap 𝒰 A j)
    rw [comparison_structure f 𝒰 C A e j]
    simp
  · simp

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem structure_equifibered : (structureNat f 𝒰 C A e).Equifibered := by
  intro i j d
  apply IsPullback.of_map (Over.forget X) ((structureNat f 𝒰 C A e).naturality d)
  apply local_square_isPullback_of_pulled_square f (𝒰.f i) (𝒰.f j)
    (𝒰.trans d) (𝒰.trans_map d) (A i) (A j) (transition f 𝒰 C A e d)
  · exact congrArg (fun k ↦ k.left) ((structureNat f 𝒰 C A e).naturality d)
  · exact pulled_structure_isPullback f 𝒰 C A e d

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def datum : Scheme.Cover.RelativeGluingData 𝒰 where
  functor := diagram f 𝒰 C A e ⋙ Over.forget X
  natTrans := Functor.whiskerRight (structureNat f 𝒰 C A e) (Over.forget X)
  equifibered {_i _j} d := ((structure_equifibered f 𝒰 C A e) d).map (Over.forget X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def cover : FiniteEtale X := by
  let D := datum f 𝒰 C A e
  have (i : 𝒰.I₀) : IsFinite (D.natTrans.app i) := inferInstanceAs (IsFinite (A i).obj.hom)
  have (i : 𝒰.I₀) : Etale (D.natTrans.app i) := inferInstanceAs (Etale (A i).obj.hom)
  exact RelativeGluing.gluedCover D

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def cocone : Cocone (diagram f 𝒰 C A e) where
  pt := (cover f 𝒰 C A e).obj
  ι :=
    { app i := Over.homMk (colimit.ι (datum f 𝒰 C A e).functor i)
        ((datum f 𝒰 C A e).ι_toBase i)
      naturality i j d := by
        apply Over.OverMorphism.ext
        change (datum f 𝒰 C A e).functor.map d ≫
            colimit.ι (datum f 𝒰 C A e).functor j =
          colimit.ι (datum f 𝒰 C A e).functor i ≫ 𝟙 _
        rw [Category.comp_id]
        exact colimit.w (datum f 𝒰 C A e).functor d }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def coconeIsColimit : IsColimit (cocone f 𝒰 C A e) := by
  apply isColimitOfReflects (Over.forget X)
  change IsColimit (colimit.cocone (datum f 𝒰 C A e).functor)
  exact colimit.isColimit (datum f 𝒰 C A e).functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def diagramCoverIso : diagram f 𝒰 C A e ≅
    overCoverDiagram (cover f 𝒰 C A e).obj (datum f 𝒰 C A e).cover :=
  NatIso.ofComponents (fun i ↦ Over.isoMk (Iso.refl _) (by
    change (𝟙 ((diagram f 𝒰 C A e).obj i).left) ≫
        (colimit.ι (datum f 𝒰 C A e).functor i ≫ (datum f 𝒰 C A e).toBase) =
      (A i).obj.hom ≫ 𝒰.f i
    rw [Category.id_comp]
    exact (datum f 𝒰 C A e).ι_toBase i)) (by
      intro i j d
      apply Over.OverMorphism.ext
      change ((diagram f 𝒰 C A e).map d).left ≫ 𝟙 _ =
        𝟙 _ ≫ ((diagram f 𝒰 C A e).map d).left
      simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def pulledCoconeIsColimit :
    IsColimit ((Over.pullback f).mapCocone (cocone f 𝒰 C A e)) := by
  let : PreservesColimit
      (overCoverDiagram (cover f 𝒰 C A e).obj (datum f 𝒰 C A e).cover)
      (Over.pullback f) :=
    overPullback_preserves_overCoverDiagram (cover f 𝒰 C A e).obj
      (datum f 𝒰 C A e).cover f
  let : PreservesColimit (diagram f 𝒰 C A e) (Over.pullback f) :=
    preservesColimit_of_iso_diagram (Over.pullback f) (diagramCoverIso f 𝒰 C A e).symm
  exact isColimitOfPreserves (Over.pullback f) (coconeIsColimit f 𝒰 C A e)

omit [Surjective f] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    [∀ i, (baseChange (pullback.fst (𝒰.f i) f)).IsEquivalence] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem geometricComponentIso_hom_ι (i : 𝒰.I₀) :
    (geometricTargetComponentIso f 𝒰 C i).hom ≫
      (overCoverCocone C.obj (targetOpenCover f 𝒰 C)).ι.app i =
        (geometricLocalCocone f 𝒰 C).ι.app i := by
  apply Over.OverMorphism.ext
  change (_ ≫ _) ≫ pullback.fst (C.obj.hom ≫ f) (𝒰.f i) =
    pullback.snd (pullback.snd (𝒰.f i) f) C.obj.hom
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
    pullbackLeftPullbackSndIso_hom_snd]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def geometricDiagramIso : geometricLocalDiagram f 𝒰 C ≅
    overCoverDiagram C.obj (targetOpenCover f 𝒰 C) :=
  NatIso.ofComponents (geometricTargetComponentIso f 𝒰 C) (by
    intro i j d
    let c := overCoverCocone C.obj (targetOpenCover f 𝒰 C)
    have : Mono (c.ι.app j).left :=
      inferInstanceAs (Mono ((targetOpenCover f 𝒰 C).f j))
    let : Mono (c.ι.app j) := Over.mono_of_mono_left _
    apply (cancel_mono (c.ι.app j)).mp
    rw [Category.assoc, geometricComponentIso_hom_ι,
      (geometricLocalCocone f 𝒰 C).w d, Category.assoc, c.w d]
    exact (geometricComponentIso_hom_ι f 𝒰 C i).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def geometricCoconeIsColimit : IsColimit (geometricLocalCocone f 𝒰 C) := by
  let e := geometricDiagramIso f 𝒰 C
  let c := overCoverCocone C.obj (targetOpenCover f 𝒰 C)
  have hc := (IsColimit.precomposeHomEquiv e c).symm
    (overCoverCoconeIsColimit C.obj (targetOpenCover f 𝒰 C))
  apply IsColimit.ofIsoColimit hc
  refine Cocone.ext (Iso.refl _) ?_
  intro i
  change ((geometricTargetComponentIso f 𝒰 C i).hom ≫ c.ι.app i) ≫ 𝟙 _ =
    (geometricLocalCocone f 𝒰 C).ι.app i
  rw [Category.comp_id]
  exact geometricComponentIso_hom_ι f 𝒰 C i

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def baseChangeIso : (baseChange f).obj (cover f 𝒰 C A e) ≅ C :=
  ObjectProperty.isoMk _
    ((pulledCoconeIsColimit f 𝒰 C A e).coconePointsIsoOfNatIso
      (geometricCoconeIsColimit f 𝒰 C) (diagramIso f 𝒰 C A e))

end Gluing

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem baseChange_essSurj_of_local_equivalences
    {X T : Scheme.{u}} (f : T ⟶ X) [Surjective f]
    (𝒰 : X.OpenCover) [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected]
    [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    [∀ i, (baseChange (pullback.fst (𝒰.f i) f)).IsEquivalence] :
    (baseChange f).EssSurj where
  mem_essImage C := by
    let A (i : 𝒰.I₀) :=
      (baseChange (pullback.fst (𝒰.f i) f)).asEquivalence.inverse.obj
        ((baseChange (pullback.snd (𝒰.f i) f)).obj C)
    let e (i : 𝒰.I₀) :
        (baseChange (pullback.fst (𝒰.f i) f)).obj (A i) ≅
          (baseChange (pullback.snd (𝒰.f i) f)).obj C :=
      (baseChange (pullback.fst (𝒰.f i) f)).asEquivalence.counitIso.app _
    exact ⟨Gluing.cover f 𝒰 C A e, ⟨Gluing.baseChangeIso f 𝒰 C A e⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite étale covers of an arbitrary scheme and its actual nilpotent
closed subscheme are equivalent under the literal native base-change functor.
The global cover is constructed by gluing the proved affine object lifts. -/
theorem subscheme_baseChange_isEquivalence {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : IsNilpotent I) :
    (baseChange I.subschemeι).IsEquivalence := by
  let : Surjective I.subschemeι := subscheme_surjective_of_nilpotent I hI
  let (U : X.directedAffineCover.I₀) :
      (baseChange (pullback.fst (X.directedAffineCover.f U) I.subschemeι)).IsEquivalence :=
    subscheme_local_baseChange_isEquivalence I hI U
  let : (baseChange I.subschemeι).Faithful := baseChange_faithful_of_surjective _
  let : (baseChange I.subschemeι).Full := subscheme_baseChange_full I hI
  let : (baseChange I.subschemeι).EssSurj :=
    baseChange_essSurj_of_local_equivalences I.subschemeι X.directedAffineCover
  exact { }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same equivalence for the original closed immersion with nilpotent
kernel, using its native image comparison only inside the proof. -/
theorem closedImmersion_baseChange_isEquivalence {X T : Scheme.{u}}
    (j : T ⟶ X) [IsClosedImmersion j] (hj : IsNilpotent j.ker) :
    (baseChange j).IsEquivalence := by
  let : (baseChange j.imageι).IsEquivalence := subscheme_baseChange_isEquivalence j.ker hj
  let : (baseChange j.toImage).IsEquivalence := baseChange_isEquivalence_of_isIso _
  rw [← j.toImage_imageι]
  exact Functor.isEquivalence_of_iso (baseChangeComp j.imageι j.toImage).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nilpotent_comap_from_affine {X S : Scheme.{u}} [IsAffine S]
    (J : S.IdealSheafData)
    (hJ : IsNilpotent (J.ideal ⟨⊤, isAffineOpen_top S⟩)) (f : X ⟶ S) :
    IsNilpotent (J.comap f) := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  ext U : 2
  change ((J.comap f).ideal U) ^ n = ⊥
  rw [Scheme.IdealSheafData.ideal_comap_eq_map_appLE J f
    ⟨⊤, isAffineOpen_top S⟩ U (by simp), ← Ideal.map_pow,
    show (J.ideal ⟨⊤, isAffineOpen_top S⟩) ^ n = ⊥ from hn, Ideal.map_bot]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite étale equivalence along the literal pullback projection of an
actual surjective ring map with nilpotent kernel, over any original scheme. -/
theorem specMap_pullback_baseChange_isEquivalence
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (hker : IsNilpotent (RingHom.ker φ))
    {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) :
    (baseChange (pullback.fst π (Spec.map (CommRingCat.ofHom φ)))).IsEquivalence := by
  let q := Spec.map (CommRingCat.ofHom φ)
  let : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ hφ
  have htop : IsNilpotent (q.ker.ideal ⟨⊤, isAffineOpen_top _⟩) := by
    rw [Scheme.IdealSheafData.specMap_kernel_top]
    exact Ideal.isNilpotent_comap_of_injective (RingHom.ker φ)
      (Scheme.ΓSpecIso (.of R)).hom.hom
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective hker
  have hk : IsNilpotent (pullback.fst π q).ker := by
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion q π]
    exact nilpotent_comap_from_affine q.ker htop π
  exact closedImmersion_baseChange_isEquivalence (pullback.fst π q) hk

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A nilpotent ideal of the original base gives the actual scheme-level
quotient equivalence, retaining both native pullbacks in the functor. -/
theorem quotient_pullback_baseChange_isEquivalence
    (R : Type u) [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) :
    (baseChange (pullback.fst π
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).IsEquivalence := by
  apply specMap_pullback_baseChange_isEquivalence
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective _ π
  simpa only [Ideal.mk_ker] using hI

end AlgebraicGeometry.Scheme.FiniteEtale.Nilpotent
