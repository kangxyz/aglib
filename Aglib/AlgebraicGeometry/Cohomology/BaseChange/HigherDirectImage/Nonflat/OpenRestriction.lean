/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartAdjoint
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineNaturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.OpenSquareComposition
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction.Composition
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Composition

/-!
# General open composition of the original nonflat comparison

The two actual comparison arrows agree after an open change of the new base.
On each affine chart the proof retains the original local scalar mate and
uses the native pullback/open composition for both its source and coefficient.
The higher-image target comparison is the original open-composition isomorphism.

Only the original direct-image morphism is qcqs and the original coefficient
is quasicoherent. The original change of base is arbitrary. No compatibility
family, flatness or finiteness of either base scheme is assumed.

-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

/-- Original restriction followed by ordinary pullback composition. -/
private def openPullbackCompIso {X V V₀ : Scheme.{u}}
    (g : V ⟶ X) (v : V₀ ⟶ V) [IsOpenImmersion v] :
    pullback g ⋙ restrictFunctor v ≅ pullback (v ≫ g) :=
  Functor.isoWhiskerLeft (pullback g) (restrictFunctorIsoPullback v) ≪≫ pullbackComp v g

private theorem conjugate_openRestriction_hom
    {X Y : Scheme.{u}} (v : X ⟶ Y) [IsOpenImmersion v] :
    conjugateEquiv (pullbackPushforwardAdjunction v) (restrictAdjunction v)
      (restrictFunctorIsoPullback v).hom = 𝟙 (pushforward v) := by
  simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

private theorem conjugate_openRestrictionComp_hom
    {X Y Z : Scheme.{u}} (t : X ⟶ Y) (v : Y ⟶ Z)
    [IsOpenImmersion t] [IsOpenImmersion v] :
    conjugateEquiv ((restrictAdjunction v).comp (restrictAdjunction t))
      (restrictAdjunction (t ≫ v)) (restrictFunctorComp t v).hom =
        (pushforwardComp t v).hom := by
  have h : (restrictFunctorIsoPullback (t ≫ v)).hom ≫ (pullbackComp t v).inv =
      (restrictFunctorComp t v).hom ≫
        whiskerRight (restrictFunctorIsoPullback v).hom (restrictFunctor t) ≫
        whiskerLeft (pullback v) (restrictFunctorIsoPullback t).hom := by
    apply NatTrans.ext
    funext M
    exact restrictFunctorIsoPullback_comp_hom_app t v M
  have hc := congrArg (conjugateEquiv
    ((pullbackPushforwardAdjunction v).comp (pullbackPushforwardAdjunction t))
    (restrictAdjunction (t ≫ v))) h
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (t ≫ v)),
    ← conjugateEquiv_comp _ ((restrictAdjunction v).comp (restrictAdjunction t)),
    ← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction v).comp (restrictAdjunction t))] at hc
  rw [conjugateEquiv_pullbackComp_inv, conjugate_openRestriction_hom,
    conjugateEquiv_whiskerLeft, conjugate_openRestriction_hom,
    conjugateEquiv_whiskerRight, conjugate_openRestriction_hom] at hc
  simpa only [whiskerLeft_id', whiskerRight_id', Category.id_comp, Category.comp_id]
    using hc.symm

private theorem conjugate_openPullbackComp_hom
    {X V V₀ : Scheme.{u}} (g : V ⟶ X) (v : V₀ ⟶ V) [IsOpenImmersion v] :
    conjugateEquiv (pullbackPushforwardAdjunction (v ≫ g))
      ((pullbackPushforwardAdjunction g).comp (restrictAdjunction v))
      (openPullbackCompIso g v).hom = (pushforwardComp v g).inv := by
  simp only [openPullbackCompIso, Iso.trans_hom, isoWhiskerLeft_hom]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction v))]
  rw [conjugateEquiv_pullbackComp_hom, conjugateEquiv_whiskerLeft,
    conjugate_openRestriction_hom]
  simp only [whiskerRight_id', Category.comp_id]

/-- The actual source comparison pastes across an open of the new base. -/
private theorem pullbackOpenSquare_openComp_hom
    {X V V₀ T J : Scheme.{u}}
    (g : V ⟶ X) (v : V₀ ⟶ V) (t : T ⟶ V₀) (j : J ⟶ X) (q : T ⟶ J)
    [IsOpenImmersion v] [IsOpenImmersion t] [IsOpenImmersion j]
    (hw : t ≫ (v ≫ g) = q ≫ j) (hT : (t ≫ v) ≫ g = q ≫ j) :
    (pullbackOpenSquare (t ≫ v) q g j hT).hom =
      whiskerLeft (pullback g) (restrictFunctorComp t v).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight (openPullbackCompIso g v).hom (restrictFunctor t) ≫
        (pullbackOpenSquare t q (v ≫ g) j hw).hom := by
  apply (conjugateEquiv ((restrictAdjunction j).comp (pullbackPushforwardAdjunction q))
    ((pullbackPushforwardAdjunction g).comp (restrictAdjunction (t ≫ v)))).injective
  rw [pullbackOpenSquare_conjugate_hom]
  rw [← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction g).comp
        ((restrictAdjunction v).comp (restrictAdjunction t))),
    ← conjugateEquiv_comp _
      (((pullbackPushforwardAdjunction g).comp (restrictAdjunction v)).comp
        (restrictAdjunction t)),
    ← conjugateEquiv_comp _
      ((pullbackPushforwardAdjunction (v ≫ g)).comp (restrictAdjunction t))]
  rw [pullbackOpenSquare_conjugate_hom, conjugateEquiv_whiskerRight,
    conjugate_openPullbackComp_hom, conjugateEquiv_associator_inv,
    conjugateEquiv_whiskerLeft, conjugate_openRestrictionComp_hom]
  ext M U : 3
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_inv_app, Hom.comp_app, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_inv_app_app, Category.id_comp, Category.comp_id]
  congr 1

/-- Component form of the same original source comparison, with no affine hypothesis. -/
private theorem pullbackOpenSquare_openComp_hom_app
    {X V V₀ T J : Scheme.{u}}
    (g : V ⟶ X) (v : V₀ ⟶ V) (t : T ⟶ V₀) (j : J ⟶ X) (q : T ⟶ J)
    [IsOpenImmersion v] [IsOpenImmersion t] [IsOpenImmersion j]
    (hw : t ≫ (v ≫ g) = q ≫ j) (hT : (t ≫ v) ≫ g = q ≫ j) (E : X.Modules) :
    (pullbackOpenSquare (t ≫ v) q g j hT).hom.app E =
      (restrictFunctorComp t v).hom.app ((pullback g).obj E) ≫
        (restrictFunctor t).map ((openPullbackCompIso g v).hom.app E) ≫
        (pullbackOpenSquare t q (v ≫ g) j hw).hom.app E := by
  have h := congr_app (pullbackOpenSquare_openComp_hom g v t j q hw hT) E
  simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_inv_app, Category.id_comp] using h

/-- The exact coefficient comparison on an affine chart after open base restriction. -/
private def openCoefficientIso {U W W₀ W₁ : Scheme.{u}}
    (a : W ⟶ U) (c : W₀ ⟶ W) (z : W₁ ⟶ W₀)
    [IsOpenImmersion c] [IsOpenImmersion z] (M : U.Modules) :
    ((pullback a).obj M).restrict (z ≫ c) ≅
      ((pullback (c ≫ a)).obj M).restrict z :=
  (restrictFunctorComp z c).app ((pullback a).obj M) ≪≫
    (restrictFunctor z).mapIso ((openPullbackCompIso a c).app M)

/-- The original restricted-unit coefficient arrows agree through the same
native source comparison. This uses their actual adjoints, not object isomorphism alone. -/
private theorem chartCoefficient_openComp
    {U W W₀ W₁ U₁ : Scheme.{u}}
    (a : W ⟶ U) (c : W₀ ⟶ W) (z : W₁ ⟶ W₀) (p : U₁ ⟶ U) (q : W₁ ⟶ U₁)
    [IsOpenImmersion c] [IsOpenImmersion z] [IsOpenImmersion p]
    (hw : q ≫ p = z ≫ (c ≫ a)) (hT : q ≫ p = (z ≫ c) ≫ a) (M : U.Modules) :
    chartCoefficient a p (z ≫ c) q hT ((pullbackPushforwardAdjunction a).unit.app M) ≫
        (pushforward q).map (openCoefficientIso a c z M).hom =
      chartCoefficient (c ≫ a) p z q hw
        ((pullbackPushforwardAdjunction (c ≫ a)).unit.app M) := by
  simp only [Functor.id_obj]
  apply ((pullbackPushforwardAdjunction q).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm]
  have hi₁ := chartCoefficient_pullbackUnit_adjoint a p (z ≫ c) q hT M
  have hi₀ := chartCoefficient_pullbackUnit_adjoint (c ≫ a) p z q hw M
  simp only [Functor.id_obj] at hi₁ hi₀
  rw [hi₁, hi₀]
  let O₁ := (pullbackOpenSquare (z ≫ c) q a p hT.symm).app M
  let O₀ := (pullbackOpenSquare z q (c ≫ a) p hw.symm).app M
  let L := openCoefficientIso a c z M
  have ho : O₁.hom = L.hom ≫ O₀.hom := by
    simpa only [O₁, O₀, L, openCoefficientIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc] using
      pullbackOpenSquare_openComp_hom_app a c z p q hw.symm hT.symm M
  change O₁.inv ≫ L.hom = O₀.inv
  apply (cancel_mono O₀.hom).mp
  rw [Category.assoc, ← ho, Iso.inv_hom_id, Iso.inv_hom_id]

/-- Typed cancellation for the source, original scalar mate and higher-image target diagrams. -/
private theorem openLocalComparison_paste
    {C : Type*} [Category C] {E E₁ E₂ A B C₀ C₁ F₀ F₁ F₂ : C}
    (s : E ⟶ E₁) (t : F₀ ⟶ F₁) (u : E₁ ⟶ E₂) (v : F₁ ⟶ F₂)
    (o₁ : E ⟶ A) (o₀ : E₂ ⟶ A) (r : A ⟶ B) (β₁ : B ⟶ C₀) (β₀ : B ⟶ C₁)
    (R₁ : F₀ ⟶ C₀) (R₁i : C₀ ⟶ F₀) (R₀ : F₂ ⟶ C₁) (R₀i : C₁ ⟶ F₂)
    (L : C₀ ⟶ C₁) (h₁ : R₁i ≫ R₁ = 𝟙 C₀) (h₀ : R₀ ≫ R₀i = 𝟙 F₂)
    (ho : o₁ = s ≫ u ≫ o₀) (hβ : β₁ ≫ L = β₀)
    (hR : t ≫ v ≫ R₀ = R₁ ≫ L) :
    s ≫ u ≫ (o₀ ≫ r ≫ β₀ ≫ R₀i) = (o₁ ≫ r ≫ β₁ ≫ R₁i) ≫ t ≫ v := by
  have hi := congrArg (fun k => R₁i ≫ k ≫ R₀i) hR
  simp only [Category.assoc, h₀, Category.comp_id, reassoc_of% h₁] at hi
  simp only [Category.assoc]
  rw [← reassoc_of% ho, ← reassoc_of% hβ, hi]

set_option maxHeartbeats 800000 in
-- Elaborating the native open-composition paste exhausted the standard budget.
/-- The two original local comparisons agree under open composition on a
supplied actual affine chart presentation. -/
private theorem localMap_openComp
    {W U V X W₀ V₀ U₁ W₁ : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
    (c : W₀ ⟶ W) (d : W₀ ⟶ V₀) (v : V₀ ⟶ V)
    [IsOpenImmersion c] [IsOpenImmersion v] (hV : IsPullback c d b v)
    {R S : CommRingCat.{u}}
    (j : Spec R ⟶ X) (t : Spec S ⟶ V₀) (σ : R ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion t]
    (hw : Spec.map σ ≫ j = t ≫ (v ≫ g))
    (hT : Spec.map σ ≫ j = (t ≫ v) ≫ g)
    (p : U₁ ⟶ U) (f₁ : U₁ ⟶ Spec R) [IsOpenImmersion p]
    (hU : IsPullback p f₁ f j)
    (z : W₁ ⟶ W₀) (e : W₁ ⟶ Spec S) [IsOpenImmersion z]
    (hW : IsPullback z e d t)
    (q : W₁ ⟶ U₁) (hq : q ≫ p = z ≫ (c ≫ a))
    (hqT : q ≫ p = (z ≫ c) ≫ a) (hb : q ≫ f₁ = e ≫ Spec.map σ)
    (n : ℕ) (M : U.Modules) [M.IsQuasicoherent] :
    let N := (pullback a).obj M
    let E := ((pushforward f).rightDerived n).obj M
    let F := ((pushforward b).rightDerived n).obj N
    (restrictFunctorComp t v).hom.app ((pullback g).obj E) ≫
        (restrictFunctor t).map ((openPullbackCompIso g v).hom.app E) ≫
        localMap (c ≫ a) d f (v ≫ g) (hV.paste_horiz h) j t σ hw n M
          p f₁ hU z e hW q hq hb =
      localMap a b f g h j (t ≫ v) σ hT n M
          p f₁ hU (z ≫ c) e (hW.paste_horiz hV) q hqT hb ≫
        (restrictFunctorComp t v).hom.app F ≫
        (restrictFunctor t).map ((higherDirectImageOpenRestrictionIso c d b v hV n).hom.app N) ≫
        (restrictFunctor t).map
          (((pushforward d).rightDerived n).map ((openPullbackCompIso a c).hom.app M)) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact d := MorphismProperty.of_isPullback hV inferInstance
  let : QuasiSeparated d := MorphismProperty.of_isPullback hV inferInstance
  let : QuasiCompact f₁ := MorphismProperty.of_isPullback hU inferInstance
  let : QuasiSeparated f₁ := MorphismProperty.of_isPullback hU inferInstance
  let : QuasiCompact e := MorphismProperty.of_isPullback hW inferInstance
  let : QuasiSeparated e := MorphismProperty.of_isPullback hW inferInstance
  let N := (pullback a).obj M
  let N₀ := (pullback (c ≫ a)).obj M
  let E := ((pushforward f).rightDerived n).obj M
  let F := ((pushforward b).rightDerived n).obj N
  let J := restrictFunctor t
  let P := pullback (Spec.map σ)
  let B := (pushforward f₁).rightDerived n
  let D := (pushforward d).rightDerived n
  let K := (pushforward e).rightDerived n
  let C : N.restrict c ⟶ N₀ := (openPullbackCompIso a c).hom.app M
  let L : N.restrict (z ≫ c) ⟶ N₀.restrict z := (openCoefficientIso a c z M).hom
  let l : N.restrict (z ≫ c) ⟶ (N.restrict c).restrict z :=
    (restrictFunctorComp z c).hom.app N
  let s : ((pullback g).obj E).restrict (t ≫ v) ⟶
      (((pullback g).obj E).restrict v).restrict t :=
    (restrictFunctorComp t v).hom.app ((pullback g).obj E)
  let r : F.restrict (t ≫ v) ⟶ (F.restrict v).restrict t :=
    (restrictFunctorComp t v).hom.app F
  let ri : (F.restrict v).restrict t ⟶ F.restrict (t ≫ v) :=
    (restrictFunctorComp t v).inv.app F
  let A : E.restrict j ⟶ B.obj (M.restrict p) :=
    (higherDirectImageOpenRestrictionIso p f₁ f j hU n).hom.app M
  let Rv : F.restrict v ⟶ D.obj (N.restrict c) :=
    (higherDirectImageOpenRestrictionIso c d b v hV n).hom.app N
  let Rz : (D.obj (N.restrict c)).restrict t ⟶ K.obj ((N.restrict c).restrict z) :=
    (higherDirectImageOpenRestrictionIso z e d t hW n).hom.app (N.restrict c)
  let R₀ : (D.obj N₀).restrict t ⟶ K.obj (N₀.restrict z) :=
    (higherDirectImageOpenRestrictionIso z e d t hW n).hom.app N₀
  let R₀i : K.obj (N₀.restrict z) ⟶ (D.obj N₀).restrict t :=
    (higherDirectImageOpenRestrictionIso z e d t hW n).inv.app N₀
  let R₁ : F.restrict (t ≫ v) ⟶ K.obj (N.restrict (z ≫ c)) :=
    (higherDirectImageOpenRestrictionIso (z ≫ c) e b (t ≫ v)
      (hW.paste_horiz hV) n).hom.app N
  let R₁i : K.obj (N.restrict (z ≫ c)) ⟶ F.restrict (t ≫ v) :=
    (higherDirectImageOpenRestrictionIso (z ≫ c) e b (t ≫ v)
      (hW.paste_horiz hV) n).inv.app N
  let o₀ : ((pullback (v ≫ g)).obj E).restrict t ⟶ P.obj (E.restrict j) :=
    (pullbackOpenSquare t (Spec.map σ) (v ≫ g) j hw.symm).hom.app E
  let o₁ : ((pullback g).obj E).restrict (t ≫ v) ⟶ P.obj (E.restrict j) :=
    (pullbackOpenSquare (t ≫ v) (Spec.map σ) g j hT.symm).hom.app E
  let ψ₁ := chartCoefficient a p (z ≫ c) q hqT
    ((pullbackPushforwardAdjunction a).unit.app M)
  let ψ₀ := chartCoefficient (c ≫ a) p z q hq
    ((pullbackPushforwardAdjunction (c ≫ a)).unit.app M)
  let β₁ := higherDirectImageAffineMap (R := R) (S := S) (X := U₁) (Y := W₁)
    (M := M.restrict p) (N := N.restrict (z ≫ c)) q e f₁ σ hb ψ₁ n
  let β₀ := higherDirectImageAffineMap (R := R) (S := S) (X := U₁) (Y := W₁)
    (M := M.restrict p) (N := N₀.restrict z) q e f₁ σ hb ψ₀ n
  have hψ : (𝟙 (M.restrict p)) ≫ ψ₀ = ψ₁ ≫ (pushforward q).map L := by
    rw [Category.id_comp]
    exact (chartCoefficient_openComp a c z p q hq hqT M).symm
  have hβ : β₁ ≫ K.map L = β₀ := by
    have hn := higherDirectImageAffineMap_naturality (R := R) (S := S)
      (X := U₁) (Y := W₁) q e f₁ σ hb
      (M := M.restrict p) (M' := M.restrict p)
      (N := N.restrict (z ≫ c)) (N' := N₀.restrict z) ψ₁ ψ₀ (𝟙 _) L hψ n
    erw [B.map_id, P.map_id, Category.id_comp] at hn
    exact hn.symm
  have hpaste : ri ≫ R₁ ≫ K.map l = J.map Rv ≫ Rz :=
    higherDirectImageOpenRestrictionIso_comp c d b v z e t
      hV hW (hW.paste_horiz hV) N n
  have hpaste' : r ≫ J.map Rv ≫ Rz = R₁ ≫ K.map l := by
    have hri : r ≫ ri = 𝟙 (F.restrict (t ≫ v)) :=
      (restrictFunctorComp t v).hom_inv_id_app F
    rw [← hpaste, reassoc_of% hri]
  have hn := (higherDirectImageOpenRestrictionIso z e d t hW n).hom.naturality C
  change J.map (D.map C) ≫ R₀ = Rz ≫ K.map ((restrictFunctor z).map C) at hn
  have htarget : r ≫ (J.map Rv ≫ J.map (D.map C)) ≫ R₀ = R₁ ≫ K.map L := by
    change r ≫ (J.map Rv ≫ J.map (D.map C)) ≫ R₀ =
      R₁ ≫ K.map (l ≫ (restrictFunctor z).map C)
    rw [K.map_comp]
    simp only [Category.assoc]
    rw [hn, reassoc_of% hpaste']
  have hsource : o₁ = s ≫ J.map ((openPullbackCompIso g v).hom.app E) ≫ o₀ :=
    pullbackOpenSquare_openComp_hom_app g v t j (Spec.map σ) hw.symm hT.symm E
  exact openLocalComparison_paste (C := (Spec S).Modules)
    (E := ((pullback g).obj E).restrict (t ≫ v))
    (E₁ := (((pullback g).obj E).restrict v).restrict t)
    (E₂ := ((pullback (v ≫ g)).obj E).restrict t)
    (A := P.obj (E.restrict j)) (B := P.obj (B.obj (M.restrict p)))
    (C₀ := K.obj (N.restrict (z ≫ c))) (C₁ := K.obj (N₀.restrict z))
    (F₀ := F.restrict (t ≫ v)) (F₁ := (F.restrict v).restrict t)
    (F₂ := (D.obj N₀).restrict t) s r
    (J.map ((openPullbackCompIso g v).hom.app E)) (J.map Rv ≫ J.map (D.map C))
    o₁ o₀ (P.map A) β₁ β₀ R₁ R₁i R₀ R₀i (K.map L)
    ((higherDirectImageOpenRestrictionIso (z ≫ c) e b (t ≫ v)
      (hW.paste_horiz hV) n).inv_hom_id_app N)
    ((higherDirectImageOpenRestrictionIso z e d t hW n).hom_inv_id_app N₀)
    hsource hβ htarget

/-- Restriction form of general open composition, proved on the actual affine charts. -/
private theorem higherDirectImageBaseChangeMap_open_restrict_form
    {W U V X W₀ V₀ : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
    (c : W₀ ⟶ W) (d : W₀ ⟶ V₀) (v : V₀ ⟶ V)
    [IsOpenImmersion c] [IsOpenImmersion v] (hV : IsPullback c d b v)
    (n : ℕ) (M : U.Modules) [M.IsQuasicoherent] :
    (openPullbackCompIso g v).hom.app (((pushforward f).rightDerived n).obj M) ≫
        higherDirectImageBaseChangeMap (c ≫ a) d f (v ≫ g) (hV.paste_horiz h) n M =
      (restrictFunctor v).map (higherDirectImageBaseChangeMap a b f g h n M) ≫
        (higherDirectImageOpenRestrictionIso c d b v hV n).hom.app ((pullback a).obj M) ≫
        ((pushforward d).rightDerived n).map ((openPullbackCompIso a c).hom.app M) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact d := MorphismProperty.of_isPullback hV inferInstance
  let : QuasiSeparated d := MorphismProperty.of_isPullback hV inferInstance
  let H := hV.paste_horiz h
  let E := ((pushforward f).rightDerived n).obj M
  let N := (pullback a).obj M
  let F := ((pushforward b).rightDerived n).obj N
  let β := higherDirectImageBaseChangeMap a b f g h n M
  let β₀ := higherDirectImageBaseChangeMap (c ≫ a) d f (v ≫ g) H n M
  apply hom_ext_of_restrict_jointlySurjective
    (fun C : AffineBaseChangeChart (v ≫ g) => Spec C.targetRing) (fun C => C.target)
    (affineBaseChangeCharts_cover (v ≫ g))
  intro C
  let j := C.source
  let t := C.target
  let σ := C.scalar
  let p := Limits.pullback.fst f j
  let f₁ := Limits.pullback.snd f j
  let z := Limits.pullback.fst d t
  let e := Limits.pullback.snd d t
  let hU := IsPullback.of_hasPullback f j
  let hW := IsPullback.of_hasPullback d t
  have hT : Spec.map σ ≫ j = (t ≫ v) ≫ g := C.comm.trans (Category.assoc t v g).symm
  let q := hU.lift (z ≫ (c ≫ a)) (e ≫ Spec.map σ) (by
    calc
      (z ≫ (c ≫ a)) ≫ f = e ≫ (t ≫ (v ≫ g)) := (hW.paste_horiz H).w
      _ = (e ≫ Spec.map σ) ≫ j := by
        rw [Category.assoc]
        exact congrArg (fun k => e ≫ k) C.comm.symm)
  have hq : q ≫ p = z ≫ (c ≫ a) := hU.lift_fst _ _ _
  have hqT : q ≫ p = (z ≫ c) ≫ a := hq.trans (Category.assoc z c a).symm
  have hb : q ≫ f₁ = e ≫ Spec.map σ := hU.lift_snd _ _ _
  have hβ := higherDirectImageBaseChangeMap_restrict_affine a b f g h j (t ≫ v) σ hT
    n M p f₁ hU (z ≫ c) e (hW.paste_horiz hV) q hqT hb
  have hβ₀ := higherDirectImageBaseChangeMap_restrict_affine (c ≫ a) d f (v ≫ g) H
    j t σ C.comm n M p f₁ hU z e hW q hq hb
  have hn := ((restrictFunctorComp t v).hom.naturality β).symm
  change (restrictFunctorComp t v).hom.app ((pullback g).obj E) ≫
      (restrictFunctor t).map ((restrictFunctor v).map β) =
    (restrictFunctor (t ≫ v)).map β ≫ (restrictFunctorComp t v).hom.app F at hn
  apply (cancel_epi ((restrictFunctorComp t v).hom.app ((pullback g).obj E))).mp
  simp only [Functor.map_comp]
  rw [reassoc_of% hn, hβ, hβ₀]
  exact localMap_openComp a b f g h c d v hV j t σ C.comm hT
    p f₁ hU z e hW q hq hqT hb n M

end AlgebraicGeometry.Scheme.Modules.Nonflat

namespace AlgebraicGeometry.Scheme.Modules

/-- The original canonical comparison composes with every open change of the new base.
The intervening isomorphism is exactly the native higher-image open comparison,
through the original restriction/pullback identifications. No flatness of `g` is assumed. -/
theorem higherDirectImageBaseChangeMap_comp_of_isOpenImmersion
    {W U V X W₀ V₀ : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
    (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
    (c : W₀ ⟶ W) (d : W₀ ⟶ V₀) (v : V₀ ⟶ V)
    [IsOpenImmersion c] [IsOpenImmersion v] (hV : IsPullback c d b v)
    (n : ℕ) (M : U.Modules) [M.IsQuasicoherent] :
    let N := (pullback a).obj M
    let O := (restrictFunctorIsoPullback v).symm.app
        (((pushforward b).rightDerived n).obj N) ≪≫
      (higherDirectImageOpenRestrictionIso c d b v hV n).app N ≪≫
      ((pushforward d).rightDerived n).mapIso ((restrictFunctorIsoPullback c).app N)
    (pullbackComp v g).hom.app (((pushforward f).rightDerived n).obj M) ≫
        higherDirectImageBaseChangeMap (c ≫ a) d f (v ≫ g) (hV.paste_horiz h) n M =
      (pullback v).map (higherDirectImageBaseChangeMap a b f g h n M) ≫ O.hom ≫
        ((pushforward d).rightDerived n).map ((pullbackComp c a).hom.app M) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact d := MorphismProperty.of_isPullback hV inferInstance
  let : QuasiSeparated d := MorphismProperty.of_isPullback hV inferInstance
  let E := ((pushforward f).rightDerived n).obj M
  let N := (pullback a).obj M
  let F := ((pushforward b).rightDerived n).obj N
  let β := higherDirectImageBaseChangeMap a b f g h n M
  have hr := Nonflat.higherDirectImageBaseChangeMap_open_restrict_form
    a b f g h c d v hV n M
  have hn := (restrictFunctorIsoPullback v).hom.naturality β
  change (restrictFunctor v).map β ≫ (restrictFunctorIsoPullback v).hom.app F =
    (restrictFunctorIsoPullback v).hom.app ((pullback g).obj E) ≫ (pullback v).map β at hn
  apply (cancel_epi ((restrictFunctorIsoPullback v).hom.app ((pullback g).obj E))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [← reassoc_of% hn, Iso.hom_inv_id_app_assoc]
  simpa only [Nonflat.openPullbackCompIso, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.map_comp, Category.assoc] using hr

end AlgebraicGeometry.Scheme.Modules
