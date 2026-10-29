/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Elements.Topology
public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Sheaf conditions for the native fibre and sigma functors

The sigma functor and its label transports are the existing native
OverPresheafAux.yonedaCollectionPresheaf. A genuine sheaf of labels
supplies the first gluing; gluing in the selected fibre supplies the second.
The per-cover version retains the weaker hypotheses used by overSigma.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite
open CategoryTheory.OverPresheafAux

namespace CategoryTheory.Presheaf.ElementsSite

universe u v

universe uP uF uG

section Mixed

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type uP)
  (F : (Site P)ᵒᵖ ⥤ Type uF)

private abbrev sigmaRestrict {X Y : C} (f : X ⟶ Y)
    (z : Σ a : P.obj (op Y), F.obj (op (mk P Y a))) :
    Σ a : P.obj (op X), F.obj (op (mk P X a)) :=
  ⟨P.map f.op z.1, F.map (lift P (mk P Y z.1) f).op z.2⟩

private lemma mixed_map_id {X : (Site P)ᵒᵖ} (f : X ⟶ X)
    (h : f = 𝟙 X) (s : F.obj X) : F.map f s = s := by simp [h]

private lemma mixed_sigma_ext {X : C} {a b : P.obj (op X)} (h : a = b)
    {s : F.obj (op (mk P X a))} {t : F.obj (op (mk P X b))}
    (hs : s = F.map (homMk P (𝟙 X) (by simp [h]) :
      mk P X a ⟶ mk P X b).op t) :
    (⟨a, s⟩ : Σ p : P.obj (op X), F.obj (op (mk P X p))) = ⟨b, t⟩ := by
  subst b
  have hi : (homMk P (𝟙 X) (by simp) :
      mk P X a ⟶ mk P X a).op = 𝟙 _ := by
    apply Quiver.Hom.unop_inj
    apply hom_ext P
    rfl
  rw [mixed_map_id P F _ hi] at hs
  subst t
  rfl

private lemma mixed_transport_eq {X : C}
    {s t : Σ a : P.obj (op X), F.obj (op (mk P X a))} (h : s = t)
    (Z : Site P) (a : (projection P).obj Z ⟶ X)
    (hs : P.map a.op s.1 = Z.unop.val) (ht : P.map a.op t.1 = Z.unop.val) :
    F.map (homMk P (a := Z) (b := mk P X s.1) a hs).op s.2 =
      F.map (homMk P (a := Z) (b := mk P X t.1) a ht).op t.2 := by
  cases h
  rfl

private lemma mixed_restrict_label {Z W : Site P} (c : W ⟶ Z)
    (s : Σ a : P.obj (op ((projection P).obj Z)),
      F.obj (op (mk P ((projection P).obj Z) a)))
    (hs : P.map (𝟙 _) s.1 = Z.unop.val) :
    P.map (𝟙 _) (sigmaRestrict P F ((projection P).map c) s).1 = W.unop.val := by
  have hs' : s.1 = Z.unop.val := by simpa using hs
  simpa only [sigmaRestrict, Functor.map_id, ConcreteCategory.id_apply, hs'] using map_val P c

private lemma mixed_map_transport_id {Z W : Site P} (c : W ⟶ Z)
    (s : Σ a : P.obj (op ((projection P).obj Z)),
      F.obj (op (mk P ((projection P).obj Z) a)))
    (hs : P.map (𝟙 _) s.1 = Z.unop.val)
    (hs' : P.map (𝟙 _) (sigmaRestrict P F ((projection P).map c) s).1 = W.unop.val) :
    F.map c.op
        (F.map (homMk P (a := Z) (b := mk P ((projection P).obj Z) s.1)
          (𝟙 _) hs).op s.2) =
      F.map (homMk P (a := W)
          (b := mk P ((projection P).obj W) (sigmaRestrict P F ((projection P).map c) s).1)
          (𝟙 _) hs').op (sigmaRestrict P F ((projection P).map c) s).2 := by
  let f : (projection P).obj W ⟶ (projection P).obj Z := (projection P).map c
  let src := mk P ((projection P).obj Z) s.1
  let mid := mk P ((projection P).obj W) (P.map f.op s.1)
  let k₀ : Z ⟶ src := homMk P (a := Z) (b := src) (𝟙 _) hs
  let k₁ : W ⟶ mid := homMk P (a := W) (b := mid) (𝟙 _) hs'
  let l : mid ⟶ src := lift P src f
  have hk : c ≫ k₀ = k₁ ≫ l := by
    apply hom_ext P
    change f ≫ (𝟙 _) = (𝟙 _) ≫ f
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hop : k₀.op ≫ c.op = l.op ≫ k₁.op :=
    congrArg (fun k : W ⟶ src => k.op) hk
  change F.map c.op (F.map k₀.op s.2) = F.map k₁.op (F.map l.op s.2)
  calc
    F.map c.op (F.map k₀.op s.2) =
        F.map (k₀.op ≫ c.op) s.2 :=
      (ConcreteCategory.congr_hom (F.map_comp k₀.op c.op) s.2).symm
    _ = F.map (l.op ≫ k₁.op) s.2 :=
      congrArg (fun k : op src ⟶ op W => F.map k s.2) hop
    _ = F.map k₁.op (F.map l.op s.2) :=
      ConcreteCategory.congr_hom (F.map_comp l.op k₁.op) s.2

/-- Per-cover sigma gluing for an actual total presheaf and actual fibre
presheaf. Label, fibre and total value universes are independent. The
objectwise equivalence is required to preserve the original restriction maps. -/
theorem isSheafFor_of_sigma_equiv (G : Cᵒᵖ ⥤ Type uG)
    (e : ∀ X : C, G.obj (op X) ≃
      Σ a : P.obj (op X), F.obj (op (mk P X a)))
    (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (z : G.obj (op Y)),
      e X (G.map f.op z) =
        ⟨P.map f.op (e Y z).1,
          F.map (lift P (mk P Y (e Y z).1) f).op (e Y z).2⟩)
    {X : C} {R : Sieve X} (hP : Presieve.IsSheafFor P R.arrows)
    (hF : ∀ a : P.obj (op X), Presieve.IsSheafFor F
      (Sieve.functorPullback (projection P) (X := mk P X a) R).arrows) :
    Presieve.IsSheafFor G R.arrows := by
  intro x hx
  have he' : ∀ ⦃Y Z : C⦄ (f : Y ⟶ Z) (z : G.obj (op Z)),
      e Y (G.map f.op z) = sigmaRestrict P F f (e Z z) := he
  let x₀ : Presieve.FamilyOfElements P R.arrows :=
    fun Y f hf => (e Y (x f hf)).1
  have hx₀ : x₀.Compatible := by
    intro Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ fac
    have h : sigmaRestrict P F g₁ (e Y₁ (x f₁ h₁)) =
        sigmaRestrict P F g₂ (e Y₂ (x f₂ h₂)) :=
      (he' g₁ _).symm.trans ((congrArg (e W) (hx g₁ g₂ h₁ h₂ fac)).trans (he' g₂ _))
    exact congrArg Sigma.fst h
  obtain ⟨a, ha, hau⟩ := hP x₀ hx₀
  have hw : ∀ ⦃Z : Site P⦄ (b : Z ⟶ mk P X a) (hb : R ((projection P).map b)),
      P.map (𝟙 _) (e ((projection P).obj Z) (x ((projection P).map b) hb)).1 =
        Z.unop.val := by
    intro Z b hb
    have hlabel : (e ((projection P).obj Z) (x ((projection P).map b) hb)).1 =
        P.map ((projection P).map b).op a := (ha _ hb).symm
    simpa only [Functor.map_id, ConcreteCategory.id_apply] using
      hlabel.trans (map_val P b)
  let x' : Presieve.FamilyOfElements F
      (Sieve.functorPullback (projection P) (X := mk P X a) R).arrows :=
    fun Z b hb => F.map (homMk P (a := Z)
      (b := mk P ((projection P).obj Z) (e ((projection P).obj Z)
        (x ((projection P).map b) hb)).1) (𝟙 _) (hw b hb)).op
      (e ((projection P).obj Z) (x ((projection P).map b) hb)).2
  have hx' : x'.Compatible := by
    intro Z₁ Z₂ W c₁ c₂ b₁ b₂ h₁ h₂ fac
    have hfac : (projection P).map c₁ ≫ (projection P).map b₁ =
        (projection P).map c₂ ≫ (projection P).map b₂ := by
      simpa only [Functor.map_comp] using congrArg ((projection P).map) fac
    have h : sigmaRestrict P F ((projection P).map c₁)
          (e ((projection P).obj Z₁) (x ((projection P).map b₁) h₁)) =
        sigmaRestrict P F ((projection P).map c₂)
          (e ((projection P).obj Z₂) (x ((projection P).map b₂) h₂)) :=
      (he' _ _).symm.trans
        ((congrArg (e ((projection P).obj W))
          (hx ((projection P).map c₁) ((projection P).map c₂) h₁ h₂ hfac)).trans (he' _ _))
    have h₁' := mixed_restrict_label P F c₁ _ (hw b₁ h₁)
    have h₂' := mixed_restrict_label P F c₂ _ (hw b₂ h₂)
    dsimp only [x']
    rw [mixed_map_transport_id P F c₁ _ _ h₁',
      mixed_map_transport_id P F c₂ _ _ h₂']
    exact mixed_transport_eq P F h W (𝟙 _) h₁' h₂'
  obtain ⟨s, hs, hsu⟩ := hF a x' hx'
  refine ⟨(e X).symm ⟨a, s⟩, ?_, ?_⟩
  · intro Y f hf
    apply (e Y).injective
    rw [he']
    simp only [Equiv.apply_symm_apply]
    apply mixed_sigma_ext P F (ha f hf)
    exact hs (lift P (mk P X a) f) hf
  · intro z hz
    have hr : ∀ ⦃Y : C⦄ (f : Y ⟶ X) (hf : R f),
        sigmaRestrict P F f (e X z) = e Y (x f hf) :=
      fun Y f hf => (he' f z).symm.trans (congrArg (e Y) (hz f hf))
    rcases hze : e X z with ⟨a', s'⟩
    rw [hze] at hr
    have ha' : a' = a := hau a' (fun Y f hf => congrArg Sigma.fst (hr f hf))
    subst a'
    have hs' : s' = s := hsu s' (by
      intro Z b hb
      have h := hr ((projection P).map b) hb
      let f : (projection P).obj Z ⟶ X := (projection P).map b
      let src := mk P X a
      let mid := mk P ((projection P).obj Z) (P.map f.op a)
      have h₁ : P.map (𝟙 _) (P.map f.op a) = Z.unop.val := by
        simpa only [Functor.map_id, ConcreteCategory.id_apply] using map_val P b
      let k : Z ⟶ mid := homMk P (a := Z) (b := mid) (𝟙 _) h₁
      let l : mid ⟶ src := lift P src f
      have h' := mixed_transport_eq P F h Z (𝟙 _) h₁ (hw b hb)
      have htyped : F.map k.op (F.map l.op s') = x' b hb := h'
      have hk : k ≫ l = b := by
        apply hom_ext P
        change (𝟙 _) ≫ f = f
        exact Category.id_comp _
      have hop : l.op ≫ k.op = b.op :=
        congrArg (fun t : Z ⟶ src => t.op) hk
      calc
        F.map b.op s' = F.map (l.op ≫ k.op) s' :=
          congrArg (fun t : op src ⟶ op Z => F.map t s') hop.symm
        _ = F.map k.op (F.map l.op s') :=
          ConcreteCategory.congr_hom (F.map_comp l.op k.op) s'
        _ = x' b hb := htyped)
    subst s'
    apply (e X).injective
    simp only [hze, Equiv.apply_symm_apply]

end Mixed

section CoverTransfer

universe uD vD uE vE uH

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]

/-- The per-sieve part of native continuous precomposition, with no topology
hypothesis on the actual target presheaf. This is used for two actual
equivalences of the element-site presentations. -/
theorem isSheafFor_precomp_of_flat (L : D ⥤ E) [RepresentablyFlat L]
    (H : Eᵒᵖ ⥤ Type uH) {a : D} (S : Sieve a)
    (hH : Presieve.IsSheafFor H (S.functorPushforward L).arrows) :
    Presieve.IsSheafFor (L.op ⋙ H) S.arrows := by
  let H' : Sheaf (⊥ : GrothendieckTopology E) (Type uH) :=
    ⟨H, Presheaf.isSheaf_bot H⟩
  let hL : CompatiblePreserving.{uH} (⊥ : GrothendieckTopology E) L :=
    compatiblePreservingOfFlat _ L
  intro x hx
  have hpush : (x.functorPushforward L).Compatible :=
    Presieve.FamilyOfElements.Compatible.functorPushforward hL H' hx
  apply existsUnique_of_exists_of_unique
  · exact ⟨hH.amalgamate (x.functorPushforward L) hpush,
      fun V f hf => (hH.isAmalgamation hpush (L.map f) _).trans
        (hL.apply_map H' hx hf)⟩
  · intro y₁ y₂ hy₁ hy₂
    apply hH.isSeparatedFor.ext
    rintro Y _ ⟨Z, g, h, hg, rfl⟩
    simpa using! congrArg _ ((hy₁ g hg).trans (hy₂ g hg).symm)

end CoverTransfer

section Represented

variable {C : Type u} [Category.{v} C]

/-- The actual represented-elements map to the original over category. -/
def representedElementsToOver (U : C) : Site (yoneda.obj U) ⥤ Over U where
  obj a := Over.mk a.unop.val
  map f := Over.homMk ((projection (yoneda.obj U)).map f)
    (map_val (yoneda.obj U) f)
  map_id a := by ext; rfl
  map_comp f g := by ext; rfl

instance representedElementsToOver_faithful (U : C) :
    (representedElementsToOver U).Faithful where
  map_injective h := hom_ext _ (congrArg CommaMorphism.left h)

instance representedElementsToOver_full (U : C) :
    (representedElementsToOver U).Full where
  map_surjective {a b} f :=
    ⟨homMk (yoneda.obj U) f.left f.w, by ext; rfl⟩

instance representedElementsToOver_essSurj (U : C) :
    (representedElementsToOver U).EssSurj where
  mem_essImage a :=
    ⟨mk (yoneda.obj U) a.left a.hom, ⟨Over.isoMk (Iso.refl _) (by
      change (𝟙 _) ≫ a.hom = a.hom
      exact Category.id_comp _)⟩⟩

instance representedElementsToOver_isEquivalence (U : C) :
    (representedElementsToOver U).IsEquivalence where

/-- The represented-elements map sends the lifted sieve to exactly the old
over-category sieve, preserving its per-cover sheaf condition. -/
theorem representedElements_isSheafFor (U : C) (Q : (Over U)ᵒᵖ ⥤ Type uF)
    {X : C} {R : Sieve X} (g : X ⟶ U)
    (hQ : Presieve.IsSheafFor Q ((Sieve.overEquiv (Over.mk g)).symm R).arrows) :
    Presieve.IsSheafFor ((representedElementsToOver U).op ⋙ Q)
      (Sieve.functorPullback (projection (yoneda.obj U))
        (X := mk (yoneda.obj U) X g) R).arrows := by
  apply isSheafFor_precomp_of_flat (representedElementsToOver U) Q _
  let T : Sieve (Over.mk g) := (Sieve.overEquiv (Over.mk g)).symm R
  have hT : (Sieve.functorPullback (projection (yoneda.obj U))
        (X := mk (yoneda.obj U) X g) R).functorPushforward
        (representedElementsToOver U) = T := by
    change (Sieve.functorPullback (representedElementsToOver U)
        (X := mk (yoneda.obj U) X g) T).functorPushforward
      (representedElementsToOver U) = T
    exact (Sieve.essSurjFullFunctorGaloisInsertion (representedElementsToOver U)
      (mk (yoneda.obj U) X g)).l_u_eq T
  rw [hT]
  exact hQ

end Represented

variable {C : Type u} [Category.{v} C] (A : Cᵒᵖ ⥤ Type v)

/-- The native costructured-arrow presentation used by the existing sigma functor. -/
abbrev CostructuredSite := CostructuredArrow yoneda A

abbrev costructuredProjection : CostructuredSite A ⥤ C :=
  CostructuredArrow.proj yoneda A

/-- Transport the actual element topology through the native Yoneda equivalence. -/
abbrev costructuredTopology (J : GrothendieckTopology C) :
    GrothendieckTopology (CostructuredSite A) :=
  (Functor.Elements.costructuredArrowYonedaEquivalence A).inverse.inducedTopology
    (topology A J)

@[simp]
lemma mem_costructuredTopology_iff (J : GrothendieckTopology C)
    {a : CostructuredSite A} (S : Sieve a) :
    S ∈ costructuredTopology A J a ↔
      S.functorPushforward (costructuredProjection A) ∈ J a.left := by
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, mem_topology_iff,
    ← Sieve.functorPushforward_comp]
  rfl

instance costructuredProjection_isContinuous (J : GrothendieckTopology C) :
    (costructuredProjection A).IsContinuous (costructuredTopology A J) J := by
  change ((Functor.Elements.costructuredArrowYonedaEquivalence A).inverse ⋙
    projection A).IsContinuous (costructuredTopology A J) J
  exact Functor.isContinuous_comp _ _ _ (topology A J) _

@[simp]
lemma costructured_functorPushforward_functorPullback
    {a : CostructuredSite A} (R : Sieve a.left) :
    (Sieve.functorPullback (costructuredProjection A) (X := a) R).functorPushforward
      (costructuredProjection A) = R := by
  ext X f
  constructor
  · rintro ⟨b, g, h, hg, rfl⟩
    exact R.downward_closed hg h
  · intro hf
    exact ⟨CostructuredArrow.mk (yoneda.map f ≫ a.hom),
      CostructuredArrow.mkPrecomp a.hom f, 𝟙 _, hf, by simp⟩

lemma costructured_functorPullback_mem (J : GrothendieckTopology C)
    {a : CostructuredSite A} {R : Sieve a.left} (hR : R ∈ J a.left) :
    Sieve.functorPullback (costructuredProjection A) (X := a) R ∈
      costructuredTopology A J a := by
  rw [mem_costructuredTopology_iff, costructured_functorPushforward_functorPullback]
  exact hR

variable {A}
variable (F : (CostructuredSite A)ᵒᵖ ⥤ Type v)

/-- The native sigma presheaf is a specialization of mixed-value sigma
gluing. Its original constructor and all native label transports are retained. -/
theorem yonedaCollection_isSheafFor {X : C} {R : Sieve X}
    (hA : Presieve.IsSheafFor A R.arrows)
    (hF : ∀ s : yoneda.obj X ⟶ A, Presieve.IsSheafFor F
      (Sieve.functorPullback (costructuredProjection A)
        (X := CostructuredArrow.mk s) R).arrows) :
    Presieve.IsSheafFor (yonedaCollectionPresheaf A F) R.arrows := by
  let e := Functor.Elements.costructuredArrowYonedaEquivalence A
  let F' := e.functor.op ⋙ F
  apply isSheafFor_of_sigma_equiv A F' (yonedaCollectionPresheaf A F)
    (fun X => Equiv.refl _) ?_ hA ?_
  · intro Y Z f z
    change YonedaCollection F Z at z
    let p₀ : A.obj (op Z) := z.1
    let s₀ : yoneda.obj Z ⟶ A := yonedaEquiv.symm p₀
    let t : F.obj (op (CostructuredArrow.mk s₀)) := z.snd
    let p₁ : A.obj (op Y) := A.map f.op p₀
    let s₁ : yoneda.obj Y ⟶ A := yonedaEquiv.symm p₁
    let s₂ : yoneda.obj Y ⟶ A := (YonedaCollection.map₂ F f z).fst
    let b : CostructuredArrow.mk s₁ ⟶ CostructuredArrow.mk s₀ :=
      e.functor.map (lift A (mk A Z p₀) f)
    let q : YonedaCollection F Y := ⟨p₁, F.map b.op t⟩
    let sPre : yoneda.obj Y ⟶ A := yoneda.map f ≫ s₀
    let l : CostructuredArrow.mk sPre ⟶ CostructuredArrow.mk s₀ :=
      CostructuredArrow.mkPrecomp s₀ f
    have h₂ : s₂ = sPre := YonedaCollection.map₂_fst (F := F) f z
    have hf : s₂ = s₁ :=
      h₂.trans (yonedaEquiv_symm_map f.op p₀).symm
    let u : op (CostructuredArrow.mk s₁) ⟶ op (CostructuredArrow.mk s₂) :=
      eqToHom (congrArg (fun s => op (CostructuredArrow.mk s)) hf.symm)
    let v : op (CostructuredArrow.mk sPre) ⟶ op (CostructuredArrow.mk s₂) :=
      eqToHom (congrArg (fun s => op (CostructuredArrow.mk s)) h₂.symm)
    have hp : (YonedaCollection.map₂ F f z).snd = F.map (l.op ≫ v) t :=
      YonedaCollection.map₂_snd (F := F) f z
    let proj := (costructuredProjection A).op
    have hu : proj.map u = 𝟙 (op Y) := by
      change proj.map u = 𝟙 (proj.obj (op (CostructuredArrow.mk s₁)))
      simp only [u, eqToHom_map, eqToHom_refl]
    have hv : proj.map v = 𝟙 (op Y) := by
      change proj.map v = 𝟙 (proj.obj (op (CostructuredArrow.mk sPre)))
      simp only [v, eqToHom_map, eqToHom_refl]
    have hb : proj.map b.op = f.op := rfl
    have hl : proj.map l.op = f.op := rfl
    have harr : b.op ≫ u = l.op ≫ v := by
      apply proj.map_injective
      calc
        proj.map (b.op ≫ u) = proj.map b.op ≫ proj.map u := proj.map_comp _ _
        _ = f.op ≫ 𝟙 (op Y) :=
          congrArg₂ (fun (a : op Z ⟶ op Y) (b : op Y ⟶ op Y) => a ≫ b) hb hu
        _ = proj.map l.op ≫ proj.map v :=
          (congrArg₂ (fun (a : op Z ⟶ op Y) (b : op Y ⟶ op Y) => a ≫ b) hl hv).symm
        _ = proj.map (l.op ≫ v) := (proj.map_comp _ _).symm
    change YonedaCollection.map₂ F f z = q
    refine YonedaCollection.ext hf ?_
    change F.map u (F.map b.op t) = (YonedaCollection.map₂ F f z).snd
    calc
      F.map u (F.map b.op t) = F.map (b.op ≫ u) t :=
        (ConcreteCategory.congr_hom (F.map_comp b.op u) t).symm
      _ = F.map (l.op ≫ v) t :=
        congrArg (fun k : op (CostructuredArrow.mk s₀) ⟶
          op (CostructuredArrow.mk s₂) => F.map k t) harr
      _ = (YonedaCollection.map₂ F f z).snd := hp.symm
  · intro a
    apply isSheafFor_precomp_of_flat e.functor F _
    let T : Sieve (CostructuredArrow.mk (yonedaEquiv.symm a)) :=
      Sieve.functorPullback (costructuredProjection A)
        (X := CostructuredArrow.mk (yonedaEquiv.symm a)) R
    have hT : (Sieve.functorPullback (projection A) (X := mk A X a) R).functorPushforward
        e.functor = T := by
      change (Sieve.functorPullback e.functor (X := mk A X a) T).functorPushforward e.functor = T
      exact (Sieve.essSurjFullFunctorGaloisInsertion e.functor (mk A X a)).l_u_eq T
    rw [hT]
    exact hF (yonedaEquiv.symm a)

/-- Gluing for the original total presheaf uses the genuine sheaf of base labels. -/
theorem yonedaCollection_isSheaf (J : GrothendieckTopology C)
    (hA : Presieve.IsSheaf J A)
    (hF : Presieve.IsSheaf (costructuredTopology A J) F) :
    Presieve.IsSheaf J (yonedaCollectionPresheaf A F) := by
  intro X R hR
  exact yonedaCollection_isSheafFor F (hA R hR)
    (fun s => hF _ (costructured_functorPullback_mem A J hR))

/-- The native fibre functor retains its actual underlying section. -/
theorem restrictedYonedaObj_isSheaf (J : GrothendieckTopology C)
    (hA : Presieve.IsSheaf J A) {Y : Cᵒᵖ ⥤ Type v} (η : Y ⟶ A)
    (hY : Presieve.IsSheaf J Y) :
    Presieve.IsSheaf (costructuredTopology A J) (restrictedYonedaObj η) := by
  have hY' : Presieve.IsSheaf (costructuredTopology A J)
      ((costructuredProjection A).op ⋙ Y) := (costructuredProjection A).op_comp_isSheaf_of_types
    (costructuredTopology A J) J
    (⟨Y, (isSheaf_iff_isSheaf_of_type J Y).2 hY⟩ : Sheaf J (Type v))
  have hA' : Presieve.IsSheaf (costructuredTopology A J)
      ((costructuredProjection A).op ⋙ A) := (costructuredProjection A).op_comp_isSheaf_of_types
    (costructuredTopology A J) J
    (⟨A, (isSheaf_iff_isSheaf_of_type J A).2 hA⟩ : Sheaf J (Type v))
  intro a T hT x hx
  let x₀ : Presieve.FamilyOfElements ((costructuredProjection A).op ⋙ Y) T.arrows :=
    fun Z b hb => (x b hb).val
  have hx₀ : x₀.Compatible := by
    intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ fac
    exact congrArg Subtype.val (hx g₁ g₂ h₁ h₂ fac)
  obtain ⟨y, hy, hyu⟩ := hY' T hT x₀ hx₀
  have hlabel : η.app (op a.left) y = yonedaEquiv a.hom := by
    apply (hA' T hT).isSeparatedFor.ext
    intro Z b hb
    change A.map b.left.op (η.app (op a.left) y) =
      A.map b.left.op (yonedaEquiv a.hom)
    have hyb : Y.map b.left.op y = (x b hb).val := hy b hb
    rw [← η.naturality_apply, hyb]
    exact ((x b hb).prop.app).trans
      ((congrArg yonedaEquiv b.w.symm).trans
        (yonedaEquiv_naturality a.hom b.left).symm)
  refine ⟨⟨y, ⟨hlabel⟩⟩, ?_, ?_⟩
  · intro Z b hb
    apply Subtype.ext
    exact hy b hb
  · intro y' hy'
    apply Subtype.ext
    exact hyu y'.val (fun Z b hb => congrArg Subtype.val (hy' b hb))

/-- The sheaf restriction of the native presheaf equivalence is legitimate
because the base labels are an actual sheaf. -/
theorem isSheaf_iff_restrictedYonedaObj (J : GrothendieckTopology C)
    (hA : Presieve.IsSheaf J A) {Y : Cᵒᵖ ⥤ Type v} (η : Y ⟶ A) :
    Presieve.IsSheaf J Y ↔
      Presieve.IsSheaf (costructuredTopology A J) (restrictedYonedaObj η) := by
  constructor
  · exact restrictedYonedaObj_isSheaf J hA η
  · intro hF
    exact Presieve.isSheaf_iso J (unitAuxAux η)
      (yonedaCollection_isSheaf (restrictedYonedaObj η) J hA hF)

end CategoryTheory.Presheaf.ElementsSite
