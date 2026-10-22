/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Modules.Affine
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Modules.Properties
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing
public import Aglib.CategoryTheory.Sites.Descent.Bind
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-!
# Finitely presented module objects on actual scheme limits

An actual finitely presented module on a limit of qcqs schemes with affine
transitions descends above any prescribed stage. The proof models compact
opens, descends the original isomorphism on a binary overlap, and glues
actual local objects. Native cone maps recover the original module.
The fixed-model specialization uses the literal native base-change cone.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

section BinaryDescent

open Opposite Bicategory CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type*} [Category C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat}
  {S W : C} {X : Bool → C} (f : ∀ b, X b ⟶ S)
  [∀ b, Mono (f b)] (p : W ⟶ X false) (q : W ⟶ X true)
  (H : IsPullback p q (f false) (f true))
  (M : ∀ b, F.obj (.mk (op (X b))))
  (e : (F.map p.op.toLoc).toFunctor.obj (M false) ≅
    (F.map q.op.toLoc).toFunctor.obj (M true))

private def binaryHom {Y : C} (t : Y ⟶ S) (a b : Bool)
    (g₁ : Y ⟶ X a) (g₂ : Y ⟶ X b)
    (h₁ : g₁ ≫ f a = t) (h₂ : g₂ ≫ f b = t) :
    (F.map g₁.op.toLoc).toFunctor.obj (M a) ⟶
      (F.map g₂.op.toLoc).toFunctor.obj (M b) := by
  cases a <;> cases b
  · exact eqToHom (congrArg (fun g : Y ⟶ X false ↦
      (F.map g.op.toLoc).toFunctor.obj (M false)) ((cancel_mono (f false)).mp (h₁.trans h₂.symm)))
  · exact pullHom e.hom (H.lift g₁ g₂ (h₁.trans h₂.symm)) g₁ g₂
      (H.lift_fst _ _ _) (H.lift_snd _ _ _)
  · exact pullHom e.inv (H.lift g₂ g₁ (h₂.trans h₁.symm)) g₁ g₂
      (H.lift_snd _ _ _) (H.lift_fst _ _ _)
  · exact eqToHom (congrArg (fun g : Y ⟶ X true ↦
      (F.map g.op.toLoc).toFunctor.obj (M true)) ((cancel_mono (f true)).mp (h₁.trans h₂.symm)))

private theorem binaryHom_self {Y : C} (t : Y ⟶ S) (a : Bool)
    (g : Y ⟶ X a) (h : g ≫ f a = t) : binaryHom f p q H M e t a a g g h h = 𝟙 _ := by
  cases a <;> simp only [binaryHom, eqToHom_refl]

private theorem binaryHom_pullHom {Y Y' : C} (s : Y' ⟶ Y) (t : Y ⟶ S)
    (t' : Y' ⟶ S) (ht : s ≫ t = t') (a b : Bool)
    (g₁ : Y ⟶ X a) (g₂ : Y ⟶ X b) (h₁ : g₁ ≫ f a = t) (h₂ : g₂ ≫ f b = t)
    (sg₁ : Y' ⟶ X a) (sg₂ : Y' ⟶ X b)
    (hs₁ : s ≫ g₁ = sg₁) (hs₂ : s ≫ g₂ = sg₂) :
    pullHom (binaryHom f p q H M e t a b g₁ g₂ h₁ h₂) s sg₁ sg₂ hs₁ hs₂ =
      binaryHom f p q H M e t' a b sg₁ sg₂
        (by rw [← hs₁, Category.assoc, h₁, ht])
        (by rw [← hs₂, Category.assoc, h₂, ht]) := by
  cases a <;> cases b
  · obtain rfl : g₁ = g₂ := (cancel_mono (f false)).mp (h₁.trans h₂.symm)
    subst sg₁
    subst sg₂
    simp only [binaryHom_self, pullHom_id']
  · dsimp only [binaryHom]
    rw [pullHom_pullHom]
    apply pullHom_congr_left
    apply H.hom_ext <;> simp [hs₁, hs₂]
  · dsimp only [binaryHom]
    rw [pullHom_pullHom]
    apply pullHom_congr_left
    apply H.hom_ext <;> simp [hs₁, hs₂]
  · obtain rfl : g₁ = g₂ := (cancel_mono (f true)).mp (h₁.trans h₂.symm)
    subst sg₁
    subst sg₂
    simp only [binaryHom_self, pullHom_id']

private theorem binaryHom_comp {Y : C} (t : Y ⟶ S) (a b d : Bool)
    (g₁ : Y ⟶ X a) (g₂ : Y ⟶ X b) (g₃ : Y ⟶ X d)
    (h₁ : g₁ ≫ f a = t) (h₂ : g₂ ≫ f b = t) (h₃ : g₃ ≫ f d = t) :
    binaryHom f p q H M e t a b g₁ g₂ h₁ h₂ ≫
      binaryHom f p q H M e t b d g₂ g₃ h₂ h₃ =
    binaryHom f p q H M e t a d g₁ g₃ h₁ h₃ := by
  cases a <;> cases b <;> cases d
  · obtain rfl : g₁ = g₂ := (cancel_mono (f false)).mp (h₁.trans h₂.symm)
    have heq : g₁ = g₃ := (cancel_mono (f false)).mp (h₁.trans h₃.symm)
    subst g₃
    simp only [binaryHom_self, Category.id_comp]
  · obtain rfl : g₁ = g₂ := (cancel_mono (f false)).mp (h₁.trans h₂.symm)
    simp only [binaryHom_self, Category.id_comp]
  · obtain rfl : g₁ = g₃ := (cancel_mono (f false)).mp (h₁.trans h₃.symm)
    dsimp only [binaryHom]
    rw [← pullHom_comp, e.hom_inv_id, pullHom_id']
    simp only [eqToHom_refl]
  · obtain rfl : g₂ = g₃ := (cancel_mono (f true)).mp (h₂.trans h₃.symm)
    simp only [binaryHom_self, Category.comp_id]
  · obtain rfl : g₂ = g₃ := (cancel_mono (f false)).mp (h₂.trans h₃.symm)
    simp only [binaryHom_self, Category.comp_id]
  · obtain rfl : g₁ = g₃ := (cancel_mono (f true)).mp (h₁.trans h₃.symm)
    dsimp only [binaryHom]
    rw [← pullHom_comp, e.inv_hom_id, pullHom_id']
    simp only [eqToHom_refl]
  · obtain rfl : g₁ = g₂ := (cancel_mono (f true)).mp (h₁.trans h₂.symm)
    simp only [binaryHom_self, Category.id_comp]
  · obtain rfl : g₁ = g₂ := (cancel_mono (f true)).mp (h₁.trans h₂.symm)
    have heq : g₁ = g₃ := (cancel_mono (f true)).mp (h₁.trans h₃.symm)
    subst g₃
    simp only [binaryHom_self, Category.id_comp]

private def binaryDescentData : F.DescentData f where
  obj := M
  hom _ t a b g₁ g₂ h₁ h₂ := binaryHom f p q H M e t a b g₁ g₂ h₁ h₂
  pullHom_hom _ _ s t t' ht a b g₁ g₂ h₁ h₂ sg₁ sg₂ hs₁ hs₂ :=
    binaryHom_pullHom f p q H M e s t t' ht a b g₁ g₂ h₁ h₂ sg₁ sg₂ hs₁ hs₂
  hom_self _ t a g h := binaryHom_self f p q H M e t a g h
  hom_comp _ t a b d g₁ g₂ g₃ h₁ h₂ h₃ :=
    binaryHom_comp f p q H M e t a b d g₁ g₂ g₃ h₁ h₂ h₃

private theorem binaryDescentData_obj (b : Bool) :
    (binaryDescentData f p q H M e).obj b = M b := rfl

private theorem binaryDescentData_hom_overlap :
    (binaryDescentData f p q H M e).hom (p ≫ f false) p q rfl H.w.symm = e.hom := by
  change pullHom e.hom (H.lift p q H.w) p q
    (H.lift_fst p q H.w) (H.lift_snd p q H.w) = e.hom
  have h : H.lift p q H.w = 𝟙 W := by
    apply H.hom_ext <;> simp
  exact (pullHom_congr_left e.hom h (H.lift_fst p q H.w) (H.lift_snd p q H.w)
    (by simp) (by simp)).trans (pullHom_id e.hom)

private def binaryPair : ∀ a b, ChosenPullback (f a) (f b)
  | false, false =>
      { pullback := X false
        p₁ := 𝟙 _
        p₂ := 𝟙 _
        condition := by simp
        isLimit := (IsKernelPair.id_of_mono (f false)).isLimit
        p := f false
        hp₁ := by simp }
  | false, true =>
      { pullback := W
        p₁ := p
        p₂ := q
        condition := H.w
        isLimit := H.isLimit }
  | true, false =>
      { pullback := W
        p₁ := q
        p₂ := p
        condition := H.w.symm
        isLimit := H.flip.isLimit
        p := p ≫ f false
        hp₁ := H.w.symm }
  | true, true =>
      { pullback := X true
        p₁ := 𝟙 _
        p₂ := 𝟙 _
        condition := by simp
        isLimit := (IsKernelPair.id_of_mono (f true)).isLimit
        p := f true
        hp₁ := by simp }

private def binaryDescentIso (D E : F.DescentData f) (ε : ∀ b, D.obj b ≅ E.obj b)
    (h : (F.map p.op.toLoc).toFunctor.map (ε false).hom ≫
        E.hom (p ≫ f false) p q rfl H.w.symm =
      D.hom (p ≫ f false) p q rfl H.w.symm ≫
        (F.map q.op.toLoc).toFunctor.map (ε true).hom) : D ≅ E := by
  let B := binaryPair f p q H
  have hpair (a b : Bool) :
      (F.map (B a b).p₁.op.toLoc).toFunctor.map (ε a).hom ≫
          E.hom (B a b).p (B a b).p₁ (B a b).p₂ (B a b).hp₁ (B a b).hp₂ =
        D.hom (B a b).p (B a b).p₁ (B a b).p₂ (B a b).hp₁ (B a b).hp₂ ≫
          (F.map (B a b).p₂.op.toLoc).toFunctor.map (ε b).hom := by
    cases a <;> cases b
    · simp only [B, binaryPair, D.hom_self, E.hom_self, Category.id_comp, Category.comp_id]
    · exact h
    · change (F.map q.op.toLoc).toFunctor.map (ε true).hom ≫
          E.hom (p ≫ f false) q p H.w.symm rfl =
        D.hom (p ≫ f false) q p H.w.symm rfl ≫
          (F.map p.op.toLoc).toFunctor.map (ε false).hom
      apply (cancel_epi (D.hom (p ≫ f false) p q rfl H.w.symm)).mp
      calc
        _ = ((F.map p.op.toLoc).toFunctor.map (ε false).hom ≫
            E.hom (p ≫ f false) p q rfl H.w.symm) ≫
            E.hom (p ≫ f false) q p H.w.symm rfl := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ z ≫ E.hom (p ≫ f false) q p H.w.symm rfl) h.symm
        _ = (F.map p.op.toLoc).toFunctor.map (ε false).hom := by
          rw [Category.assoc, E.hom_comp]
          simp only [E.hom_self, Category.comp_id]
        _ = _ := by
          rw [← Category.assoc, D.hom_comp]
          simp only [D.hom_self, Category.id_comp]
    · simp only [B, binaryPair, D.hom_self, E.hom_self, Category.id_comp, Category.comp_id]
  refine DescentData.isoMk ε ?_
  exact DescentData.comm_of_overlap (F := F) (D₁ := D) (D₂ := E) (fun b ↦ (ε b).hom)
    (fun a b ↦ (B a b).pullback) (fun a b ↦ (B a b).p₁) (fun a b ↦ (B a b).p₂)
    (fun a b ↦ (B a b).p) (fun a b ↦ (B a b).hp₁) (fun a b ↦ (B a b).hp₂)
    (fun _ _ _ _ g₁ g₂ h₁ h₂ ↦ (B _ _).isPullback.exists_lift g₁ g₂ (h₁.trans h₂.symm)) hpair


end BinaryDescent

private theorem exists_glued_of_openCover
    {S : Scheme.{u}} {A : Type v} {X : A → Scheme.{u}}
    (f : ∀ a, X a ⟶ S) [∀ a, IsOpenImmersion (f a)]
    (hcover : IsOpenCover (fun a ↦ (f a).opensRange))
    (D : pullbackPseudofunctor.{u}.DescentData f) :
    ∃ G : S.Modules,
      Nonempty ((pullbackPseudofunctor.toDescentData f).obj G ≅ D) := by
  let 𝒰 : S.OpenCover :=
    { I₀ := A
      X := X
      f := f
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ hcover.exists_mem x, inferInstance⟩ }
  let T := pullbackPseudofunctor.toDescentData f
  have h𝒰 : Sieve.ofArrows X f ∈ Scheme.zariskiTopology S := 𝒰.mem_grothendieckTopology
  have : T.IsEquivalence :=
    CategoryTheory.Pseudofunctor.isEquivalence_toDescentData
      (F := pullbackPseudofunctor.{u}) f h𝒰
  exact Functor.EssSurj.mem_essImage T D

private theorem finitePresentation_of_binary_pullback_isos
    {S : Scheme.{u}} (X : Bool → Scheme.{u})
    (f : ∀ b, X b ⟶ S) [∀ b, IsOpenImmersion (f b)]
    (hcover : IsOpenCover (fun b ↦ (f b).opensRange))
    (G : S.Modules) (M : ∀ b, (X b).Modules)
    [∀ b, (M b).IsFinitePresentation]
    (e : ∀ b, (pullback (f b)).obj G ≅ M b) : G.IsFinitePresentation := by
  have hcover' : IsOpenCover (fun b : ULift.{u} Bool ↦ (f b.down).opensRange) := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨b, hb⟩ := hcover.exists_mem x
    exact Opens.mem_iSup.mpr ⟨ULift.up b, hb⟩
  apply finitePresentation_of_openCover G
    (fun b : ULift.{u} Bool ↦ (f b.down).opensRange) hcover'
  intro b
  have hpb : ((pullback (f b.down)).obj G).IsFinitePresentation :=
    (finitePresentation_iff_of_iso (e b.down)).mpr inferInstance
  let := hpb
  exact (finitePresentation_iff_of_iso (restrictOpensRangeIso (f b.down) G)).mpr inferInstance

private def descentIsoApp
    {S : Scheme.{u}} {A : Type v} {X : A → Scheme.{u}} {f : ∀ a, X a ⟶ S}
    {D E : pullbackPseudofunctor.{u}.DescentData f} (e : D ≅ E) (a : A) :
    D.obj a ≅ E.obj a where
  hom := e.hom.hom a
  inv := e.inv.hom a
  hom_inv_id := by
    simpa only [CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      CategoryTheory.Pseudofunctor.DescentData.id_hom] using
      congrArg (fun φ : D ⟶ D ↦ φ.hom a) e.hom_inv_id
  inv_hom_id := by
    simpa only [CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      CategoryTheory.Pseudofunctor.DescentData.id_hom] using
      congrArg (fun φ : E ⟶ E ↦ φ.hom a) e.inv_hom_id

/-- Two actual finitely presented modules on a binary open cover glue along
an actual overlap isomorphism. The recovering local isomorphisms retain
that original transition through the native module descent comparison. -/
theorem exists_binary_finitePresentation_glued
    {S W : Scheme.{u}} (X : Bool → Scheme.{u})
    (f : ∀ b, X b ⟶ S) [∀ b, IsOpenImmersion (f b)]
    (hcover : IsOpenCover (fun b ↦ (f b).opensRange))
    (p : W ⟶ X false) (q : W ⟶ X true)
    (H : IsPullback p q (f false) (f true))
    (M : ∀ b, (X b).Modules) [∀ b, (M b).IsFinitePresentation]
    (α : (pullback p).obj (M false) ≅ (pullback q).obj (M true)) :
    ∃ G : S.Modules, G.IsFinitePresentation ∧
      ∃ e : ∀ b, (pullback (f b)).obj G ≅ M b,
        (pullback p).map (e false).hom ≫ α.hom =
          ((pullbackPseudofunctor.toDescentData f).obj G).hom
            (p ≫ f false) p q rfl H.w.symm ≫ (pullback q).map (e true).hom := by
  let D : pullbackPseudofunctor.{u}.DescentData f := binaryDescentData f p q H M α
  obtain ⟨G, ⟨e⟩⟩ := exists_glued_of_openCover f hcover D
  let ε (b : Bool) : (pullback (f b)).obj G ≅ M b := descentIsoApp e b
  have hG : G.IsFinitePresentation := finitePresentation_of_binary_pullback_isos X f hcover G M ε
  refine ⟨G, hG, ε, ?_⟩
  have h := e.hom.comm (p ≫ f false) p q rfl H.w.symm
  rw [binaryDescentData_hom_overlap] at h
  exact h


/-- Compatible actual local isomorphisms on a binary open cover glue to an
isomorphism of the two original module sheaves. -/
theorem nonempty_iso_of_binary_restrictions
    {S W : Scheme.{u}} (X : Bool → Scheme.{u})
    (f : ∀ b, X b ⟶ S) [∀ b, IsOpenImmersion (f b)]
    (hcover : IsOpenCover (fun b ↦ (f b).opensRange))
    (p : W ⟶ X false) (q : W ⟶ X true)
    (H : IsPullback p q (f false) (f true))
    (M N : S.Modules) (ε : ∀ b, (pullback (f b)).obj M ≅ (pullback (f b)).obj N)
    (h : (pullback p).map (ε false).hom ≫
        ((pullbackPseudofunctor.toDescentData f).obj N).hom
          (p ≫ f false) p q rfl H.w.symm =
      ((pullbackPseudofunctor.toDescentData f).obj M).hom
          (p ≫ f false) p q rfl H.w.symm ≫ (pullback q).map (ε true).hom) :
    Nonempty (M ≅ N) := by
  have hsurj (x : S) : ∃ b, ∃ y, f b y = x := hcover.exists_mem x
  let FF := fullyFaithfulToDescentDataOfOpenImmersion f hsurj
  exact ⟨FF.preimageIso (binaryDescentIso f p q H _ _ ε h)⟩


/-- Two original cartesian chart squares identify their overlap with the
literal base change of the original stage overlap. The projections retain
the original chart maps and the actual base projection. -/
theorem exists_binary_overlap_of_squares
    {C : Type*} [Category C] [HasPullbacks C]
    {S T : C} (ρ : S ⟶ T) (X Y : Bool → C)
    (f : ∀ b, X b ⟶ T) (g : ∀ b, Y b ⟶ S) (a : ∀ b, Y b ⟶ X b)
    (H : ∀ b, IsPullback (a b) (g b) (f b) ρ) :
    let w : Limits.pullback (f false) (f true) ⟶ T :=
      Limits.pullback.fst (f false) (f true) ≫ f false
    ∃ (p : Limits.pullback ρ w ⟶ Y false) (q : Limits.pullback ρ w ⟶ Y true),
      IsPullback p q (g false) (g true) ∧
      p ≫ a false = Limits.pullback.snd ρ w ≫ Limits.pullback.fst (f false) (f true) ∧
      q ≫ a true = Limits.pullback.snd ρ w ≫ Limits.pullback.snd (f false) (f true) ∧
      p ≫ g false = Limits.pullback.fst ρ w ∧
      q ≫ g true = Limits.pullback.fst ρ w := by
  let w : Limits.pullback (f false) (f true) ⟶ T :=
    Limits.pullback.fst (f false) (f true) ≫ f false
  let πW := Limits.pullback.snd ρ w
  let β := Limits.pullback.fst ρ w
  have h₀ : (πW ≫ Limits.pullback.fst (f false) (f true)) ≫ f false = β ≫ ρ := by
    simpa only [πW, β, w, Category.assoc] using
      (Limits.pullback.condition (f := ρ) (g := w)).symm
  have h₁ : (πW ≫ Limits.pullback.snd (f false) (f true)) ≫ f true = β ≫ ρ := by
    calc
      _ = (πW ≫ Limits.pullback.fst (f false) (f true)) ≫ f false := by
        rw [Category.assoc, Category.assoc,
          (Limits.pullback.condition (f := f false) (g := f true)).symm]
      _ = _ := h₀
  let p := (H false).lift (πW ≫ Limits.pullback.fst (f false) (f true)) β h₀
  let q := (H true).lift (πW ≫ Limits.pullback.snd (f false) (f true)) β h₁
  have hp₀ : p ≫ a false = πW ≫ Limits.pullback.fst (f false) (f true) :=
    (H false).lift_fst _ _ _
  have hq₀ : q ≫ a true = πW ≫ Limits.pullback.snd (f false) (f true) :=
    (H true).lift_fst _ _ _
  have hp₁ : p ≫ g false = β := (H false).lift_snd _ _ _
  have hq₁ : q ≫ g true = β := (H true).lift_snd _ _ _
  refine ⟨p, q, ?_, hp₀, hq₀, hp₁, hq₁⟩
  refine IsPullback.mk' (hp₁.trans hq₁.symm) ?_ ?_
  · intro Z r s hrs hqs
    apply Limits.pullback.hom_ext
    · simpa only [Category.assoc, hp₁] using congrArg (fun z ↦ z ≫ g false) hrs
    · apply Limits.pullback.hom_ext
      · simpa only [Category.assoc, hp₀] using congrArg (fun z ↦ z ≫ a false) hrs
      · simpa only [Category.assoc, hq₀] using congrArg (fun z ↦ z ≫ a true) hqs
  · intro Z x y hxy
    let z₀ : Z ⟶ Limits.pullback (f false) (f true) :=
      Limits.pullback.lift (x ≫ a false) (y ≫ a true) (by
        simpa only [Category.assoc, (H false).w, (H true).w] using
          congrArg (fun z ↦ z ≫ ρ) hxy)
    have hz : (x ≫ g false) ≫ ρ = z₀ ≫ w := by
      simpa only [z₀, w, Limits.pullback.lift_fst_assoc, Category.assoc] using
        congrArg (fun z ↦ x ≫ z) (H false).w.symm
    let z := Limits.pullback.lift (x ≫ g false) z₀ hz
    have hz₀ : z ≫ πW = z₀ := Limits.pullback.lift_snd _ _ _
    have hzβ : z ≫ β = x ≫ g false := Limits.pullback.lift_fst _ _ _
    refine ⟨z, ?_, ?_⟩
    · apply (H false).hom_ext
      · rw [Category.assoc, hp₀, ← Category.assoc, hz₀]
        exact Limits.pullback.lift_fst _ _ _
      · rw [Category.assoc, hp₁]
        exact hzβ
    · apply (H true).hom_ext
      · rw [Category.assoc, hq₀, ← Category.assoc, hz₀]
        exact Limits.pullback.lift_snd _ _ _
      · rw [Category.assoc, hq₁, hzβ]
        exact hxy

private structure OpenModuleModel
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (M : c.pt.Modules) (U : c.pt.Opens) where
  stage : I
  chart : (D.obj stage).Opens
  isCompact : IsCompact (chart : Set (D.obj stage))
  preimageEq : c.π.app stage ⁻¹ᵁ chart = U
  sheaf : chart.toScheme.Modules
  isFinitePresentation : sheaf.IsFinitePresentation
  comparison : (pullback ((c.π.app stage).resLE chart U
      (le_of_eq preimageEq.symm))).obj sheaf ≅ M.restrict U.ι

private def openModuleModelProjection
    {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
    {M : c.pt.Modules} {U : c.pt.Opens} (N : OpenModuleModel D c M U) :
    U.toScheme ⟶ N.chart.toScheme :=
  (c.π.app N.stage).resLE N.chart U (le_of_eq N.preimageEq.symm)

private theorem openModuleModelProjection_isPullback
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) (V : (D.obj i).Opens) (U : c.pt.Opens) (h : c.π.app i ⁻¹ᵁ V = U) :
    IsPullback ((c.π.app i).resLE V U (le_of_eq h.symm)) U.ι V.ι (c.π.app i) := by
  subst U
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    isPullback_morphismRestrict (c.π.app i) V

private theorem exists_openModuleModel_of_isAffineOpen
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (M : c.pt.Modules) [M.IsFinitePresentation]
    (U : c.pt.Opens) (hU : IsAffineOpen U) :
    Nonempty (OpenModuleModel D c M U) := by
  obtain ⟨i, V, hV, rfl⟩ := exists_isAffineOpen_preimage_eq D c hc U hU
  have (j : Over i) : IsAffine ((opensDiagram D i V).obj j) :=
    hV.preimage (D.map j.hom)
  have : (M.restrict (c.π.app i ⁻¹ᵁ V).ι).IsFinitePresentation :=
    finitePresentation_restrict _ M
  obtain ⟨j, _, N, hN, ⟨e⟩⟩ := exists_affine_model_above_of_isLimit
    (opensDiagram D i V) (opensCone D c i V) (isLimitOpensCone D c hc i V)
    (Over.mk (𝟙 i)) (M.restrict (c.π.app i ⁻¹ᵁ V).ι)
  have heq : c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ V) = c.π.app i ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, c.w j.hom]
  exact ⟨{
    stage := j.left
    chart := D.map j.hom ⁻¹ᵁ V
    isCompact := (hV.preimage (D.map j.hom)).isCompact
    preimageEq := heq
    sheaf := N
    isFinitePresentation := hN
    comparison := e }⟩

private def rebaseOpenModuleModel
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {M : c.pt.Modules} {U : c.pt.Opens} (N : OpenModuleModel D c M U)
    {j : I} (q : j ⟶ N.stage) : OpenModuleModel D c M U := by
  let V := D.map q ⁻¹ᵁ N.chart
  have heq : c.π.app j ⁻¹ᵁ V = U := by
    rw [← Scheme.Hom.comp_preimage, c.w q, N.preimageEq]
  let r := (D.map q).resLE N.chart V le_rfl
  let p := (c.π.app j).resLE V U (le_of_eq heq.symm)
  have hp : p ≫ r = openModuleModelProjection N := by
    apply (cancel_mono N.chart.ι).mp
    simp only [p, r, openModuleModelProjection, Category.assoc,
      Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι, c.w q]
  let := N.isFinitePresentation
  exact {
    stage := j
    chart := V
    isCompact := (D.map q).isCompact_preimage N.isCompact
    preimageEq := heq
    sheaf := (pullback r).obj N.sheaf
    isFinitePresentation := inferInstance
    comparison := (pullbackComp p r).app N.sheaf ≪≫
      (pullbackCongr hp).app N.sheaf ≪≫ N.comparison }

private theorem exists_global_of_top_openModuleModel
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (M : c.pt.Modules) (A : OpenModuleModel D c M ⊤) (hA : A.chart = ⊤) :
    ∃ N : (D.obj A.stage).Modules, N.IsFinitePresentation ∧
      Nonempty ((pullback (c.π.app A.stage)).obj N ≅ M) := by
  rcases A with ⟨i, V, hV, hpre, N, hN, e⟩
  change V = ⊤ at hA
  subst V
  let p := (c.π.app i).resLE (⊤ : (D.obj i).Opens) (⊤ : c.pt.Opens)
    (le_of_eq hpre.symm)
  have hp : p ≫ (D.obj i).topIso.hom = c.pt.topIso.hom ≫ c.π.app i :=
    Scheme.Hom.resLE_comp_ι _ _
  have heq : c.π.app i ≫ (D.obj i).topIso.inv = c.pt.topIso.inv ≫ p := by
    apply (cancel_mono (D.obj i).topIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hp,
      Iso.inv_hom_id_assoc]
  let := hN
  refine ⟨(pullback (D.obj i).topIso.inv).obj N, inferInstance, ⟨?_⟩⟩
  exact (pullbackComp (c.π.app i) (D.obj i).topIso.inv).app N ≪≫
    (pullbackCongr heq).app N ≪≫
    ((pullbackComp c.pt.topIso.inv p).app N).symm ≪≫
    (pullback c.pt.topIso.inv).mapIso e ≪≫
    (pullback c.pt.topIso.inv).mapIso
      ((restrictFunctorIsoPullback (⊤ : c.pt.Opens).ι).app M) ≪≫
    (pullbackComp c.pt.topIso.inv (⊤ : c.pt.Opens).ι).app M ≪≫
    (pullbackCongr (c.pt.topIso.inv_hom_id)).app M ≪≫ (pullbackId c.pt).app M


private def openModuleConeProjection
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) (V : (D.obj i).Opens) (U : c.pt.Opens)
    (h : c.π.app i ⁻¹ᵁ V = U) (j : Over i) :
    U.toScheme ⟶ ((opensDiagram D i V).obj j) :=
  (c.π.app j.left).resLE (D.map j.hom ⁻¹ᵁ V) U (le_of_eq (by
    rw [← Scheme.Hom.comp_preimage, c.w j.hom, h]))

private theorem openModuleConeProjection_comp_ι
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) (V : (D.obj i).Opens) (U : c.pt.Opens)
    (h : c.π.app i ⁻¹ᵁ V = U) (j : Over i) :
    openModuleConeProjection D c i V U h j ≫ (D.map j.hom ⁻¹ᵁ V).ι =
      U.ι ≫ c.π.app j.left := Scheme.Hom.resLE_comp_ι _ _

private def openModuleCone
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) (V : (D.obj i).Opens) (U : c.pt.Opens)
    (h : c.π.app i ⁻¹ᵁ V = U) : Cone (opensDiagram D i V) where
  pt := U
  π.app j := openModuleConeProjection D c i V U h j
  π.naturality {j k} f := by
    change 𝟙 U.toScheme ≫ openModuleConeProjection D c i V U h k =
      openModuleConeProjection D c i V U h j ≫ (opensDiagram D i V).map f
    rw [Category.id_comp]
    symm
    apply (cancel_mono (D.map k.hom ⁻¹ᵁ V).ι).mp
    have hι : (opensDiagram D i V).map f ≫ (D.map k.hom ⁻¹ᵁ V).ι =
        (D.map j.hom ⁻¹ᵁ V).ι ≫ D.map f.left := by
      simpa only [opensDiagramι, Functor.comp_map, Over.forget_map] using
        (opensDiagramι D i V).naturality f
    calc
      _ = openModuleConeProjection D c i V U h j ≫
          (D.map j.hom ⁻¹ᵁ V).ι ≫ D.map f.left := by
        rw [Category.assoc, hι]
      _ = U.ι ≫ c.π.app j.left ≫ D.map f.left := by
        rw [← Category.assoc, openModuleConeProjection_comp_ι]
        simp only [Category.assoc]
      _ = U.ι ≫ c.π.app k.left := by rw [c.w f.left]
      _ = _ := (openModuleConeProjection_comp_ι D c i V U h k).symm

private def isLimitOpenModuleCone
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i : I) (V : (D.obj i).Opens) (U : c.pt.Opens)
    (h : c.π.app i ⁻¹ᵁ V = U) : IsLimit (openModuleCone D c i V U h) := by
  apply (isLimitOpensCone D c hc i V).ofIsoLimit
  refine (Cone.ext (c.pt.isoOfEq h.symm) ?_).symm
  intro j
  apply (cancel_mono (D.map j.hom ⁻¹ᵁ V).ι).mp
  simp only [Category.assoc, opensCone, openModuleCone, openModuleConeProjection,
    Scheme.Hom.resLE_comp_ι, Scheme.isoOfEq_hom_ι_assoc]


/-- Actual finitely presented objects on finitely many affine base changes
have models at one common stage, with the original native pullback maps.
The finite family can be the affine charts of a given stage scheme. -/
theorem exists_common_models_on_affine_baseChanges
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {A : Type u} [Finite A] (X : A → Scheme.{u}) [∀ a, IsAffine (X a)]
    (f : ∀ a, X a ⟶ D.obj i)
    (M : ∀ a, (Limits.pullback (c.π.app i) (f a)).Modules)
    [∀ a, (M a).IsFinitePresentation] :
    ∃ (j : Over i)
      (N : ∀ a, ((Scheme.baseChangeDiagram D i (f a)).obj j).Modules),
      (∀ a, (N a).IsFinitePresentation) ∧
      ∀ a, Nonempty ((pullback ((Scheme.baseChangeCone D c i (f a)).π.app j)).obj
        (N a) ≅ M a) := by
  classical
  choose j N hN he using fun a : A ↦
    exists_model_on_affine_baseChanges D c hc i (f a) (M a)
  obtain ⟨k, p, v, hv⟩ := IsCofiltered.wideCospan (fun a ↦ (j a).hom)
  let o : Over i := Over.mk p
  let q (a : A) : o ⟶ j a := Over.homMk (v a) (hv a)
  let N' (a : A) :=
    (pullback ((Scheme.baseChangeDiagram D i (f a)).map (q a))).obj (N a)
  refine ⟨o, N', ?_, ?_⟩
  · intro a
    have : (N a).IsFinitePresentation := hN a
    exact inferInstanceAs ((N' a).IsFinitePresentation)
  · intro a
    let D' := Scheme.baseChangeDiagram D i (f a)
    let c' := Scheme.baseChangeCone D c i (f a)
    exact ⟨(pullbackComp (c'.π.app o) (D'.map (q a))).app (N a) ≪≫
      (pullbackCongr (c'.w (q a))).app (N a) ≪≫ (he a).some⟩




private theorem pullbackCongr_symm_hom
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (pullbackCongr h.symm).hom.app M = (pullbackCongr h).inv.app M := by
  cases h
  rfl

set_option backward.defeqAttrib.useBackward true in
private theorem pullFunctor_hom_on_overlap
    {S T W Z : Scheme.{u}} (ρ : S ⟶ T) (X Y : Bool → Scheme.{u})
    (f : ∀ b, X b ⟶ T) (g : ∀ b, Y b ⟶ S)
    (a : ∀ b, Y b ⟶ X b) (ha : ∀ b, a b ≫ f b = g b ≫ ρ)
    (p : W ⟶ X false) (q : W ⟶ X true) (hw : p ≫ f false = q ≫ f true)
    (p' : Z ⟶ Y false) (q' : Z ⟶ Y true) (hw' : p' ≫ g false = q' ≫ g true)
    (l : Z ⟶ W) (hp : l ≫ p = p' ≫ a false) (hq : l ≫ q = q' ≫ a true)
    (D : pullbackPseudofunctor.DescentData f) :
    let K := (CategoryTheory.Pseudofunctor.DescentData.pullFunctor
      pullbackPseudofunctor (α := id) ha).obj D
    K.hom (p' ≫ g false) p' q' rfl hw'.symm =
      (pullbackSquareIso p' l (a false) p hp.symm).inv.app (D.obj false) ≫
        (pullback l).map (D.hom (p ≫ f false) p q rfl hw.symm) ≫
        (pullbackSquareIso q' l (a true) q hq.symm).hom.app (D.obj true) := by
  have ht : l ≫ (p ≫ f false) = (p' ≫ g false) ≫ ρ := by
    rw [← Category.assoc, hp, Category.assoc, ha false, Category.assoc]
  have hd := (D.pullHom_hom l (p ≫ f false) ((p' ≫ g false) ≫ ρ) ht p q
    rfl hw.symm (p' ≫ a false) (q' ≫ a true) hp hq).symm
  change (pullbackComp p' (a false)).hom.app (D.obj false) ≫
      D.hom ((p' ≫ g false) ≫ ρ) (p' ≫ a false) (q' ≫ a true) _ _ ≫
      (pullbackComp q' (a true)).inv.app (D.obj true) = _
  rw [hd]
  dsimp only [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rw [pullbackPseudofunctor_mapComp'_hom_app p l (p' ≫ a false) hp (D.obj false),
    pullbackPseudofunctor_mapComp'_inv_app q l (q' ≫ a true) hq (D.obj true)]
  simp only [pullbackPseudofunctor_map_toFunctor, pullbackSquareIso,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Category.assoc]
  rw [pullbackCongr_symm_hom hp (D.obj false)]

set_option backward.defeqAttrib.useBackward true in
private theorem binary_pullFunctor_hom
    {S T W Z : Scheme.{u}} (ρ : S ⟶ T) (X Y : Bool → Scheme.{u})
    (f : ∀ b, X b ⟶ T) (g : ∀ b, Y b ⟶ S)
    (a : ∀ b, Y b ⟶ X b) (ha : ∀ b, a b ≫ f b = g b ≫ ρ)
    [∀ b, Mono (f b)]
    (p : W ⟶ X false) (q : W ⟶ X true) (H : IsPullback p q (f false) (f true))
    (p' : Z ⟶ Y false) (q' : Z ⟶ Y true) (H' : IsPullback p' q' (g false) (g true))
    (l : Z ⟶ W) (hp : l ≫ p = p' ≫ a false) (hq : l ≫ q = q' ≫ a true)
    (N : ∀ b, (X b).Modules)
    (α : (pullback p).obj (N false) ≅ (pullback q).obj (N true)) :
    let K := (CategoryTheory.Pseudofunctor.DescentData.pullFunctor
      pullbackPseudofunctor (α := id) ha).obj
        (binaryDescentData (F := pullbackPseudofunctor) f p q H N α)
    K.hom (p' ≫ g false) p' q' rfl H'.w.symm =
      (pullbackSquareIso p' l (a false) p hp.symm).inv.app (N false) ≫
        (pullback l).map α.hom ≫
        (pullbackSquareIso q' l (a true) q hq.symm).hom.app (N true) := by
  have h := pullFunctor_hom_on_overlap ρ X Y f g a ha p q H.w p' q' H'.w l hp hq
    (binaryDescentData (F := pullbackPseudofunctor) f p q H N α)
  simpa only [binaryDescentData_hom_overlap, binaryDescentData_obj] using h

private theorem eq_comp_hom_of_comp_inv_eq
    {C : Type*} [Category C] {A B C' : C} (e : B ≅ C')
    (f : A ⟶ C') (g : A ⟶ B) (h : f ≫ e.inv = g) : f = g ≫ e.hom := by
  calc
    f = (f ≫ e.inv) ≫ e.hom := by
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    _ = g ≫ e.hom := congrArg (fun t ↦ t ≫ e.hom) h

private theorem eq_comp_inv_of_comp_hom_eq
    {C : Type*} [Category C] {A B C' : C} (e : B ≅ C')
    (f : A ⟶ B) (g : A ⟶ C') (h : f ≫ e.hom = g) : f = g ≫ e.inv := by
  calc
    f = (f ≫ e.hom) ≫ e.inv := by
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    _ = g ≫ e.inv := congrArg (fun t ↦ t ≫ e.inv) h

private theorem exists_binary_glued_and_recovered
    {S T W Z : Scheme.{u}} (ρ : S ⟶ T) (X Y : Bool → Scheme.{u})
    (f : ∀ b, X b ⟶ T) (g : ∀ b, Y b ⟶ S)
    [∀ b, IsOpenImmersion (f b)] [∀ b, IsOpenImmersion (g b)]
    (hcover : IsOpenCover (fun b ↦ (f b).opensRange))
    (hcover' : IsOpenCover (fun b ↦ (g b).opensRange))
    (a : ∀ b, Y b ⟶ X b) (ha : ∀ b, a b ≫ f b = g b ≫ ρ)
    (p : W ⟶ X false) (q : W ⟶ X true) (H : IsPullback p q (f false) (f true))
    (p' : Z ⟶ Y false) (q' : Z ⟶ Y true) (H' : IsPullback p' q' (g false) (g true))
    (l : Z ⟶ W) (hp : l ≫ p = p' ≫ a false) (hq : l ≫ q = q' ≫ a true)
    (N : ∀ b, (X b).Modules) [∀ b, (N b).IsFinitePresentation]
    (M : S.Modules) (e : ∀ b, (pullback (a b)).obj (N b) ≅ (pullback (g b)).obj M)
    (α : (pullback p).obj (N false) ≅ (pullback q).obj (N true))
    (hα : (pullbackSquareIso p' l (a false) p hp.symm).inv.app (N false) ≫
        (pullback l).map α.hom ≫
        (pullbackSquareIso q' l (a true) q hq.symm).hom.app (N true) =
      (pullback p').map (e false).hom ≫
        ((pullbackPseudofunctor.toDescentData g).obj M).hom
          (p' ≫ g false) p' q' rfl H'.w.symm ≫
        (pullback q').map (e true).inv) :
    ∃ G : T.Modules, G.IsFinitePresentation ∧
      Nonempty ((pullback ρ).obj G ≅ M) := by
  let D : pullbackPseudofunctor.DescentData f :=
    binaryDescentData (F := pullbackPseudofunctor) f p q H N α
  obtain ⟨G, ⟨ε⟩⟩ := exists_glued_of_openCover f hcover D
  have hG : G.IsFinitePresentation := finitePresentation_of_binary_pullback_isos X f
    hcover G N (fun b ↦ descentIsoApp ε b)
  let B : pullbackPseudofunctor.DescentData f ⥤ pullbackPseudofunctor.DescentData g :=
    CategoryTheory.Pseudofunctor.DescentData.pullFunctor pullbackPseudofunctor (α := id) ha
  let E := (pullbackPseudofunctor.toDescentData g).obj M
  have hE : (pullback p').map (e false).hom ≫ E.hom
        (p' ≫ g false) p' q' rfl H'.w.symm =
      (B.obj D).hom (p' ≫ g false) p' q' rfl H'.w.symm ≫
        (pullback q').map (e true).hom := by
    rw [binary_pullFunctor_hom ρ X Y f g a ha p q H p' q' H' l hp hq N α]
    exact eq_comp_hom_of_comp_inv_eq ((pullback q').mapIso (e true)) _ _
      (by simpa only [E, Functor.mapIso_inv, Category.assoc] using hα.symm)
  let η : B.obj D ≅ E :=
    binaryDescentIso (F := pullbackPseudofunctor) g p' q' H' _ _ e hE
  let γ : (pullbackPseudofunctor.toDescentData g).obj ((pullback ρ).obj G) ≅ E :=
    ((CategoryTheory.Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
      pullbackPseudofunctor ha).app G).symm ≪≫ B.mapIso ε ≪≫ η
  have hsurj (x : S) : ∃ b, ∃ y, g b y = x := hcover'.exists_mem x
  let FF := fullyFaithfulToDescentDataOfOpenImmersion g hsurj
  exact ⟨G, hG, ⟨FF.preimageIso γ⟩⟩


private def binaryOpenCover {S : Scheme.{u}} (U V : S.Opens) :
    (U ⊔ V).toScheme.OpenCover where
  I₀ := Bool
  X := Bool.rec U.toScheme V.toScheme
  f := Bool.rec (S.homOfLE le_sup_left) (S.homOfLE le_sup_right)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      rcases x.2 with hx | hx
      · exact ⟨false, ⟨x.1, hx⟩, S.homOfLE_apply' le_sup_left x.1 hx⟩
      · exact ⟨true, ⟨x.1, hx⟩, S.homOfLE_apply' le_sup_right x.1 hx⟩
    · intro b
      cases b <;> infer_instance

private def openModuleStructure
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    (i : I) (V : (D.obj i).Opens) :
    opensDiagram D i V ⟶ (Functor.const (Over i)).obj V.toScheme where
  app j := (D.map j.hom).resLE V (D.map j.hom ⁻¹ᵁ V) le_rfl
  naturality {j k} q := by
    apply (cancel_mono V.ι).mp
    change ((opensDiagram D i V).map q ≫ _) ≫ V.ι = (_ ≫ 𝟙 V.toScheme) ≫ V.ι
    rw [Category.comp_id, Category.assoc, Scheme.Hom.resLE_comp_ι]
    have hι := (opensDiagramι D i V).naturality q
    simp only [opensDiagramι, Functor.comp_map, Over.forget_map] at hι
    rw [← Category.assoc, hι, Category.assoc, ← D.map_comp, Over.w q]
    exact (Scheme.Hom.resLE_comp_ι _ _).symm

private theorem openModuleCone_structure
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) (V : (D.obj i).Opens) (U : c.pt.Opens)
    (h : c.π.app i ⁻¹ᵁ V = U) (j : Over i) :
    (openModuleCone D c i V U h).π.app j ≫ (openModuleStructure D i V).app j =
      (c.π.app i).resLE V U (le_of_eq h.symm) := by
  change openModuleConeProjection D c i V U h j ≫
    (D.map j.hom).resLE V (D.map j.hom ⁻¹ᵁ V) le_rfl =
      (c.π.app i).resLE V U (le_of_eq h.symm)
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    openModuleConeProjection_comp_ι, Category.assoc, c.w j.hom,
    Scheme.Hom.resLE_comp_ι]

private def coverProjectionOfComp
    {S B T X Y : Scheme.{u}} (ρ : S ⟶ T) (b : S ⟶ B) (r : B ⟶ T)
    (h : b ≫ r = ρ) (f : X ⟶ T) (g : Y ⟶ S) (a : Y ⟶ X)
    (ha : a ≫ f = g ≫ ρ) : Y ⟶ Limits.pullback r f :=
  Limits.pullback.lift (g ≫ b) a (by rw [Category.assoc, h]; exact ha.symm)

private theorem coverProjectionOfComp_isPullback
    {S B T X Y : Scheme.{u}} (ρ : S ⟶ T) (b : S ⟶ B) (r : B ⟶ T)
    (h : b ≫ r = ρ) (f : X ⟶ T) (g : Y ⟶ S) (a : Y ⟶ X)
    (H : IsPullback a g f ρ) :
    IsPullback (coverProjectionOfComp ρ b r h f g a H.w) g
      (Limits.pullback.fst r f) b := by
  refine IsPullback.of_right (h₁₂ := Limits.pullback.snd r f) ?_ ?_
    (IsPullback.of_hasPullback r f).flip
  · simpa only [coverProjectionOfComp, Limits.pullback.lift_snd, h] using H
  · exact Limits.pullback.lift_fst _ _ _

private def restrictHomOfLEIso {S : Scheme.{u}} (M : S.Modules)
    {U V : S.Opens} (h : U ≤ V) :
    M.restrict U.ι ≅ (pullback (S.homOfLE h)).obj (M.restrict V.ι) :=
  ((restrictFunctorCongr (S.homOfLE_ι h)).app M).symm ≪≫
    (restrictFunctorComp (S.homOfLE h) V.ι).app M ≪≫
    (restrictFunctorIsoPullback (S.homOfLE h)).app (M.restrict V.ι)



private def rebaseCoverProjection
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (q : j ⟶ i) {X V : Scheme.{u}}
    (f : X ⟶ D.obj i) (F : V ⟶ c.pt) (a : V ⟶ X)
    (ha : a ≫ f = F ≫ c.π.app i) :
    V ⟶ Limits.pullback (D.map q) f :=
  coverProjectionOfComp (c.π.app i) (c.π.app j) (D.map q) (c.w q) f F a ha

private theorem rebaseCoverProjection_isPullback
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (q : j ⟶ i) {X V : Scheme.{u}}
    (f : X ⟶ D.obj i) (F : V ⟶ c.pt) (a : V ⟶ X)
    (H : IsPullback a F f (c.π.app i)) :
    IsPullback (rebaseCoverProjection D c q f F a H.w) F
      (Limits.pullback.fst (D.map q) f) (c.π.app j) :=
  coverProjectionOfComp_isPullback (c.π.app i) (c.π.app j) (D.map q) (c.w q) f F a H


private theorem exists_baseChange_relative_iso
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {W : Scheme.{u}} (f : W ⟶ D.obj i) [QuasiCompact f] [QuasiSeparated f]
    (M N : W.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (e : (pullback (Limits.pullback.snd (c.π.app i) f)).obj M ≅
      (pullback (Limits.pullback.snd (c.π.app i) f)).obj N) :
    ∃ (j : Over i)
      (e' : (pullback (Limits.pullback.snd (D.map j.hom) f)).obj M ≅
        (pullback (Limits.pullback.snd (D.map j.hom) f)).obj N),
      pullbackHomOfTriangle ((Scheme.baseChangeCone D c i f).π.app j)
        (Limits.pullback.snd (D.map j.hom) f) (Limits.pullback.snd (c.π.app i) f)
        (Scheme.baseChangeCone_π_app_snd D c i f j) e'.hom = e.hom := by
  let D' := Scheme.baseChangeDiagram D i f
  let c' := Scheme.baseChangeCone D c i f
  let t : D' ⟶ (Functor.const (Over i)).obj W :=
    { app j := Limits.pullback.snd (D.map j.hom) f
      naturality {j k} q := by
        change D'.map q ≫ Limits.pullback.snd (D.map k.hom) f =
          Limits.pullback.snd (D.map j.hom) f ≫ 𝟙 W
        rw [Category.comp_id]
        exact Scheme.baseChangeDiagram_map_snd D i f q }
  have hl (j : Over i) : c'.π.app j ≫ t.app j = Limits.pullback.snd (c.π.app i) f :=
    Scheme.baseChangeCone_π_app_snd D c i f j
  have {j k : Over i} (q : j ⟶ k) : IsAffineHom (D'.map q) := inferInstance
  have (j : Over i) : CompactSpace (D'.obj j) := inferInstance
  have (j : Over i) : QuasiSeparatedSpace (D'.obj j) := inferInstance
  obtain ⟨j, _, E, hE, _⟩ := exists_relative_iso_above_of_isLimit D' c'
    (Scheme.isLimitBaseChangeCone D c hc i f) t (Limits.pullback.snd (c.π.app i) f)
    hl (Over.mk (𝟙 i)) M N e
  exact ⟨j, E, hE⟩

private theorem pullbackSquareIso_cone_cancel_hom
    {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
    (p : X₁ ⟶ X₀) (q : X₂ ⟶ X₁) (r : X₂ ⟶ X₀) (hr : q ≫ p = r)
    (φ : S₁ ⟶ S₀) (ψ : S₂ ⟶ S₁) (ρ : S₂ ⟶ S₀) (hρ : ψ ≫ φ = ρ)
    (a₀ : S₀ ⟶ X₀) (a₁ : S₁ ⟶ X₁) (a₂ : S₂ ⟶ X₂)
    (w₁ : φ ≫ a₀ = a₁ ≫ p) (w₂ : ψ ≫ a₁ = a₂ ≫ q) (w₀ : ρ ≫ a₀ = a₂ ≫ r)
    (M : X₀.Modules) :
    (pullbackTriangleIso ψ φ ρ hρ).inv.app ((pullback a₀).obj M) ≫
        (pullback ψ).map ((pullbackSquareIso a₁ φ p a₀ w₁.symm).hom.app M) =
      (pullbackSquareIso a₂ ρ r a₀ w₀.symm).hom.app M ≫
        (((pullbackSquareIso a₂ ψ q a₁ w₂.symm).app ((pullback p).obj M)) ≪≫
          (pullback a₂).mapIso ((pullbackTriangleIso q p r hr).app M)).inv := by
  apply (cancel_mono
    ((pullbackSquareIso a₂ ψ q a₁ w₂.symm).hom.app ((pullback p).obj M))).mp
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using
      pullbackSquareIso_cone_hom p q r hr φ ψ ρ hρ a₀ a₁ a₂ w₁ w₂ w₀ M

private theorem conjugate_overlap_recovery
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {P Q : C} {P' Q' X Y : D}
    (β₀ : G.obj P ≅ P') (β₁ : G.obj Q ≅ Q')
    (u₀ : P' ≅ X) (u₁ : Q' ≅ Y) (α : P ⟶ Q) (z : X ⟶ Y)
    (h : (β₀ ≪≫ u₀).inv ≫ G.map α = z ≫ (β₁ ≪≫ u₁).inv) :
    β₀.inv ≫ G.map α ≫ β₁.hom = u₀.hom ≫ z ≫ u₁.inv := by
  apply (cancel_epi u₀.inv).mp
  apply (cancel_mono β₁.inv).mp
  simpa only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using h

private theorem binary_refinement_recovery
    {W W' Z : Scheme.{u}} (X X' Y : Bool → Scheme.{u})
    (s : ∀ b, X' b ⟶ X b) (a' : ∀ b, Y b ⟶ X' b) (a : ∀ b, Y b ⟶ X b)
    (hs : ∀ b, a' b ≫ s b = a b)
    (sk : W' ⟶ W) (lk : Z ⟶ W') (l : Z ⟶ W) (hl : lk ≫ sk = l)
    (r : ∀ b, W ⟶ X b) (rk : ∀ b, W' ⟶ X' b) (rInf : ∀ b, Z ⟶ Y b)
    (hStage : ∀ b, sk ≫ r b = rk b ≫ s b)
    (hMiddle : ∀ b, lk ≫ rk b = rInf b ≫ a' b)
    (hInf : ∀ b, l ≫ r b = rInf b ≫ a b)
    (N : ∀ b, (X b).Modules)
    (z : (pullback (rInf false)).obj ((pullback (a false)).obj (N false)) ⟶
      (pullback (rInf true)).obj ((pullback (a true)).obj (N true)))
    (E : (pullback sk).obj ((pullback (r false)).obj (N false)) ≅
      (pullback sk).obj ((pullback (r true)).obj (N true)))
    (hE : pullbackHomOfTriangle lk sk l hl E.hom =
      (pullbackSquareIso (rInf false) l (a false) (r false) (hInf false).symm).hom.app
          (N false) ≫ z ≫
        (pullbackSquareIso (rInf true) l (a true) (r true) (hInf true).symm).inv.app (N true)) :
    let T (b : Bool) := pullbackTriangleIso (a' b) (s b) (a b) (hs b)
    let N' (b : Bool) := (pullback (s b)).obj (N b)
    let βk (b : Bool) :=
      (pullbackSquareIso (rk b) sk (s b) (r b) (hStage b).symm).app (N b)
    let βdirect (b : Bool) :=
      (pullbackSquareIso (rInf b) lk (a' b) (rk b) (hMiddle b).symm).app (N' b)
    (βdirect false).inv ≫
        (pullback lk).map (((βk false).symm ≪≫ E ≪≫ βk true).hom) ≫
        (βdirect true).hom =
      (pullback (rInf false)).map ((T false).hom.app (N false)) ≫ z ≫
        (pullback (rInf true)).map ((T true).inv.app (N true)) := by
  dsimp only
  let T (b : Bool) := pullbackTriangleIso (a' b) (s b) (a b) (hs b)
  let P (b : Bool) := (pullback (r b)).obj (N b)
  let βInf (b : Bool) :=
    (pullbackSquareIso (rInf b) l (a b) (r b) (hInf b).symm).app (N b)
  let βk (b : Bool) :=
    (pullbackSquareIso (rk b) sk (s b) (r b) (hStage b).symm).app (N b)
  let βdirect (b : Bool) :=
    (pullbackSquareIso (rInf b) lk (a' b) (rk b) (hMiddle b).symm).app
      ((pullback (s b)).obj (N b))
  let L (b : Bool) := βdirect b ≪≫ (pullback (rInf b)).mapIso ((T b).app (N b))
  let V := (pullbackTriangleIso lk sk l hl).symm
  have hβ (b : Bool) : V.hom.app (P b) ≫ (pullback lk).map (βk b).hom =
      (βInf b).hom ≫ (L b).inv :=
    pullbackSquareIso_cone_cancel_hom (s b) (a' b) (a b) (hs b)
      sk lk l hl (r b) (rk b) (rInf b) (hStage b) (hMiddle b) (hInf b) (N b)
  have hLift : V.hom.app (P false) ≫ (pullback lk).map E.hom =
      ((βInf false).hom ≫ z ≫ (βInf true).inv) ≫ V.hom.app (P true) := by
    exact eq_comp_inv_of_comp_hom_eq ((pullbackTriangleIso lk sk l hl).app (P true))
      _ _ hE
  have hRecovery := lift_conjugate_recovery (pullback l) (pullback sk) (pullback lk) V
    (βInf false) (βInf true) (βk false) (βk true) (L false) (L true)
    (hβ false) (hβ true) z E.hom hLift
  have H := conjugate_overlap_recovery (pullback lk) (βdirect false) (βdirect true)
    ((pullback (rInf false)).mapIso ((T false).app (N false)))
    ((pullback (rInf true)).mapIso ((T true).app (N true)))
    (((βk false).symm ≪≫ E ≪≫ βk true).hom) z hRecovery
  exact H

private theorem exists_binary_glued_of_refinement
    {S B W Wk Z : Scheme.{u}} (ρ₁ : S ⟶ B) (X X' Y : Bool → Scheme.{u})
    (f' : ∀ b, X' b ⟶ B) (g : ∀ b, Y b ⟶ S)
    [∀ b, IsOpenImmersion (f' b)] [∀ b, IsOpenImmersion (g b)]
    (hcoverk : IsOpenCover (fun b ↦ (f' b).opensRange))
    (hcover' : IsOpenCover (fun b ↦ (g b).opensRange))
    (s : ∀ b, X' b ⟶ X b) (a' : ∀ b, Y b ⟶ X' b) (a : ∀ b, Y b ⟶ X b)
    (hs : ∀ b, a' b ≫ s b = a b) (ha : ∀ b, a' b ≫ f' b = g b ≫ ρ₁)
    (p : W ⟶ X false) (q : W ⟶ X true)
    (pk : Wk ⟶ X' false) (qk : Wk ⟶ X' true)
    (Hk : IsPullback pk qk (f' false) (f' true))
    (pInf : Z ⟶ Y false) (qInf : Z ⟶ Y true)
    (HInf : IsPullback pInf qInf (g false) (g true))
    (sk : Wk ⟶ W) (lk : Z ⟶ Wk) (l : Z ⟶ W) (hlk : lk ≫ sk = l)
    (hpk : sk ≫ p = pk ≫ s false) (hqk : sk ≫ q = qk ≫ s true)
    (hlp : lk ≫ pk = pInf ≫ a' false) (hlq : lk ≫ qk = qInf ≫ a' true)
    (hpInf : l ≫ p = pInf ≫ a false) (hqInf : l ≫ q = qInf ≫ a true)
    (N : ∀ b, (X b).Modules) [∀ b, (N b).IsFinitePresentation]
    (M : S.Modules) (e : ∀ b, (pullback (a b)).obj (N b) ≅ (pullback (g b)).obj M)
    (E : (pullback sk).obj ((pullback p).obj (N false)) ≅
      (pullback sk).obj ((pullback q).obj (N true)))
    (hE : pullbackHomOfTriangle lk sk l hlk E.hom =
      (((pullbackSquareIso pInf l (a false) p hpInf.symm).app (N false)) ≪≫
        (pullback pInf).mapIso (e false) ≪≫
        ((pullbackPseudofunctor.toDescentData g).obj M).iso
          (pInf ≫ g false) pInf qInf rfl HInf.w.symm ≪≫
        (pullback qInf).mapIso (e true).symm ≪≫
        ((pullbackSquareIso qInf l (a true) q hqInf.symm).app (N true)).symm).hom) :
    ∃ G : B.Modules, G.IsFinitePresentation ∧ Nonempty ((pullback ρ₁).obj G ≅ M) := by
  let r : ∀ b : Bool, W ⟶ X b := fun | false => p | true => q
  let rk : ∀ b : Bool, Wk ⟶ X' b := fun | false => pk | true => qk
  let rInf : ∀ b : Bool, Z ⟶ Y b := fun | false => pInf | true => qInf
  have hStage (b : Bool) : sk ≫ r b = rk b ≫ s b := by
    cases b
    · exact hpk
    · exact hqk
  have hMiddle (b : Bool) : lk ≫ rk b = rInf b ≫ a' b := by
    cases b
    · exact hlp
    · exact hlq
  have hInf (b : Bool) : l ≫ r b = rInf b ≫ a b := by
    cases b
    · exact hpInf
    · exact hqInf
  let βInf (b : Bool) :=
    (pullbackSquareIso (rInf b) l (a b) (r b) (hInf b).symm).app (N b)
  let τ := ((pullbackPseudofunctor.toDescentData g).obj M).iso
    (pInf ≫ g false) pInf qInf rfl HInf.w.symm
  let U (b : Bool) := (pullbackTriangleIso (a' b) (s b) (a b) (hs b)).symm
  let N' (b : Bool) := (pullback (s b)).obj (N b)
  have (b : Bool) : (N' b).IsFinitePresentation := inferInstance
  let e' (b : Bool) : (pullback (a' b)).obj (N' b) ≅ (pullback (g b)).obj M :=
    ((U b).app (N b)).symm ≪≫ e b
  let βk (b : Bool) :=
    (pullbackSquareIso (rk b) sk (s b) (r b) (hStage b).symm).app (N b)
  let βdirect (b : Bool) :=
    (pullbackSquareIso (rInf b) lk (a' b) (rk b) (hMiddle b).symm).app (N' b)
  let z := (pullback pInf).map (e false).hom ≫ τ.hom ≫ (pullback qInf).map (e true).inv
  let α : (pullback pk).obj (N' false) ≅ (pullback qk).obj (N' true) :=
    (βk false).symm ≪≫ E ≪≫ βk true
  have hE' : pullbackHomOfTriangle lk sk l hlk E.hom =
      (βInf false).hom ≫ z ≫ (βInf true).inv := by
    simpa only [z, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc] using hE
  have hα₀ : (βdirect false).inv ≫ (pullback lk).map α.hom ≫ (βdirect true).hom =
      (pullback pInf).map ((U false).inv.app (N false)) ≫ z ≫
        (pullback qInf).map ((U true).hom.app (N true)) := by
    exact binary_refinement_recovery X X' Y s a' a hs sk lk l hlk r rk rInf
      hStage hMiddle hInf N z E (by
        simpa only [βInf, Iso.app_hom, Iso.app_inv] using hE')
  have hα : (βdirect false).inv ≫ (pullback lk).map α.hom ≫ (βdirect true).hom =
      (pullback pInf).map (e' false).hom ≫ τ.hom ≫ (pullback qInf).map (e' true).inv := by
    change (βdirect false).inv ≫ (pullback lk).map α.hom ≫ (βdirect true).hom =
      (pullback pInf).map (((U false).app (N false)).inv ≫ (e false).hom) ≫
        τ.hom ≫ (pullback qInf).map ((e true).inv ≫ ((U true).app (N true)).hom)
    conv_rhs => rw [Functor.map_comp, Functor.map_comp]
    simpa only [z, Iso.app_hom, Iso.app_inv, Category.assoc] using hα₀
  obtain ⟨G, hG, heG⟩ := exists_binary_glued_and_recovered ρ₁ X' Y f' g
    hcoverk hcover' a' ha pk qk Hk pInf qInf HInf lk hlp hlq N' M e' α hα
  exact ⟨G, hG, heG⟩

private theorem exists_binary_model_of_refined_overlap
    {S T B : Scheme.{u}} (ρ : S ⟶ T) (ρ₁ : S ⟶ B) (t : B ⟶ T)
    (ht : ρ₁ ≫ t = ρ) (X Y : Bool → Scheme.{u})
    (f : ∀ b, X b ⟶ T) (g : ∀ b, Y b ⟶ S)
    [∀ b, IsOpenImmersion (f b)] [∀ b, IsOpenImmersion (g b)]
    (hcover : IsOpenCover (fun b ↦ (f b).opensRange))
    (hcover' : IsOpenCover (fun b ↦ (g b).opensRange))
    (a : ∀ b, Y b ⟶ X b) (H : ∀ b, IsPullback (a b) (g b) (f b) ρ)
    (N : ∀ b, (X b).Modules) [∀ b, (N b).IsFinitePresentation]
    (M : S.Modules) (e : ∀ b, (pullback (a b)).obj (N b) ≅ (pullback (g b)).obj M) :
    let W := Limits.pullback (f false) (f true)
    let p : W ⟶ X false := Limits.pullback.fst _ _
    let q : W ⟶ X true := Limits.pullback.snd _ _
    let w : W ⟶ T := p ≫ f false
    let Z := Limits.pullback ρ w
    let l : Z ⟶ W := Limits.pullback.snd _ _
    ∀ (pInf : Z ⟶ Y false) (qInf : Z ⟶ Y true)
      (HInf : IsPullback pInf qInf (g false) (g true))
      (hpInf : pInf ≫ a false = l ≫ p) (hqInf : qInf ≫ a true = l ≫ q)
      (_ : pInf ≫ g false = Limits.pullback.fst ρ w)
      (_ : qInf ≫ g true = Limits.pullback.fst ρ w)
      (lk : Z ⟶ Limits.pullback t w)
      (hlk : lk ≫ Limits.pullback.snd t w = l)
      (_ : lk ≫ Limits.pullback.fst t w = Limits.pullback.fst ρ w ≫ ρ₁)
      (E : (pullback (Limits.pullback.snd t w)).obj ((pullback p).obj (N false)) ≅
        (pullback (Limits.pullback.snd t w)).obj ((pullback q).obj (N true))),
      pullbackHomOfTriangle lk (Limits.pullback.snd t w) l hlk E.hom =
        (((pullbackSquareIso pInf l (a false) p hpInf).app (N false)) ≪≫
          (pullback pInf).mapIso (e false) ≪≫
          ((pullbackPseudofunctor.toDescentData g).obj M).iso
            (pInf ≫ g false) pInf qInf rfl HInf.w.symm ≪≫
          (pullback qInf).mapIso (e true).symm ≪≫
          ((pullbackSquareIso qInf l (a true) q hqInf).app (N true)).symm).hom →
      ∃ G : B.Modules, G.IsFinitePresentation ∧ Nonempty ((pullback ρ₁).obj G ≅ M) := by
  dsimp only
  intro pInf qInf HInf hpInf hqInf hpInfg hqInfg lk hlk hlkfst E hE
  let W := Limits.pullback (f false) (f true)
  let p : W ⟶ X false := Limits.pullback.fst _ _
  let q : W ⟶ X true := Limits.pullback.snd _ _
  let w : W ⟶ T := p ≫ f false
  let Z := Limits.pullback ρ w
  let l : Z ⟶ W := Limits.pullback.snd _ _
  let Wk : Scheme.{u} := Limits.pullback t w
  let X' (b : Bool) := Limits.pullback t (f b)
  let f' (b : Bool) : X' b ⟶ B := Limits.pullback.fst _ _
  let s (b : Bool) : X' b ⟶ X b := Limits.pullback.snd _ _
  let a' (b : Bool) := coverProjectionOfComp ρ ρ₁ t ht (f b) (g b) (a b) (H b).w
  have H' (b : Bool) : IsPullback (a' b) (g b) (f' b) ρ₁ :=
    coverProjectionOfComp_isPullback ρ ρ₁ t ht (f b) (g b) (a b) (H b)
  have hs (b : Bool) : a' b ≫ s b = a b := Limits.pullback.lift_snd _ _ _
  let 𝒰 : T.OpenCover :=
    { I₀ := Bool
      X := X
      f := f
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ hcover.exists_mem x, inferInstance⟩ }
  let 𝒰k : B.OpenCover := 𝒰.pullback₁ t
  have hcoverk : IsOpenCover (fun b ↦ (f' b).opensRange) := 𝒰k.isOpenCover_opensRange
  obtain ⟨pk, qk, Hk, hpk, hqk, hpkg, hqkg⟩ :=
    exists_binary_overlap_of_squares t X X' f f' s
      (fun b ↦ (IsPullback.of_hasPullback t (f b)).flip)
  let sk : Wk ⟶ W := Limits.pullback.snd t w
  have hpk' : pk ≫ s false = sk ≫ p := hpk
  have hqk' : qk ≫ s true = sk ≫ q := hqk
  have hpkg' : pk ≫ f' false = Limits.pullback.fst t w := hpkg
  have hqkg' : qk ≫ f' true = Limits.pullback.fst t w := hqkg
  have hpi : pInf ≫ a false = l ≫ p := hpInf
  have hqi : qInf ≫ a true = l ≫ q := hqInf
  have hpig : pInf ≫ g false = Limits.pullback.fst ρ w := hpInfg
  have hqig : qInf ≫ g true = Limits.pullback.fst ρ w := hqInfg
  have hlp : lk ≫ pk = pInf ≫ a' false := by
    apply Limits.pullback.hom_ext
    · change (lk ≫ pk) ≫ f' false = (pInf ≫ a' false) ≫ f' false
      rw [Category.assoc, hpkg', hlkfst, Category.assoc, (H' false).w,
        ← Category.assoc, hpig]
    · change (lk ≫ pk) ≫ s false = (pInf ≫ a' false) ≫ s false
      rw [Category.assoc, hpk', ← Category.assoc, hlk,
        Category.assoc, hs false, hpi]
  have hlq : lk ≫ qk = qInf ≫ a' true := by
    apply Limits.pullback.hom_ext
    · change (lk ≫ qk) ≫ f' true = (qInf ≫ a' true) ≫ f' true
      rw [Category.assoc, hqkg', hlkfst, Category.assoc, (H' true).w,
        ← Category.assoc, hqig]
    · change (lk ≫ qk) ≫ s true = (qInf ≫ a' true) ≫ s true
      rw [Category.assoc, hqk', ← Category.assoc, hlk,
        Category.assoc, hs true, hqi]
  exact exists_binary_glued_of_refinement ρ₁ X X' Y f' g hcoverk hcover' s a' a hs
    (fun b ↦ (H' b).w) p q pk qk Hk pInf qInf HInf sk lk l hlk hpk.symm hqk.symm
    hlp hlq hpInf.symm hqInf.symm N M e E hE

private theorem exists_binary_model_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (X Y : Bool → Scheme.{u}) [∀ b, CompactSpace (X b)]
    (f : ∀ b, X b ⟶ D.obj i) (g : ∀ b, Y b ⟶ c.pt)
    [∀ b, IsOpenImmersion (f b)] [∀ b, IsOpenImmersion (g b)]
    (hcover : IsOpenCover (fun b ↦ (f b).opensRange))
    (hcover' : IsOpenCover (fun b ↦ (g b).opensRange))
    (a : ∀ b, Y b ⟶ X b) (H : ∀ b, IsPullback (a b) (g b) (f b) (c.π.app i))
    (N : ∀ b, (X b).Modules) [∀ b, (N b).IsFinitePresentation]
    (M : c.pt.Modules) (e : ∀ b, (pullback (a b)).obj (N b) ≅ (pullback (g b)).obj M) :
    ∃ (j : I) (_ : j ⟶ i) (G : (D.obj j).Modules), G.IsFinitePresentation ∧
      Nonempty ((pullback (c.π.app j)).obj G ≅ M) := by
  let W := Limits.pullback (f false) (f true)
  let p : W ⟶ X false := Limits.pullback.fst _ _
  let q : W ⟶ X true := Limits.pullback.snd _ _
  let w : W ⟶ D.obj i := p ≫ f false
  let Z := Limits.pullback (c.π.app i) w
  let l : Z ⟶ W := Limits.pullback.snd _ _
  obtain ⟨pInf, qInf, HInf, hpInf, hqInf, hpInfg, hqInfg⟩ :=
    exists_binary_overlap_of_squares (c.π.app i) X Y f g a H
  let r : ∀ b : Bool, W ⟶ X b := fun | false => p | true => q
  let rInf : ∀ b : Bool, Z ⟶ Y b := fun | false => pInf | true => qInf
  have hInf (b : Bool) : l ≫ r b = rInf b ≫ a b := by
    cases b
    · exact hpInf.symm
    · exact hqInf.symm
  let P : Bool → W.Modules := fun b ↦ (pullback (r b)).obj (N b)
  let βInf (b : Bool) :=
    (pullbackSquareIso (rInf b) l (a b) (r b) (hInf b).symm).app (N b)
  let τ := ((pullbackPseudofunctor.toDescentData g).obj M).iso
    (pInf ≫ g false) pInf qInf rfl HInf.w.symm
  let Φ : (pullback l).obj (P false) ≅ (pullback l).obj (P true) :=
    βInf false ≪≫ (pullback pInf).mapIso (e false) ≪≫ τ ≪≫
      (pullback qInf).mapIso (e true).symm ≪≫ (βInf true).symm
  have (b : Bool) : QuasiCompact (f b) := inferInstance
  have : CompactSpace W :=
    inferInstanceAs (CompactSpace (Limits.pullback (C := Scheme.{u}) (f false) (f true)))
  have : IsOpenImmersion w := inferInstanceAs (IsOpenImmersion (p ≫ f false))
  have : QuasiCompact w := inferInstance
  have (b : Bool) : (P b).IsFinitePresentation := inferInstance
  obtain ⟨k, E, hE⟩ := exists_baseChange_relative_iso D c hc i w (P false) (P true) Φ
  let lk : Z ⟶ Limits.pullback (D.map k.hom) w :=
    (Scheme.baseChangeCone D c i w).π.app k
  obtain ⟨G, hG, heG⟩ := exists_binary_model_of_refined_overlap
    (c.π.app i) (c.π.app k.left) (D.map k.hom) (c.w k.hom)
    X Y f g hcover hcover' a H N M e pInf qInf HInf hpInf hqInf hpInfg hqInfg lk
    (Scheme.baseChangeCone_π_app_snd D c i w k)
    (Scheme.baseChangeCone_π_app_fst D c i w k) E (by exact hE)
  exact ⟨k.left, k.hom, G, hG, heG⟩

private theorem exists_openModuleModel_sup
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (M : c.pt.Modules)
    (U V : c.pt.Opens) (A : OpenModuleModel D c M U) (B : OpenModuleModel D c M V) :
    Nonempty (OpenModuleModel D c M (U ⊔ V)) := by
  let i := IsCofiltered.min A.stage B.stage
  let qA : i ⟶ A.stage := IsCofiltered.minToLeft A.stage B.stage
  let qB : i ⟶ B.stage := IsCofiltered.minToRight A.stage B.stage
  let A' := rebaseOpenModuleModel D c A qA
  let B' := rebaseOpenModuleModel D c B qB
  let VA : (D.obj i).Opens := D.map qA ⁻¹ᵁ A.chart
  let VB : (D.obj i).Opens := D.map qB ⁻¹ᵁ B.chart
  have hApre : c.π.app i ⁻¹ᵁ VA = U := A'.preimageEq
  have hBpre : c.π.app i ⁻¹ᵁ VB = V := B'.preimageEq
  let W : (D.obj i).Opens := VA ⊔ VB
  have hW : IsCompact (W : Set (D.obj i)) := A'.isCompact.union B'.isCompact
  have hpre : c.π.app i ⁻¹ᵁ W = U ⊔ V := by
    rw [Scheme.Hom.preimage_sup, hApre, hBpre]
  let p := (c.π.app i).resLE W (U ⊔ V) (le_of_eq hpre.symm)
  have HW : IsPullback p (U ⊔ V).ι W.ι (c.π.app i) :=
    openModuleModelProjection_isPullback D c i W (U ⊔ V) hpre
  let 𝒰 := binaryOpenCover VA VB
  let 𝒱 := binaryOpenCover U V
  let a₀ := (c.π.app i).resLE VA U (le_of_eq hApre.symm)
  let a₁ := (c.π.app i).resLE VB V (le_of_eq hBpre.symm)
  let a : ∀ b : Bool, 𝒱.X b ⟶ 𝒰.X b := fun | false => a₀ | true => a₁
  have hιA : (D.obj i).homOfLE (le_sup_left : VA ≤ W) ≫ W.ι = VA.ι :=
    (D.obj i).homOfLE_ι le_sup_left
  have hιB : (D.obj i).homOfLE (le_sup_right : VB ≤ W) ≫ W.ι = VB.ι :=
    (D.obj i).homOfLE_ι le_sup_right
  have hιU : c.pt.homOfLE (le_sup_left : U ≤ U ⊔ V) ≫ (U ⊔ V).ι = U.ι :=
    c.pt.homOfLE_ι le_sup_left
  have hιV : c.pt.homOfLE (le_sup_right : V ≤ U ⊔ V) ≫ (U ⊔ V).ι = V.ι :=
    c.pt.homOfLE_ι le_sup_right
  have ha₀ι : a₀ ≫ VA.ι = U.ι ≫ c.π.app i := Scheme.Hom.resLE_comp_ι _ _
  have ha₁ι : a₁ ≫ VB.ι = V.ι ≫ c.π.app i := Scheme.Hom.resLE_comp_ι _ _
  have hpι : p ≫ W.ι = (U ⊔ V).ι ≫ c.π.app i := Scheme.Hom.resLE_comp_ι _ _
  have Ha (b : Bool) : IsPullback (a b) (𝒱.f b) (𝒰.f b) p := by
    have hcomp : a b ≫ 𝒰.f b = 𝒱.f b ≫ p := by
      apply (cancel_mono W.ι).mp
      cases b
      · change (a₀ ≫ (D.obj i).homOfLE (le_sup_left : VA ≤ W)) ≫ W.ι =
          (c.pt.homOfLE (le_sup_left : U ≤ U ⊔ V) ≫ p) ≫ W.ι
        rw [Category.assoc, hιA, ha₀ι, Category.assoc, hpι, ← Category.assoc, hιU]
      · change (a₁ ≫ (D.obj i).homOfLE (le_sup_right : VB ≤ W)) ≫ W.ι =
          (c.pt.homOfLE (le_sup_right : V ≤ U ⊔ V) ≫ p) ≫ W.ι
        rw [Category.assoc, hιB, ha₁ι, Category.assoc, hpι, ← Category.assoc, hιV]
    apply IsPullback.of_bot (v₂₁ := (U ⊔ V).ι) (v₂₂ := W.ι) _ hcomp HW
    cases b
    · change IsPullback a₀ (c.pt.homOfLE le_sup_left ≫ (U ⊔ V).ι)
        ((D.obj i).homOfLE le_sup_left ≫ W.ι) (c.π.app i)
      rw [hιU, hιA]
      exact openModuleModelProjection_isPullback D c i VA U hApre
    · change IsPullback a₁ (c.pt.homOfLE le_sup_right ≫ (U ⊔ V).ι)
        ((D.obj i).homOfLE le_sup_right ≫ W.ι) (c.π.app i)
      rw [hιV, hιB]
      exact openModuleModelProjection_isPullback D c i VB V hBpre
  let N : ∀ b : Bool, (𝒰.X b).Modules := fun | false => A'.sheaf | true => B'.sheaf
  have hN (b : Bool) : (N b).IsFinitePresentation := by
    cases b
    · exact A'.isFinitePresentation
    · exact B'.isFinitePresentation
  let e0 : (pullback (a false)).obj (N false) ≅ M.restrict U.ι := A'.comparison
  let e1 : (pullback (a true)).obj (N true) ≅ M.restrict V.ι := B'.comparison
  let M' := M.restrict (U ⊔ V).ι
  let e : ∀ b : Bool, (pullback (a b)).obj (N b) ≅ (pullback (𝒱.f b)).obj M' := by
    intro b
    cases b
    · exact e0 ≪≫ restrictHomOfLEIso M le_sup_left
    · exact e1 ≪≫ restrictHomOfLEIso M le_sup_right
  let D' := opensDiagram D i W
  let c' := openModuleCone D c i W (U ⊔ V) hpre
  have hc' := isLimitOpenModuleCone D c hc i W (U ⊔ V) hpre
  let o : Over i := Over.mk (𝟙 i)
  let t := (openModuleStructure D i W).app o
  have ht : c'.π.app o ≫ t = p := openModuleCone_structure D c i W (U ⊔ V) hpre o
  let X (b : Bool) := Limits.pullback t (𝒰.f b)
  let f (b : Bool) : X b ⟶ D'.obj o := Limits.pullback.fst _ _
  let s (b : Bool) : X b ⟶ 𝒰.X b := Limits.pullback.snd _ _
  let a' (b : Bool) := coverProjectionOfComp p (c'.π.app o) t ht
    (𝒰.f b) (𝒱.f b) (a b) (Ha b).w
  have H' (b : Bool) : IsPullback (a' b) (𝒱.f b) (f b) (c'.π.app o) :=
    coverProjectionOfComp_isPullback p (c'.π.app o) t ht
      (𝒰.f b) (𝒱.f b) (a b) (Ha b)
  let N' (b : Bool) := (pullback (s b)).obj (N b)
  let e' (b : Bool) : (pullback (a' b)).obj (N' b) ≅ (pullback (𝒱.f b)).obj M' :=
    (pullbackTriangleIso (a' b) (s b) (a b) (Limits.pullback.lift_snd _ _ _)).app (N b) ≪≫ e b
  have (b : Bool) : CompactSpace (𝒰.X b) := by
    cases b
    · exact isCompact_iff_compactSpace.mp A'.isCompact
    · exact isCompact_iff_compactSpace.mp B'.isCompact
  have : QuasiSeparatedSpace W.toScheme := quasiSeparatedSpace_of_quasiSeparated W.ι
  have (b : Bool) : QuasiCompact (𝒰.f b) := inferInstance
  have (j : Over i) : CompactSpace (D'.obj j) :=
    isCompact_iff_compactSpace.mp
      ((D.map j.hom).isCompact_preimage hW)
  have (j : Over i) : QuasiSeparatedSpace (D'.obj j) :=
    quasiSeparatedSpace_of_quasiSeparated (D.map j.hom ⁻¹ᵁ W).ι
  have {j k : Over i} (r : j ⟶ k) : IsAffineHom (D'.map r) := inferInstance
  have (b : Bool) : CompactSpace (X b) := inferInstance
  have (b : Bool) : (N' b).IsFinitePresentation := inferInstance
  let 𝒰' : (D'.obj o).OpenCover := 𝒰.pullback₁ t
  have hcover : IsOpenCover (fun b ↦ (f b).opensRange) := 𝒰'.isOpenCover_opensRange
  obtain ⟨j, _, G, hG, ⟨eG⟩⟩ := exists_binary_model_above_of_isLimit D' c' hc' o X 𝒱.X
    f 𝒱.f hcover 𝒱.isOpenCover_opensRange a' H' N' M' e'
  have hpre' : c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ W) = U ⊔ V := by
    rw [← Scheme.Hom.comp_preimage, c.w j.hom, hpre]
  exact ⟨{
    stage := j.left
    chart := D.map j.hom ⁻¹ᵁ W
    isCompact := (D.map j.hom).isCompact_preimage hW
    preimageEq := hpre'
    sheaf := G
    isFinitePresentation := hG
    comparison := eG }⟩


/-- An actual finitely presented module on the limit of qcqs schemes with
actual affine transitions has a finitely presented model above any given
stage. The recovering isomorphism uses the original cone projection. -/
theorem exists_model_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (M : c.pt.Modules) [M.IsFinitePresentation] :
    ∃ (j : I) (_ : j ⟶ i₀) (N : (D.obj j).Modules), N.IsFinitePresentation ∧
      Nonempty ((pullback (c.π.app j)).obj N ≅ M) := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : IsAffineHom (c.π.app i₀) := isAffineHom_π_app D c hc i₀
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀)
  let P (U : c.pt.Opens) : Prop := Nonempty (OpenModuleModel D c M U)
  have htop : P ⊤ := by
    refine compact_open_induction_on (X := c.pt) ⊤ (by simpa using isCompact_univ) ?_ ?_
    · exact exists_openModuleModel_of_isAffineOpen D c hc M ⊥ (isAffineOpen_bot c.pt)
    · intro U _ V hU
      obtain ⟨A⟩ := hU
      obtain ⟨B⟩ := exists_openModuleModel_of_isAffineOpen D c hc M V.1 V.2
      exact exists_openModuleModel_sup D c hc M U V.1 A B
  obtain ⟨A⟩ := htop
  let B := rebaseOpenModuleModel D c A (IsCofiltered.minToRight i₀ A.stage)
  obtain ⟨j, q, hq⟩ := exists_map_eq_top D c hc B.chart B.preimageEq
  let C := rebaseOpenModuleModel D c B q
  obtain ⟨N, hN, he⟩ := exists_global_of_top_openModuleModel D c M C hq
  exact ⟨j, q ≫ IsCofiltered.minToLeft i₀ A.stage, N, hN, he⟩

/-- An actual fp module on the literal base change of an already given
qcqs scheme model descends to one actual later base change. -/
theorem exists_model_on_baseChanges
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) [QuasiCompact f] [QuasiSeparated f]
    (M : (Limits.pullback (c.π.app i) f).Modules) [M.IsFinitePresentation] :
    ∃ (j : Over i) (N : ((Scheme.baseChangeDiagram D i f).obj j).Modules),
      N.IsFinitePresentation ∧
      Nonempty ((pullback ((Scheme.baseChangeCone D c i f).π.app j)).obj N ≅ M) := by
  let D' := Scheme.baseChangeDiagram D i f
  let c' := Scheme.baseChangeCone D c i f
  obtain ⟨j, _, N, hN, he⟩ := exists_model_above_of_isLimit D' c'
    (Scheme.isLimitBaseChangeCone D c hc i f) (Over.mk (𝟙 i)) M
  exact ⟨j, N, hN, he⟩

/-- Over an actual filtered ring colimit, an fp module on the literal base
change of a given qcqs scheme has a model at one later original ring
stage, with the canonical native base-change projection as recovery map. -/
theorem exists_model_on_baseChanges_of_isColimit
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c) (i : I)
    {X : Scheme.{u}} (f : X ⟶ Spec (F.obj i)) [QuasiCompact f] [QuasiSeparated f]
    (M : (Limits.pullback (Spec.map (c.ι.app i)) f).Modules) [M.IsFinitePresentation] :
    ∃ (j : I) (q : i ⟶ j)
      (N : (Limits.pullback (Spec.map (F.map q)) f).Modules),
      N.IsFinitePresentation ∧ Nonempty
        ((pullback ((Scheme.baseChangeCone (F.op ⋙ Scheme.Spec)
          (Scheme.Spec.mapCone c.op) (.op i) f).π.app (Over.mk q.op))).obj N ≅ M) := by
  let D := F.op ⋙ Scheme.Spec
  let C := Scheme.Spec.mapCone c.op
  have hC : IsLimit C := isLimitOfPreserves Scheme.Spec hc.op
  have (j : Iᵒᵖ) : IsAffine (D.obj j) := inferInstanceAs (IsAffine (Spec (F.obj j.unop)))
  obtain ⟨j, N, hN, he⟩ := exists_model_on_baseChanges D C hC (.op i) f M
  exact ⟨j.left.unop, j.hom.unop, N, hN, he⟩

end AlgebraicGeometry.Scheme.Modules
