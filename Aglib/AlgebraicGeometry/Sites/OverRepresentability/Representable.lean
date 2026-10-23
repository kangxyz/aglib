/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.GlueData

/-!
# Zariski sheaves covered by representable open subfunctors are representable

Let `P` be a property of schemes over `S` that passes to open immersions and is local
(`IsOpenLocal`), and let `F` be a presheaf on `P.FullSubcategory`, with values in any universe,
satisfying the Zariski sheaf condition `IsZariskiSheaf F`. If `𝒰 : SubfunctorCover F` covers
`F` by open subfunctors `sub i` represented by `X i`, then `F` is represented by the object
`𝒰.glued` glued from the `X i` (`SubfunctorCover.representableByGlued`; Stacks, Tag 01JJ,
Lemma 26.15.4, stated there for functors on all schemes, here relative to `S`). The charts
`𝒰.ιp i : X i ⟶ 𝒰.glued` are open immersions covering `𝒰.glued` and correspond to the
universal elements of the `sub i` (`SubfunctorCover.representableByGlued_homEquiv_ιp`).

The proof follows Stacks: the universal elements glue by the sheaf condition (`univ`), and a
morphism `g : T ⟶ 𝒰.glued` pulls `univ` back into `sub i` exactly when `g` lands in the chart
`X i` (`map_univ_mem_iff`). This gives injectivity on Zariski-local factorizations through the
charts, and surjectivity by gluing the local morphisms given by the representations of the
`sub i`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme.LocalRepresentability

variable {S : Scheme.{u}} {P : ObjectProperty (Over S)} [IsOpenLocal P]

/-- An open subscheme of an object of `P.FullSubcategory`. -/
abbrev restrictOpens (T : P.FullSubcategory) (W : T.obj.left.Opens) : P.FullSubcategory :=
  ⟨overOpens T.obj W, IsOpenLocal.of_isOpenImmersion (overOpensι _ _) inferInstance T.property⟩

/-- The inclusion of an open subscheme, in `P.FullSubcategory`. -/
def restrictOpensι (T : P.FullSubcategory) (W : T.obj.left.Opens) : restrictOpens T W ⟶ T :=
  ObjectProperty.homMk (overOpensι _ _)

namespace SubfunctorCover

variable {F : P.FullSubcategoryᵒᵖ ⥤ Type v} (𝒰 : SubfunctorCover F)

lemma gluedOver_prop : P 𝒰.gluedOver :=
  IsOpenLocal.of_jointlySurjective (fun i => (𝒰.X i).obj) 𝒰.ιOver (fun _ => inferInstance)
    𝒰.ιOver_jointly_surjective (fun i => (𝒰.X i).property)

/-- The glued object of `P.FullSubcategory`. -/
abbrev glued : P.FullSubcategory :=
  ⟨𝒰.gluedOver, 𝒰.gluedOver_prop⟩

/-- The chart `X i ⟶ glued`, an open immersion. -/
def ιp (i : 𝒰.I) : 𝒰.X i ⟶ 𝒰.glued :=
  ObjectProperty.homMk (𝒰.ιOver i)

instance (i : 𝒰.I) : IsOpenImmersion (𝒰.ιp i).hom.left :=
  inferInstanceAs (IsOpenImmersion (𝒰.ιOver i).left)

lemma ιp_jointly_surjective (x : 𝒰.glued.obj.left) : ∃ i, x ∈ Set.range (𝒰.ιp i).hom.left :=
  𝒰.ιOver_jointly_surjective x

/-- Every morphism to the glued object factors through a chart on an open neighbourhood of any
point. -/
lemma exists_local_factor {Z : P.FullSubcategory} (h : Z ⟶ 𝒰.glued) (z : Z.obj.left) :
    ∃ (j : 𝒰.I) (W : Z.obj.left.Opens) (_ : z ∈ W) (c : (restrictOpens Z W).obj ⟶ (𝒰.X j).obj),
      (ObjectProperty.homMk c : restrictOpens Z W ⟶ 𝒰.X j) ≫ 𝒰.ιp j = restrictOpensι Z W ≫ h := by
  obtain ⟨j, hj⟩ := 𝒰.ιOver_jointly_surjective (h.hom.left z)
  let W : Z.obj.left.Opens := h.hom.left ⁻¹ᵁ (𝒰.ιOver j).left.opensRange
  have hW : Set.range (restrictOpensι Z W ≫ h).hom.left ⊆ Set.range (𝒰.ιOver j).left :=
    range_subset_range_of_preimage_opensRange_eq_top _ _ (by
      change (W.ι ≫ h.hom.left) ⁻¹ᵁ _ = ⊤
      rw [Scheme.Hom.comp_preimage]
      exact Scheme.Opens.ι_preimage_self W)
  exact ⟨j, W, hj, overLift (𝒰.ιOver j) (restrictOpensι Z W ≫ h).hom hW,
    ObjectProperty.hom_ext _ (overLift_comp _ _ hW)⟩

lemma isSheafFor_ιp (hF : IsZariskiSheaf F) : (Presieve.ofArrows 𝒰.X 𝒰.ιp).IsSheafFor F :=
  hF 𝒰.X 𝒰.ιp (fun _ => inferInstance) 𝒰.ιp_jointly_surjective

lemma compatible_ξ : Presieve.Arrows.Compatible F 𝒰.ιp 𝒰.ξ := by
  intro i j Z gi gj h
  obtain ⟨c, hc₁, hc₂⟩ :=
    𝒰.exists_of_comp_ιOver_eq i j gi.hom gj.hom (congrArg (fun g => g.hom) h)
  have e₁ : gi = ObjectProperty.homMk (c ≫ (𝒰.fp i j).hom) := ObjectProperty.hom_ext _ hc₁.symm
  have e₂ : gj = ObjectProperty.homMk (c ≫ (𝒰.tp i j).hom ≫ (𝒰.fp j i).hom) :=
    ObjectProperty.hom_ext _ hc₂.symm
  rw [e₁, e₂, 𝒰.map_homMk_tp_fp i j]

/-- The universal element over the glued object, glued from the universal elements of the
charts. -/
def univ (hF : IsZariskiSheaf F) : F.obj (op 𝒰.glued) :=
  ((Presieve.isSheafFor_arrows_iff F 𝒰.ιp).1 (𝒰.isSheafFor_ιp hF) 𝒰.ξ
    𝒰.compatible_ξ).exists.choose

lemma map_ιp_univ (hF : IsZariskiSheaf F) (i : 𝒰.I) :
    F.map (𝒰.ιp i).op (𝒰.univ hF) = 𝒰.ξ i :=
  ((Presieve.isSheafFor_arrows_iff F 𝒰.ιp).1 (𝒰.isSheafFor_ιp hF) 𝒰.ξ
    𝒰.compatible_ξ).exists.choose_spec i

lemma map_comp_ιp_univ (hF : IsZariskiSheaf F) (i : 𝒰.I) {Z : P.FullSubcategory}
    (a : Z ⟶ 𝒰.X i) : F.map (a ≫ 𝒰.ιp i).op (𝒰.univ hF) = F.map a.op (𝒰.ξ i) := by
  rw [map_comp_op_apply, map_ιp_univ]

lemma map_univ_mem_of_range_subset (hF : IsZariskiSheaf F) (i : 𝒰.I) {Z : P.FullSubcategory}
    (h : Z ⟶ 𝒰.glued) (hr : Set.range h.hom.left ⊆ Set.range (𝒰.ιOver i).left) :
    F.map h.op (𝒰.univ hF) ∈ (𝒰.sub i).obj (op Z) := by
  have e : h = ObjectProperty.homMk (overLift (𝒰.ιOver i) h.hom hr) ≫ 𝒰.ιp i :=
    ObjectProperty.hom_ext _ (overLift_comp _ _ hr).symm
  rw [e, map_comp_ιp_univ]
  exact 𝒰.map_ξ_mem i _

lemma range_subset_of_map_univ_mem (hF : IsZariskiSheaf F) (i : 𝒰.I) {Z : P.FullSubcategory}
    (h : Z ⟶ 𝒰.glued) (hmem : F.map h.op (𝒰.univ hF) ∈ (𝒰.sub i).obj (op Z)) :
    Set.range h.hom.left ⊆ Set.range (𝒰.ιOver i).left := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨j, W, hzW, c, hc⟩ := 𝒰.exists_local_factor h z
  have e : F.map (ObjectProperty.homMk c : restrictOpens Z W ⟶ 𝒰.X j).op (𝒰.ξ j) =
      F.map (restrictOpensι Z W).op (F.map h.op (𝒰.univ hF)) := by
    rw [← map_comp_ιp_univ 𝒰 hF, hc, map_comp_op_apply]
  have hmem' : F.map (ObjectProperty.homMk c : restrictOpens Z W ⟶ 𝒰.X j).op (𝒰.ξ j) ∈
      (𝒰.sub i).obj (op (restrictOpens Z W)) := by
    rw [e]
    exact (𝒰.sub i).map _ hmem
  have hV : c.left ⁻¹ᵁ 𝒰.V j i = ⊤ := (𝒰.map_ξ_mem_iff j i _).1 hmem'
  let c' : (restrictOpens Z W).obj ⟶ (𝒰.Vp j i).obj := overOpensLift c (𝒰.V j i) hV
  have hc' : c' ≫ (𝒰.fp j i).hom = c := overOpensLift_ι _ _ hV
  let c'' : (restrictOpens Z W).obj ⟶ (𝒰.X i).obj := c' ≫ (𝒰.tp j i).hom ≫ (𝒰.fp i j).hom
  have key : restrictOpensι Z W ≫ h = ObjectProperty.homMk c'' ≫ 𝒰.ιp i := by
    rw [← hc]
    apply ObjectProperty.hom_ext
    change c ≫ 𝒰.ιOver j = (c' ≫ (𝒰.tp j i).hom ≫ (𝒰.fp i j).hom) ≫ 𝒰.ιOver i
    rw [← hc']
    simp only [Category.assoc]
    rw [𝒰.glue_condition j i]
  have key' : W.ι ≫ h.hom.left = c''.left ≫ (𝒰.ιOver i).left :=
    congrArg (fun g => g.hom.left) key
  obtain ⟨w, rfl⟩ : z ∈ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact hzW
  have hpt := congrArg (fun f : W.toScheme ⟶ 𝒰.gluedScheme => f w) key'
  simp only [Scheme.Hom.comp_apply] at hpt
  exact ⟨c''.left w, hpt.symm⟩

/-- A morphism to the glued object pulls the universal element back into `sub i` if and only if
it lands in the chart `X i`. -/
lemma map_univ_mem_iff (hF : IsZariskiSheaf F) (i : 𝒰.I) {Z : P.FullSubcategory}
    (h : Z ⟶ 𝒰.glued) :
    F.map h.op (𝒰.univ hF) ∈ (𝒰.sub i).obj (op Z) ↔
      Set.range h.hom.left ⊆ Set.range (𝒰.ιOver i).left :=
  ⟨𝒰.range_subset_of_map_univ_mem hF i h, 𝒰.map_univ_mem_of_range_subset hF i h⟩

lemma map_univ_injective (hF : IsZariskiSheaf F) {T : P.FullSubcategory} {g g' : T ⟶ 𝒰.glued}
    (h : F.map g.op (𝒰.univ hF) = F.map g'.op (𝒰.univ hF)) : g = g' := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨j, W, hxW, c, hc⟩ := 𝒰.exists_local_factor g x
  refine ⟨W, hxW, ?_⟩
  have hmem : F.map (restrictOpensι T W ≫ g').op (𝒰.univ hF) ∈
      (𝒰.sub j).obj (op (restrictOpens T W)) := by
    rw [map_comp_op_apply, ← h, ← map_comp_op_apply, ← hc, map_comp_ιp_univ]
    exact 𝒰.map_ξ_mem j _
  have hr := 𝒰.range_subset_of_map_univ_mem hF j _ hmem
  let d := overLift (𝒰.ιOver j) (restrictOpensι T W ≫ g').hom hr
  have hd : (ObjectProperty.homMk d : restrictOpens T W ⟶ 𝒰.X j) ≫ 𝒰.ιp j =
      restrictOpensι T W ≫ g' :=
    ObjectProperty.hom_ext _ (overLift_comp _ _ hr)
  have hdc : (ObjectProperty.homMk d : restrictOpens T W ⟶ 𝒰.X j) = ObjectProperty.homMk c := by
    apply 𝒰.map_ξ_injective j
    rw [← map_comp_ιp_univ 𝒰 hF, ← map_comp_ιp_univ 𝒰 hF, hd, hc, map_comp_op_apply,
      map_comp_op_apply, h]
  have e : restrictOpensι T W ≫ g = restrictOpensι T W ≫ g' := by
    rw [← hc, ← hd, hdc]
  exact congrArg (fun f => f.hom.left) e

lemma map_univ_surjective (hF : IsZariskiSheaf F) {T : P.FullSubcategory} (η : F.obj (op T)) :
    ∃ g : T ⟶ 𝒰.glued, F.map g.op (𝒰.univ hF) = η := by
  have hloc : ∀ x : T.obj.left, ∃ (i : 𝒰.I) (W : T.obj.left.Opens), x ∈ W ∧
      F.map (restrictOpensι T W).op η ∈ (𝒰.sub i).obj (op (restrictOpens T W)) := by
    intro x
    obtain ⟨i, Z, g, ⟨z, hz⟩, hmem⟩ := 𝒰.covers η x
    obtain ⟨U, hU⟩ := 𝒰.isOpen i η
    refine ⟨i, U, ?_, (hU _).2 (Scheme.Opens.ι_preimage_self U)⟩
    have h₁ := (hU g).1 hmem
    have hzU : z ∈ g.hom.left ⁻¹ᵁ U := by
      rw [h₁]
      trivial
    rw [← hz]
    exact hzU
  choose i W hxW hmem using hloc
  obtain ⟨b, hb⟩ : ∃ b : ∀ x, restrictOpens T (W x) ⟶ 𝒰.glued,
      ∀ x, F.map (b x).op (𝒰.univ hF) = F.map (restrictOpensι T (W x)).op η := by
    refine ⟨fun x => (𝒰.representableBy (i x)).homEquiv.symm ⟨_, hmem x⟩ ≫ 𝒰.ιp (i x),
      fun x => ?_⟩
    rw [map_comp_ιp_univ, ← 𝒰.homEquiv_coe, Equiv.apply_symm_apply]
  let 𝒱 : T.obj.left.OpenCover :=
    { I₀ := T.obj.left
      X x := W x
      f x := (W x).ι
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        exact ⟨fun x => ⟨x, by simpa using hxW x⟩, inferInstance⟩ }
  have hcompat : ∀ x y, pullback.fst (𝒱.f x) (𝒱.f y) ≫ (b x).hom.left =
      pullback.snd (𝒱.f x) (𝒱.f y) ≫ (b y).hom.left := by
    intro x y
    let Ro : Over S := Over.mk (pullback.fst (W x).ι (W y).ι ≫ (W x).ι ≫ T.obj.hom)
    let j : Ro ⟶ T.obj := Over.homMk (pullback.fst (W x).ι (W y).ι ≫ (W x).ι)
    have hRo : P Ro := IsOpenLocal.of_isOpenImmersion j
      (inferInstanceAs (IsOpenImmersion (pullback.fst (W x).ι (W y).ι ≫ (W x).ι))) T.property
    let Rp : P.FullSubcategory := ⟨Ro, hRo⟩
    let p₁ : Rp ⟶ restrictOpens T (W x) :=
      ObjectProperty.homMk (Over.homMk (pullback.fst (W x).ι (W y).ι))
    let p₂ : Rp ⟶ restrictOpens T (W y) :=
      ObjectProperty.homMk (Over.homMk (pullback.snd (W x).ι (W y).ι) (by
        change pullback.snd (W x).ι (W y).ι ≫ (W y).ι ≫ T.obj.hom =
          pullback.fst (W x).ι (W y).ι ≫ (W x).ι ≫ T.obj.hom
        rw [pullback.condition_assoc]))
    have hp : p₁ ≫ restrictOpensι T (W x) = p₂ ≫ restrictOpensι T (W y) := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact pullback.condition
    have e : p₁ ≫ b x = p₂ ≫ b y := by
      apply 𝒰.map_univ_injective hF
      rw [map_comp_op_apply F p₁ (b x), map_comp_op_apply F p₂ (b y), hb x, hb y,
        ← map_comp_op_apply, ← map_comp_op_apply, hp]
    exact congrArg (fun f => f.hom.left) e
  let g₀ : T.obj.left ⟶ 𝒰.glued.obj.left := 𝒱.glueMorphisms (fun x => (b x).hom.left) hcompat
  have hg₀ : ∀ x, (W x).ι ≫ g₀ = (b x).hom.left := fun x =>
    𝒱.ι_glueMorphisms (fun x => (b x).hom.left) hcompat x
  have hw : g₀ ≫ 𝒰.glued.obj.hom = T.obj.hom := by
    refine 𝒱.hom_ext _ _ fun x => ?_
    change (W x).ι ≫ g₀ ≫ 𝒰.glued.obj.hom = (W x).ι ≫ T.obj.hom
    rw [← Category.assoc, hg₀]
    exact Over.w (b x).hom
  let g : T ⟶ 𝒰.glued := ObjectProperty.homMk (Over.homMk g₀ hw)
  have hgb : ∀ x, restrictOpensι T (W x) ≫ g = b x := fun x => by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hg₀ x
  refine ⟨g, ?_⟩
  have hsep := (hF (fun x => restrictOpens T (W x)) (fun x => restrictOpensι T (W x))
    (fun x => inferInstanceAs (IsOpenImmersion (W x).ι))
    (fun x => ⟨x, by
      change x ∈ Set.range (W x).ι
      rw [Scheme.Opens.range_ι]
      exact hxW x⟩)).isSeparatedFor
  apply hsep.ext
  rintro _ _ ⟨x⟩
  rw [← map_comp_op_apply, hgb, hb]

/-- **Stacks, Tag 01JJ** (Lemma 26.15.4), relative form: a Zariski sheaf on
`P.FullSubcategory` covered by representable open subfunctors is represented by the object glued
from the representing objects. -/
def representableByGlued (hF : IsZariskiSheaf F) : F.RepresentableBy 𝒰.glued where
  homEquiv := Equiv.ofBijective (fun g => F.map g.op (𝒰.univ hF))
    ⟨fun _ _ h => 𝒰.map_univ_injective hF h, fun η => 𝒰.map_univ_surjective hF η⟩
  homEquiv_comp f g := map_comp_op_apply F f g _

lemma representableByGlued_homEquiv_ιp (hF : IsZariskiSheaf F) (i : 𝒰.I) :
    (𝒰.representableByGlued hF).homEquiv (𝒰.ιp i) = 𝒰.ξ i :=
  𝒰.map_ιp_univ hF i

include 𝒰 in
/-- **Stacks, Tag 01JJ** (Lemma 26.15.4), relative form. -/
theorem isRepresentable (hF : IsZariskiSheaf F) : F.IsRepresentable :=
  (𝒰.representableByGlued hF).isRepresentable

end SubfunctorCover

end AlgebraicGeometry.Scheme.LocalRepresentability
