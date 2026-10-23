/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.Basic
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# The gluing data of a cover by representable open subfunctors

Let `𝒰` be a cover of a presheaf `F` on `P.FullSubcategory` by open subfunctors `sub i`
represented by `X i`, with universal elements `ξ i`. Following the proof of Stacks, Tag 01JJ
(Lemma 26.15.4), the representing scheme is glued from the `X i` along the opens
`V i j ⊆ X i` over which `ξ i` lies in `sub j`: the restriction of `ξ i` to `V i j` is represented
by a morphism `V i j ⟶ X j` over `S`, which factors through `V j i` (`tp`), and the cocycle
condition holds because morphisms into `X k` are determined by the elements of `F` they
represent.

The gluing data `glueData` lives in `Over S`; its image under `Over.forget S` is the gluing
data of schemes `schemeGlueData`. The glued scheme carries the structure morphism `gluedHom`
to `S`, and the charts `ιOver i : X i ⟶ gluedOver` are open immersions over `S` covering it, with
the pullback property `exists_of_comp_ιOver_eq` of the overlaps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover

variable {S : Scheme.{u}} {P : ObjectProperty (Over S)} [IsOpenLocal P]
  {F : P.FullSubcategoryᵒᵖ ⥤ Type v} (𝒰 : SubfunctorCover F)

/-- The open `V i j ⊆ X i`, as an object of `P.FullSubcategory`. -/
abbrev Vp (i j : 𝒰.I) : P.FullSubcategory :=
  ⟨overOpens (𝒰.X i).obj (𝒰.V i j),
    IsOpenLocal.of_isOpenImmersion (overOpensι _ _) inferInstance (𝒰.X i).property⟩

/-- The inclusion `V i j ⟶ X i`. -/
def fp (i j : 𝒰.I) : 𝒰.Vp i j ⟶ 𝒰.X i :=
  ObjectProperty.homMk (overOpensι _ _)

instance (i j : 𝒰.I) : IsOpenImmersion (𝒰.fp i j).hom.left :=
  inferInstanceAs (IsOpenImmersion (𝒰.V i j).ι)

instance (i j : 𝒰.I) : Mono (𝒰.fp i j).hom :=
  (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono (𝒰.V i j).ι))

instance (i j : 𝒰.I) : Mono (𝒰.fp i j) :=
  P.ι.mono_of_mono_map (inferInstanceAs (Mono (𝒰.fp i j).hom))

instance (i : 𝒰.I) : IsIso (𝒰.fp i i).hom := by
  have h₁ : IsIso ((𝒰.X i).obj.left.isoOfEq (𝒰.V_self i)).hom := inferInstance
  have h₂ : IsIso (⊤ : (𝒰.X i).obj.left.Opens).ι :=
    inferInstanceAs (IsIso (Scheme.topIso (𝒰.X i).obj.left).hom)
  have : IsIso (𝒰.V i i).ι := by
    rw [← Scheme.isoOfEq_hom_ι _ (𝒰.V_self i)]
    infer_instance
  have : IsIso ((Over.forget S).map (𝒰.fp i i).hom) := this
  exact isIso_of_reflects_iso _ (Over.forget S)

lemma fp_w (i j : 𝒰.I) : (𝒰.fp i j).hom.left ≫ (𝒰.X i).obj.hom = (𝒰.Vp i j).obj.hom :=
  Over.w (𝒰.fp i j).hom

lemma map_fp_ξ_mem (i j : 𝒰.I) :
    F.map (𝒰.fp i j).op (𝒰.ξ i) ∈ (𝒰.sub j).obj (op (𝒰.Vp i j)) :=
  (𝒰.map_ξ_mem_iff i j (𝒰.fp i j)).2 (Scheme.Opens.ι_preimage_self _)

/-- The morphism `V i j ⟶ X j` representing the restriction of `ξ i`, which lies in `sub j`. -/
def φ (i j : 𝒰.I) : 𝒰.Vp i j ⟶ 𝒰.X j :=
  (𝒰.representableBy j).homEquiv.symm ⟨_, 𝒰.map_fp_ξ_mem i j⟩

lemma map_φ_ξ (i j : 𝒰.I) : F.map (𝒰.φ i j).op (𝒰.ξ j) = F.map (𝒰.fp i j).op (𝒰.ξ i) := by
  rw [← 𝒰.homEquiv_coe, φ, Equiv.apply_symm_apply]

lemma φ_preimage (i j : 𝒰.I) : (𝒰.φ i j).hom.left ⁻¹ᵁ 𝒰.V j i = ⊤ := by
  rw [← 𝒰.map_ξ_mem_iff j i, map_φ_ξ]
  exact (𝒰.sub i).map _ (𝒰.ξ_mem i)

/-- The transition morphism `V i j ⟶ V j i`. -/
def tp (i j : 𝒰.I) : 𝒰.Vp i j ⟶ 𝒰.Vp j i :=
  ObjectProperty.homMk (overOpensLift (𝒰.φ i j).hom (𝒰.V j i) (𝒰.φ_preimage i j))

@[reassoc]
lemma tp_fp (i j : 𝒰.I) : 𝒰.tp i j ≫ 𝒰.fp j i = 𝒰.φ i j :=
  ObjectProperty.hom_ext _ (overOpensLift_ι _ _ (𝒰.φ_preimage i j))

lemma tp_fp_w (i j : 𝒰.I) :
    (𝒰.tp i j).hom.left ≫ (𝒰.fp j i).hom.left ≫ (𝒰.X j).obj.hom = (𝒰.Vp i j).obj.hom := by
  rw [Over.w (𝒰.fp j i).hom, Over.w (𝒰.tp i j).hom]

lemma map_tp_fp_ξ (i j : 𝒰.I) :
    F.map (𝒰.tp i j ≫ 𝒰.fp j i).op (𝒰.ξ j) = F.map (𝒰.fp i j).op (𝒰.ξ i) := by
  rw [tp_fp, map_φ_ξ]

/-- Transport of the universal elements along the transition morphisms. -/
lemma map_homMk_tp_fp (a b : 𝒰.I) {W : P.FullSubcategory} (A : W.obj ⟶ (𝒰.Vp a b).obj) :
    F.map (ObjectProperty.homMk (A ≫ (𝒰.tp a b).hom ≫ (𝒰.fp b a).hom) : W ⟶ 𝒰.X b).op
        (𝒰.ξ b) =
      F.map (ObjectProperty.homMk (A ≫ (𝒰.fp a b).hom) : W ⟶ 𝒰.X a).op (𝒰.ξ a) := by
  have e₁ : (ObjectProperty.homMk (A ≫ (𝒰.tp a b).hom ≫ (𝒰.fp b a).hom) : W ⟶ 𝒰.X b) =
      ObjectProperty.homMk A ≫ 𝒰.tp a b ≫ 𝒰.fp b a := rfl
  have e₂ : (ObjectProperty.homMk (A ≫ (𝒰.fp a b).hom) : W ⟶ 𝒰.X a) =
      ObjectProperty.homMk A ≫ 𝒰.fp a b := rfl
  rw [e₁, e₂, map_comp_op_apply F (ObjectProperty.homMk A) (𝒰.tp a b ≫ 𝒰.fp b a),
    map_comp_op_apply F (ObjectProperty.homMk A) (𝒰.fp a b), map_tp_fp_ξ]

lemma φ_self (i : 𝒰.I) : 𝒰.φ i i = 𝒰.fp i i :=
  𝒰.map_ξ_injective i (𝒰.map_φ_ξ i i)

lemma tp_self (i : 𝒰.I) : 𝒰.tp i i = 𝟙 _ := by
  rw [← cancel_mono (𝒰.fp i i), tp_fp, φ_self, Category.id_comp]

/-- The double overlap `V i j ×_{X i} V i k`, a scheme over `S`. -/
abbrev Q (i j k : 𝒰.I) : Over S :=
  pullback (𝒰.fp i j).hom (𝒰.fp i k).hom

lemma Q_prop (i j k : 𝒰.I) : P (𝒰.Q i j k) :=
  IsOpenLocal.of_isOpenImmersion (pullback.fst _ _)
    (isOpenImmersion_pullback_fst_left _ _ inferInstance) (𝒰.Vp i j).property

/-- The double overlap as an object of `P.FullSubcategory`. -/
abbrev Qp (i j k : 𝒰.I) : P.FullSubcategory :=
  ⟨𝒰.Q i j k, 𝒰.Q_prop i j k⟩

lemma q_preimage (i j k : 𝒰.I) :
    (pullback.fst (𝒰.fp i j).hom (𝒰.fp i k).hom ≫ (𝒰.tp i j).hom ≫ (𝒰.fp j i).hom).left ⁻¹ᵁ
      𝒰.V j k = ⊤ := by
  let fst : 𝒰.Qp i j k ⟶ 𝒰.Vp i j := ObjectProperty.homMk (pullback.fst _ _)
  let snd : 𝒰.Qp i j k ⟶ 𝒰.Vp i k := ObjectProperty.homMk (pullback.snd _ _)
  have hc : fst ≫ 𝒰.fp i j = snd ≫ 𝒰.fp i k := ObjectProperty.hom_ext _ pullback.condition
  refine (𝒰.map_ξ_mem_iff j k (fst ≫ 𝒰.tp i j ≫ 𝒰.fp j i)).1 ?_
  rw [map_comp_op_apply, map_tp_fp_ξ, ← map_comp_op_apply, hc, map_comp_op_apply]
  exact (𝒰.sub k).map _ (𝒰.map_fp_ξ_mem i k)

/-- The lift of `V i j ×_{X i} V i k ⟶ V j i ⟶ X j` through `V j k`. -/
def q (i j k : 𝒰.I) : 𝒰.Q i j k ⟶ (𝒰.Vp j k).obj :=
  overOpensLift (pullback.fst _ _ ≫ (𝒰.tp i j).hom ≫ (𝒰.fp j i).hom) (𝒰.V j k)
    (𝒰.q_preimage i j k)

@[reassoc]
lemma q_fp (i j k : 𝒰.I) :
    𝒰.q i j k ≫ (𝒰.fp j k).hom = pullback.fst _ _ ≫ (𝒰.tp i j).hom ≫ (𝒰.fp j i).hom :=
  overOpensLift_ι _ _ (𝒰.q_preimage i j k)

/-- The cocycle morphism of the gluing data. -/
def t' (i j k : 𝒰.I) :
    pullback (𝒰.fp i j).hom (𝒰.fp i k).hom ⟶ pullback (𝒰.fp j k).hom (𝒰.fp j i).hom :=
  pullback.lift (𝒰.q i j k) (pullback.fst _ _ ≫ (𝒰.tp i j).hom) (by rw [q_fp, Category.assoc])

@[reassoc]
lemma t'_fst (i j k : 𝒰.I) : 𝒰.t' i j k ≫ pullback.fst _ _ = 𝒰.q i j k :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma t'_snd (i j k : 𝒰.I) :
    𝒰.t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ (𝒰.tp i j).hom :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma t'_fst_fp (i j k : 𝒰.I) :
    𝒰.t' i j k ≫ pullback.fst _ _ ≫ (𝒰.fp j k).hom =
      pullback.fst _ _ ≫ (𝒰.tp i j).hom ≫ (𝒰.fp j i).hom := by
  rw [t'_fst_assoc, q_fp]

lemma cocycle_fst (i j k : 𝒰.I) :
    (𝒰.t' i j k ≫ 𝒰.t' j k i ≫ 𝒰.t' k i j) ≫ pullback.fst _ _ ≫ (𝒰.fp i j).hom =
      pullback.fst _ _ ≫ (𝒰.fp i j).hom := by
  have m₁ : (𝒰.t' i j k ≫ 𝒰.t' j k i ≫ 𝒰.t' k i j) ≫ pullback.fst _ _ ≫ (𝒰.fp i j).hom =
      (𝒰.t' i j k ≫ 𝒰.t' j k i ≫ pullback.fst _ _) ≫ (𝒰.tp k i).hom ≫ (𝒰.fp i k).hom := by
    simp only [Category.assoc, t'_fst_fp]
  have m₂ : (𝒰.t' i j k ≫ 𝒰.t' j k i ≫ pullback.fst _ _) ≫ (𝒰.fp k i).hom =
      (𝒰.t' i j k ≫ pullback.fst _ _) ≫ (𝒰.tp j k).hom ≫ (𝒰.fp k j).hom := by
    simp only [Category.assoc, t'_fst_fp]
  have m₃ : (𝒰.t' i j k ≫ pullback.fst _ _) ≫ (𝒰.fp j k).hom =
      pullback.fst _ _ ≫ (𝒰.tp i j).hom ≫ (𝒰.fp j i).hom := by
    simp only [Category.assoc, t'_fst_fp]
  have key : ∀ a b : 𝒰.Q i j k ⟶ (𝒰.X i).obj,
      F.map (ObjectProperty.homMk a : 𝒰.Qp i j k ⟶ 𝒰.X i).op (𝒰.ξ i) =
        F.map (ObjectProperty.homMk b : 𝒰.Qp i j k ⟶ 𝒰.X i).op (𝒰.ξ i) → a = b :=
    fun a b h => congrArg (fun g => g.hom) (𝒰.map_ξ_injective i h)
  apply key
  rw [m₁, 𝒰.map_homMk_tp_fp k i, m₂, 𝒰.map_homMk_tp_fp j k, m₃, 𝒰.map_homMk_tp_fp i j]

lemma cocycle (i j k : 𝒰.I) : 𝒰.t' i j k ≫ 𝒰.t' j k i ≫ 𝒰.t' k i j = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.id_comp, ← cancel_mono (𝒰.fp i j).hom]
    simpa only [Category.assoc] using 𝒰.cocycle_fst i j k
  · rw [Category.id_comp, ← cancel_mono (𝒰.fp i k).hom]
    simp only [Category.assoc]
    rw [← pullback.condition]
    simpa only [Category.assoc] using 𝒰.cocycle_fst i j k

/-- The gluing data in `Over S` of the representing objects along the opens `V i j`. -/
def glueData : CategoryTheory.GlueData (Over S) where
  J := 𝒰.I
  U i := (𝒰.X i).obj
  V p := (𝒰.Vp p.1 p.2).obj
  f i j := (𝒰.fp i j).hom
  f_id _ := inferInstance
  t i j := (𝒰.tp i j).hom
  t_id i := by rw [𝒰.tp_self]; rfl
  t' := 𝒰.t'
  t_fac := 𝒰.t'_snd
  cocycle := 𝒰.cocycle

/-- The gluing data of schemes underlying `𝒰.glueData`: the image of `𝒰.glueData` under
`Over.forget S`, with the index type, charts and overlaps stated literally. -/
def schemeGlueData : Scheme.GlueData.{u} where
  J := 𝒰.I
  U i := (𝒰.X i).obj.left
  V p := (𝒰.Vp p.1 p.2).obj.left
  f i j := (𝒰.fp i j).hom.left
  f_id i := inferInstanceAs (IsIso ((Over.forget S).map (𝒰.fp i i).hom))
  t i j := (𝒰.tp i j).hom.left
  t_id i := by rw [𝒰.tp_self]; rfl
  t' := (𝒰.glueData.mapGlueData (Over.forget S)).t'
  t_fac := (𝒰.glueData.mapGlueData (Over.forget S)).t_fac
  cocycle := (𝒰.glueData.mapGlueData (Over.forget S)).cocycle
  f_open i j := inferInstanceAs (IsOpenImmersion (𝒰.V i j).ι)

/-- The glued scheme. -/
abbrev gluedScheme : Scheme.{u} :=
  𝒰.schemeGlueData.glued

lemma gluedHom_aux (i j : 𝒰.I) :
    (𝒰.fp i j).hom.left ≫ (𝒰.X i).obj.hom =
      ((𝒰.tp i j).hom.left ≫ (𝒰.fp j i).hom.left) ≫ (𝒰.X j).obj.hom := by
  rw [fp_w, Category.assoc, tp_fp_w]

/-- The structure morphism of the glued scheme. -/
def gluedHom : 𝒰.gluedScheme ⟶ S :=
  Multicoequalizer.desc _ _ (fun i => (𝒰.X i).obj.hom) (fun ⟨i, j⟩ => 𝒰.gluedHom_aux i j)

@[reassoc (attr := simp)]
lemma ι_gluedHom (i : 𝒰.I) : 𝒰.schemeGlueData.ι i ≫ 𝒰.gluedHom = (𝒰.X i).obj.hom := by
  rw [gluedHom]
  exact Multicoequalizer.π_desc _ _ _ _ _

/-- The glued scheme, over `S`. -/
abbrev gluedOver : Over S :=
  Over.mk 𝒰.gluedHom

/-- The chart `X i ⟶ glued`, an open immersion over `S`. -/
def ιOver (i : 𝒰.I) : (𝒰.X i).obj ⟶ 𝒰.gluedOver :=
  Over.homMk (𝒰.schemeGlueData.ι i) (𝒰.ι_gluedHom i)

instance isOpenImmersion_ιOver (i : 𝒰.I) : IsOpenImmersion (𝒰.ιOver i).left :=
  𝒰.schemeGlueData.ι_isOpenImmersion i

lemma ιOver_jointly_surjective (x : 𝒰.gluedOver.left) :
    ∃ i, x ∈ Set.range (𝒰.ιOver i).left :=
  let ⟨i, y, hy⟩ := 𝒰.schemeGlueData.ι_jointly_surjective x
  ⟨i, y, hy⟩

@[reassoc]
lemma glue_condition (i j : 𝒰.I) :
    (𝒰.tp i j).hom ≫ (𝒰.fp j i).hom ≫ 𝒰.ιOver j = (𝒰.fp i j).hom ≫ 𝒰.ιOver i := by
  ext
  exact 𝒰.schemeGlueData.glue_condition i j

/-- The overlap of two charts is `V i j`: morphisms over `S` agreeing in the glued scheme
factor through `V i j`. -/
lemma exists_of_comp_ιOver_eq (i j : 𝒰.I) {Z : Over S} (a : Z ⟶ (𝒰.X i).obj)
    (b : Z ⟶ (𝒰.X j).obj) (h : a ≫ 𝒰.ιOver i = b ≫ 𝒰.ιOver j) :
    ∃ c : Z ⟶ (𝒰.Vp i j).obj, c ≫ (𝒰.fp i j).hom = a ∧
      c ≫ (𝒰.tp i j).hom ≫ (𝒰.fp j i).hom = b := by
  have hl : a.left ≫ 𝒰.schemeGlueData.ι i = b.left ≫ 𝒰.schemeGlueData.ι j := by
    have h' := congrArg (fun g => g.left) h
    simp only [Over.comp_left] at h'
    exact h'
  obtain ⟨c, hc₁, hc₂⟩ :=
    PullbackCone.IsLimit.lift' (𝒰.schemeGlueData.vPullbackConeIsLimit i j) a.left b.left hl
  let c' : Z.left ⟶ (𝒰.Vp i j).obj.left := c
  have hc₁' : c' ≫ (𝒰.fp i j).hom.left = a.left := hc₁
  have hc₂' : c' ≫ (𝒰.tp i j).hom.left ≫ (𝒰.fp j i).hom.left = b.left := hc₂
  have hw : c' ≫ (𝒰.Vp i j).obj.hom = Z.hom := by
    rw [← 𝒰.fp_w, ← Category.assoc, hc₁', Over.w a]
  refine ⟨Over.homMk c' hw, ?_, ?_⟩
  · ext
    exact hc₁'
  · ext
    simpa using hc₂'

end AlgebraicGeometry.Scheme.LocalRepresentability.SubfunctorCover
