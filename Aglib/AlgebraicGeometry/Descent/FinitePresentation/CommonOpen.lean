/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes

/-! # Descending an original common open to one stage

The original common open is modeled on both sides using the existing native
finite-presentation models. Its identity descends and becomes an isomorphism
at a later stage. Native pullback pasting then identifies the iterated base
changes with the single actual composite stage. Both original comparison
maps are retained, without a new chart or model structure.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FinitePresentationDescent.Model

universe u

/-- The whole native double base change represents the identity on the
original object and is isomorphic to the actual composite base change. -/
theorem exists_rebase_rebase_iso
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    {Z : Scheme.{u}} {t : Z ⟶ c.pt} (M : Model (c.π.app i) t)
    (j : Over i) (k : Over j.left) :
    ∃ a : Map ((M.rebase D c i j).rebase D c j.left k)
      (M.rebase D c i (Over.mk (k.hom ≫ j.hom))) (𝟙 (Over.mk t)),
      IsIso a.hom.left := by
  let e : pullback (pullback.snd M.f (D.map j.hom)) (D.map k.hom) ≅
      pullback M.f (D.map (k.hom ≫ j.hom)) :=
    pullbackLeftPullbackSndIso M.f (D.map j.hom) (D.map k.hom) ≪≫
      pullback.congrHom rfl (D.map_comp k.hom j.hom).symm
  have he₁ : e.hom ≫ pullback.fst M.f (D.map (k.hom ≫ j.hom)) =
      pullback.fst (pullback.snd M.f (D.map j.hom)) (D.map k.hom) ≫
        pullback.fst M.f (D.map j.hom) := by
    simp only [e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
      pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  have he₂ : e.hom ≫ pullback.snd M.f (D.map (k.hom ≫ j.hom)) =
      pullback.snd (pullback.snd M.f (D.map j.hom)) (D.map k.hom) := by
    simp only [e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
      pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  let a : Map ((M.rebase D c i j).rebase D c j.left k)
      (M.rebase D c i (Over.mk (k.hom ≫ j.hom))) (𝟙 (Over.mk t)) := {
    hom := Over.homMk e.hom he₂
    comm := by
      change ((M.rebase D c i j).rebase D c j.left k).p ≫ e.hom =
        (𝟙 Z) ≫ (M.rebase D c i (Over.mk (k.hom ≫ j.hom))).p
      rw [Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, he₁, ← Category.assoc]
        have h₁ : ((M.rebase D c i j).rebase D c j.left k).p ≫
            pullback.fst (pullback.snd M.f (D.map j.hom)) (D.map k.hom) =
              (M.rebase D c i j).p := rebase_p_fst D c j.left (M.rebase D c i j) k
        have h₂ : (M.rebase D c i j).p ≫ pullback.fst M.f (D.map j.hom) = M.p :=
          rebase_p_fst D c i M j
        have h₃ : (M.rebase D c i (Over.mk (k.hom ≫ j.hom))).p ≫
            pullback.fst M.f (D.map (k.hom ≫ j.hom)) = M.p :=
          rebase_p_fst D c i M (Over.mk (k.hom ≫ j.hom))
        exact (congrArg (fun q : Z ⟶ pullback M.f (D.map j.hom) =>
          q ≫ pullback.fst M.f (D.map j.hom)) h₁).trans (h₂.trans h₃.symm)
      · rw [Category.assoc, he₂]
        have h₁ : ((M.rebase D c i j).rebase D c j.left k).p ≫
            pullback.snd (pullback.snd M.f (D.map j.hom)) (D.map k.hom) =
              t ≫ c.π.app k.left := rebase_p_snd D c j.left (M.rebase D c i j) k
        have h₂ : (M.rebase D c i (Over.mk (k.hom ≫ j.hom))).p ≫
            pullback.snd M.f (D.map (k.hom ≫ j.hom)) = t ≫ c.π.app k.left :=
          rebase_p_snd D c i M (Over.mk (k.hom ≫ j.hom))
        exact h₁.trans h₂.symm }
  exact ⟨a, inferInstanceAs (IsIso e.hom)⟩

/-- Two original open immersions from the same quasi-compact scheme descend
to open immersions from one model at one later stage. The output maps retain
their original comparisons to both specified objects. -/
theorem exists_common_open_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (Z : Bool → Scheme.{u}) (t : ∀ b, Z b ⟶ c.pt)
    (M : ∀ b, Model (c.π.app i) (t b))
    {W : Scheme.{u}} [CompactSpace W] (w : W ⟶ c.pt)
    (m : ∀ b, Over.mk w ⟶ Over.mk (t b))
    [∀ b, IsOpenImmersion (m b).left] :
    ∃ k : Over i, ∃ N : Model (c.π.app k.left) w,
      ∀ b, ∃ a : Map N ((M b).rebase D c i k) (m b), IsOpenImmersion a.hom.left := by
  classical
  obtain ⟨k, hk⟩ := exists_common_open_submodels D c hc i t (fun _ : Bool => w) M m
  choose N A hA using hk
  obtain ⟨j, ⟨a⟩⟩ := exists_map D c hc k.left (N false) (N true) (𝟙 (Over.mk w))
  have : IsIso ((Over.pullback (c.π.app j.left)).map a.hom) := a.isIso_baseChange
  obtain ⟨l, hl⟩ := Scheme.exists_isIso_baseChange_map_of_isLimit D c hc j.left
    ((N false).rebase D c k.left j).f ((N true).rebase D c k.left j).f a.hom
  let M' (b : Bool) := (((M b).rebase D c i k).rebase D c k.left j).rebase D c j.left l
  let N' (b : Bool) := ((N b).rebase D c k.left j).rebase D c j.left l
  let A' (b : Bool) : Map (N' b) (M' b) (m b) :=
    ((A b).rebase D c k.left j).rebase D c j.left l
  let a' : Map (N' false) (N' true) (𝟙 (Over.mk w)) := a.rebase D c j.left l
  have : IsIso a'.hom := hl
  have : IsIso a'.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (D.obj l.left)).map a'.hom))
  have hA' (b : Bool) : IsOpenImmersion (A' b).hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) (D.map l.hom) _
      (MorphismProperty.overPullbackMap (P := @IsOpenImmersion) (D.map j.hom) _ (hA b))
  let B : ∀ b, Map (N' false) (M' b) (m b) :=
    Bool.rec (A' false) (by simpa only [Category.id_comp] using a'.comp (A' true))
  have hB (b : Bool) : IsOpenImmersion (B b).hom.left := by
    cases b
    · exact hA' false
    · change IsOpenImmersion (a'.hom.left ≫ (A' true).hom.left)
      have := hA' true
      infer_instance
  let kj : Over k.left := Over.mk (l.hom ≫ j.hom)
  let final : Over i := Over.mk ((l.hom ≫ j.hom) ≫ k.hom)
  refine ⟨final, N' false, fun b => ?_⟩
  obtain ⟨r, hr⟩ := exists_rebase_rebase_iso D c k.left ((M b).rebase D c i k) j l
  obtain ⟨s, hs⟩ := exists_rebase_rebase_iso D c i (M b) k kj
  let q : Map (M' b) ((M b).rebase D c i final) (𝟙 (Over.mk (t b))) := {
    hom := r.hom ≫ s.hom
    comm := by
      simpa only [Map.comp, M', final, kj, Over.mk_hom, Category.comp_id] using (r.comp s).comm }
  have : IsIso r.hom.left := hr
  have : IsIso s.hom.left := hs
  have hq : IsOpenImmersion q.hom.left := by
    change IsOpenImmersion (r.hom.left ≫ s.hom.left)
    infer_instance
  let result : Map (N' false) ((M b).rebase D c i final) (m b) := {
    hom := (B b).hom ≫ q.hom
    comm := by simpa only [Map.comp, Category.comp_id] using ((B b).comp q).comm }
  refine ⟨result, ?_⟩
  change IsOpenImmersion ((B b).hom.left ≫ q.hom.left)
  have := hB b
  have := hq
  infer_instance

end AlgebraicGeometry.Scheme.FinitePresentationDescent.Model
