/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ProperSubalgebraModel
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ClosedModelMaps
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Model

/-! # Common actual models for the original pointed field branches

All branch maps, sections and specified projective embeddings descend in one
finite diagram of actual models. Subsequent common refinements preserve the
same arrows and make the original embeddings closed and point branches
isomorphisms. No cover or geometric model is replaced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open Algebra.FiniteTypeSubalgebraLimit
open AlgebraicGeometry.Scheme.FinitePresentationDescent

namespace AlgebraicGeometry.Scheme.OverField.Curve.Normalization.GenericCover

universe u

variable (R L : Type u) [CommRing R] [IsNoetherianRing R] [Field L] [Algebra R L]

/-- The original stage inclusion into the same ambient field. -/
abbrev inclusion (s : Finset L) :=
  Spec.map (CommRingCat.ofHom (stage R L s).val.toRingHom)

/-- The original structural map of a coefficient stage. -/
abbrev stageStructure (s : Finset L) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (stage R L s)))

/-- The original change of base to the same ambient field. -/
abbrev fieldMap := Spec.map (CommRingCat.ofHom (algebraMap R L))

omit [IsNoetherianRing R] in
private theorem inclusion_structure (s : Finset L) :
    inclusion R L s ≫ stageStructure R L s = fieldMap R L := by
  rw [← Spec.map_comp]
  rfl

omit [IsNoetherianRing R] in
private theorem stage_structure {s t : Finset L} (q : s ⟶ t) :
    Spec.map ((ringDiagram R L).map q) ≫ stageStructure R L s =
      stageStructure R L t := by
  dsimp only [ringDiagram, subalgebraDiagram, stageStructure]
  rw [← Spec.map_comp]
  rfl

private def baseModel (s : Finset L) : Model (inclusion R L s) (𝟙 (Spec (.of L))) where
  X := Spec (.of (stage R L s))
  f := 𝟙 _
  locallyOfFinitePresentation := inferInstance
  quasiCompact := inferInstance
  quasiSeparated := inferInstance
  p := inclusion R L s
  square := IsPullback.of_id_snd

private def targetModel {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    (s : Finset L) : Model (inclusion R L s) (pullback.snd p (fieldMap R L)) := by
  let H : IsPullback (pullback.fst p (fieldMap R L))
      (pullback.snd p (fieldMap R L)) p
      (inclusion R L s ≫ stageStructure R L s) := by
    rw [inclusion_structure]
    exact IsPullback.of_hasPullback p (fieldMap R L)
  let Q := IsPullback.of_hasPullback p (stageStructure R L s)
  exact {
    X := pullback p (stageStructure R L s)
    f := pullback.snd p (stageStructure R L s)
    locallyOfFinitePresentation := inferInstance
    quasiCompact := inferInstance
    quasiSeparated := inferInstance
    p := Q.lift (pullback.fst p (fieldMap R L))
      (pullback.snd p (fieldMap R L) ≫ inclusion R L s) (by
        simpa only [Category.assoc] using H.w)
    square := H.of_right' Q }

/-- Actual models at one common coefficient stage retain every original
branch arrow and section. The target has its actual cartesian comparison
with the original `X`; the projective targets are the original standard
projective spaces over that stage. Finiteness of branch arrows is deliberately
not assumed here: it is used later by the generic-arrow construction. -/
theorem exists_common_models
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    {I : Type u} [Finite I] (C : I → Scheme.{u})
    (q : ∀ i, C i ⟶ Spec (.of L)) [∀ i, IsProper (q i)]
    (ν : ∀ i, C i ⟶ pullback p (fieldMap R L))
    (hν : ∀ i, ν i ≫ pullback.snd p (fieldMap R L) = q i)
    (σ : ∀ i, Spec (.of L) ⟶ C i) (hσ : ∀ i, σ i ≫ q i = 𝟙 _)
    (P : Set I) (hpoint : ∀ i : P, IsIso (q i))
    (n : {i : I // i ∉ P} → ℕ)
    (e : ∀ i : {i : I // i ∉ P}, C i ⟶ ProjectiveSpace L (ULift.{u} (Fin (n i + 1))))
    [∀ i, IsClosedImmersion (e i)]
    (he : ∀ i, e i ≫ ProjectiveSpace.toSpec L (ULift.{u} (Fin (n i + 1))) = q i) :
    ∃ a : Finset L,
      ∃ N : Model (inclusion R L a) (pullback.snd p (fieldMap R L)),
      ∃ M : ∀ i, Model (inclusion R L a) (q i),
        IsProper N.f ∧ (∀ i, IsProper (M i).f) ∧
        (∃ r : N.X ⟶ X, IsPullback r N.f p (stageStructure R L a) ∧
          N.p ≫ r = pullback.fst p (fieldMap R L)) ∧
        (∀ i, Nonempty (Model.Map (M i) N (Over.homMk (ν i) (hν i)))) ∧
        (∃ σa : ∀ i, Spec (.of (stage R L a)) ⟶ (M i).X,
          (∀ i, σa i ≫ (M i).f = 𝟙 _) ∧
          ∀ i, inclusion R L a ≫ σa i = σ i ≫ (M i).p) ∧
        (∀ i : P, IsIso (M i).f) ∧
        ∀ i : {i : I // i ∉ P},
          ∃ ea : (M i).X ⟶ ProjectiveSpace (stage R L a) (ULift.{u} (Fin (n i + 1))),
            IsClosedImmersion ea ∧
            ea ≫ ProjectiveSpace.toSpec (stage R L a) (ULift.{u} (Fin (n i + 1))) = (M i).f ∧
            (M i).p ≫ ea = e i ≫
              ProjectiveSpace.map (stage R L a).val.toRingHom (ULift.{u} (Fin (n i + 1))) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let J := {i : I // i ∉ P}
  let K := {i : I // i ∈ P}
  choose s₀ M₀ hM₀ using fun i =>
    Scheme.FiniteTypeSubalgebraLimit.exists_properModel_over_finiteTypeSubalgebra R L (q i)
  let F := ringDiagram R L
  let D : (Finset L)ᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (ringCocone R L).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit R L).op
  have (a : (Finset L)ᵒᵖ) : CompactSpace (D.obj a) :=
    inferInstanceAs (CompactSpace (Spec (.of (stage R L a.unop))))
  have (a : (Finset L)ᵒᵖ) : QuasiSeparatedSpace (D.obj a) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of (stage R L a.unop))))
  have (a : (Finset L)ᵒᵖ) : IsAffine (D.obj a) :=
    inferInstanceAs (IsAffine (Spec (.of (stage R L a.unop))))
  have {a b : (Finset L)ᵒᵖ} (f : a ⟶ b) : IsAffineHom (D.map f) := inferInstance
  let s : Finset L := Finset.univ.biUnion s₀
  have hsub (i : I) : s₀ i ⊆ s := Finset.subset_biUnion_of_mem s₀ (Finset.mem_univ i)
  let Ms (i : I) : Model (c.π.app (op s)) (q i) :=
    (M₀ i).rebase D c (op (s₀ i)) (Over.mk (homOfLE (hsub i)).op)
  have hMs (i : I) : IsProper (Ms i).f :=
    IsProper.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (M₀ i).f (D.map (homOfLE (hsub i)).op)) (hM₀ i)
  let O := (Bool ⊕ I) ⊕ J
  let Z : O → Scheme.{u} := Sum.elim
    (Sum.elim (Bool.rec (Spec (.of L)) (pullback p (fieldMap R L))) C)
    (fun i => ProjectiveSpace L (ULift.{u} (Fin (n i + 1))))
  let t : ∀ o : O, Z o ⟶ Spec (.of L) := fun o => by
    rcases o with (b | i) | i
    · cases b
      · exact 𝟙 _
      · exact pullback.snd p (fieldMap R L)
    · exact q i
    · exact ProjectiveSpace.toSpec L (ULift.{u} (Fin (n i + 1)))
  let M : ∀ o : O, Model (c.π.app (op s)) (t o) := fun o => by
    rcases o with (b | i) | i
    · cases b
      · exact baseModel R L s
      · exact targetModel R L p s
    · exact Ms i
    · exact ProjectiveSpace.model (stage R L s).val.toRingHom (ULift.{u} (Fin (n i + 1)))
  let obase : O := .inl (.inl false)
  let otarget : O := .inl (.inl true)
  let obranch (i : I) : O := .inl (.inr i)
  let oprojective (i : J) : O := .inr i
  let A := I ⊕ (I ⊕ (J ⊕ K))
  let src : A → O := Sum.elim obranch
    (Sum.elim (fun _ => obase) (Sum.elim (fun i => obranch i) (fun i => obranch i)))
  let dst : A → O := Sum.elim (fun _ => otarget)
    (Sum.elim obranch (Sum.elim oprojective (fun _ => obase)))
  let m : ∀ a : A, Over.mk (t (src a)) ⟶ Over.mk (t (dst a)) := fun a => by
    rcases a with i | i | i | i
    · exact Over.homMk (ν i) (hν i)
    · exact Over.homMk (σ i) (hσ i)
    · exact Over.homMk (e i) (he i)
    · exact Over.homMk (q i) (by
        change q i ≫ 𝟙 _ = q i
        exact Category.comp_id _)
  obtain ⟨j, hj⟩ := Model.exists_common_maps D c hc (op s) src dst Z t M m
  let N₁ (o : O) := (M o).rebase D c (op s) j
  let a₁ (a : A) := Classical.choice (hj a)
  let emb (i : J) : A := .inr (.inr (.inl i))
  let pt (i : K) : A := .inr (.inr (.inr i))
  let : ∀ i : J, IsClosedImmersion (m (emb i)).left :=
    fun i => inferInstanceAs (IsClosedImmersion (e i))
  obtain ⟨k, hk⟩ := Model.Map.exists_common_rebase_isClosedImmersion D c hc j.left
    (fun i : J => a₁ (emb i))
  let N₂ (o : O) := (N₁ o).rebase D c j.left k
  let a₂ (a : A) := (a₁ a).rebase D c j.left k
  have hmiso (i : K) : IsIso (m (pt i)) := by
    let : IsIso ((Over.forget (Spec (.of L))).map (m (pt i))) := by
      change IsIso (q i)
      exact hpoint i
    exact isIso_of_reflects_iso (m (pt i)) (Over.forget _)
  have hbaseiso (i : K) :
      IsIso ((Over.pullback (c.π.app k.left)).map (a₂ (pt i)).hom) := by
    let : IsIso (m (pt i)) := hmiso i
    exact Model.Map.isIso_baseChange (m := m (pt i)) (a₂ (pt i))
  obtain ⟨l, hl⟩ :=
    @Scheme.exists_common_stage_isIso_baseChange_maps_of_isLimit
      _ _ _ D inferInstance inferInstance inferInstance c hc k.left K inferInstance
      (fun i : K => (N₂ (obranch i)).X) (fun _ : K => (N₂ obase).X)
      (fun i : K => (N₂ (obranch i)).f) (fun _ : K => (N₂ obase).f)
      (fun i => (N₂ (obranch i)).locallyOfFinitePresentation)
      (fun i => (N₂ (obranch i)).quasiCompact)
      (fun _ => (N₂ obase).locallyOfFinitePresentation)
      (fun _ => (N₂ obase).quasiCompact)
      (fun _ => (N₂ obase).quasiSeparated)
      (fun i : K => (a₂ (pt i)).hom) hbaseiso
  let N₃ (o : O) := (N₂ o).rebase D c k.left l
  let a₃ (a : A) := (a₂ a).rebase D c k.left l
  let δ₁ := D.map j.hom
  let δ₂ := D.map k.hom
  let δ₃ := D.map l.hom
  let τ := l.hom ≫ k.hom ≫ j.hom
  let ψ : stage R L s →+* stage R L l.left.unop := (F.map τ.unop).hom
  have hδ : δ₃ ≫ δ₂ ≫ δ₁ = Spec.map (CommRingCat.ofHom ψ) := by
    dsimp only [δ₁, δ₂, δ₃]
    rw [← D.map_comp, ← D.map_comp]
    rfl
  let r (o : O) : (N₃ o).X ⟶ (M o).X :=
    pullback.fst (N₂ o).f δ₃ ≫ pullback.fst (N₁ o).f δ₂ ≫ pullback.fst (M o).f δ₁
  have Hr (o : O) : IsPullback (r o) (N₃ o).f (M o).f
      (Spec.map (CommRingCat.ofHom ψ)) := by
    change IsPullback
      (pullback.fst (N₂ o).f δ₃ ≫ pullback.fst (N₁ o).f δ₂ ≫
        pullback.fst (M o).f δ₁)
      (pullback.snd (N₂ o).f δ₃) (M o).f _
    have H := (IsPullback.of_hasPullback (N₂ o).f δ₃).paste_horiz
      ((IsPullback.of_hasPullback (N₁ o).f δ₂).paste_horiz
        (IsPullback.of_hasPullback (M o).f δ₁))
    rw [hδ] at H
    exact H
  have hr (o : O) : (N₃ o).p ≫ r o = (M o).p := by
    have h₃ : (N₃ o).p ≫ pullback.fst (N₂ o).f δ₃ = (N₂ o).p :=
      Model.rebase_p_fst D c k.left (N₂ o) l
    have h₂ : (N₂ o).p ≫ pullback.fst (N₁ o).f δ₂ = (N₁ o).p :=
      Model.rebase_p_fst D c j.left (N₁ o) k
    have h₁ : (N₁ o).p ≫ pullback.fst (M o).f δ₁ = (M o).p :=
      Model.rebase_p_fst D c (op s) (M o) j
    change (N₃ o).p ≫ pullback.fst (N₂ o).f δ₃ ≫
      pullback.fst (N₁ o).f δ₂ ≫ pullback.fst (M o).f δ₁ = _
    rw [← Category.assoc, h₃, ← Category.assoc, h₂, h₁]
  have hproper (i : I) : IsProper (N₃ (obranch i)).f :=
    IsProper.isStableUnderBaseChange.of_isPullback (Hr (obranch i)) (hMs i)
  have htarget : IsProper (N₃ otarget).f := by
    have h₀ : IsProper (M otarget).f :=
      IsProper.isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback p (stageStructure R L s)) inferInstance
    exact IsProper.isStableUnderBaseChange.of_isPullback (Hr otarget) h₀
  let hbase : IsIso (N₃ obase).f :=
    (Hr obase).isIso_snd_of_isIso
      (show IsIso (M obase).f from inferInstanceAs (IsIso (𝟙 _)))
  let σa (i : I) := inv (N₃ obase).f ≫ (a₃ (.inr (.inl i))).hom.left
  have hσa (i : I) : σa i ≫ (N₃ (obranch i)).f = 𝟙 _ := by
    have hw : (a₃ (.inr (.inl i))).hom.left ≫ (N₃ (obranch i)).f = (N₃ obase).f :=
      Over.w (a₃ (.inr (.inl i))).hom
    change (inv (N₃ obase).f ≫ (a₃ (.inr (.inl i))).hom.left) ≫
      (N₃ (obranch i)).f = _
    rw [Category.assoc, hw, IsIso.inv_hom_id]
  have hσcomp (i : I) : inclusion R L l.left.unop ≫ σa i = σ i ≫ (N₃ (obranch i)).p := by
    have hs : (N₃ obase).p ≫ (N₃ obase).f = inclusion R L l.left.unop := by
      have H := (N₃ obase).square.w
      change (N₃ obase).p ≫ (N₃ obase).f =
        (𝟙 (Spec (.of L))) ≫ inclusion R L l.left.unop at H
      simpa only [Category.id_comp] using H
    have hb : inclusion R L l.left.unop ≫ inv (N₃ obase).f = (N₃ obase).p := by
      rw [← hs, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have hm : (N₃ obase).p ≫ (a₃ (.inr (.inl i))).hom.left =
        σ i ≫ (N₃ (obranch i)).p := (a₃ (.inr (.inl i))).comm
    change inclusion R L l.left.unop ≫
      (inv (N₃ obase).f ≫ (a₃ (.inr (.inl i))).hom.left) = _
    rw [← Category.assoc, hb, hm]
  refine ⟨l.left.unop, N₃ otarget, (fun i => N₃ (obranch i)), htarget, hproper, ?_,
    (fun i => ⟨a₃ (.inl i)⟩), ⟨σa, hσa, hσcomp⟩, ?_, ?_⟩
  · refine ⟨r otarget ≫ pullback.fst p (stageStructure R L s), ?_, ?_⟩
    · have H := (Hr otarget).paste_horiz
        (IsPullback.of_hasPullback p (stageStructure R L s))
      have hs : Spec.map (CommRingCat.ofHom ψ) ≫ stageStructure R L s =
          stageStructure R L l.left.unop := stage_structure R L τ.unop
      rw [hs] at H
      exact H
    · rw [← Category.assoc, hr otarget]
      exact (IsPullback.of_hasPullback p (stageStructure R L s)).lift_fst _ _ _
  · intro i
    let : IsIso (a₃ (pt i)).hom := hl i
    let : IsIso (a₃ (pt i)).hom.left :=
      inferInstanceAs (IsIso ((Over.forget (D.obj l.left)).map (a₃ (pt i)).hom))
    have hw : (a₃ (pt i)).hom.left ≫ (N₃ obase).f = (N₃ (obranch i)).f :=
      Over.w (a₃ (pt i)).hom
    rw [← hw]
    infer_instance
  · intro i
    let Q := ProjectiveSpace.baseChangeIso ψ (ULift.{u} (Fin (n i + 1)))
    let E : (N₃ (oprojective i)).X ≅
        ProjectiveSpace (stage R L l.left.unop) (ULift.{u} (Fin (n i + 1))) :=
      (Hr (oprojective i)).isoPullback ≪≫ Q.symm
    have hEcomp : E.hom ≫ Q.hom = (Hr (oprojective i)).isoPullback.hom := by
      change ((Hr (oprojective i)).isoPullback.hom ≫ Q.inv) ≫ Q.hom = _
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hQ : Q.inv ≫
        ProjectiveSpace.toSpec (stage R L l.left.unop) (ULift.{u} (Fin (n i + 1))) =
        pullback.snd (ProjectiveSpace.toSpec (stage R L s) (ULift.{u} (Fin (n i + 1))))
          (Spec.map (CommRingCat.ofHom ψ)) :=
      (Iso.inv_comp_eq Q).mpr (ProjectiveSpace.baseChangeIso_hom_snd ψ _).symm
    have hE : E.hom ≫ ProjectiveSpace.toSpec (stage R L l.left.unop)
        (ULift.{u} (Fin (n i + 1))) = (N₃ (oprojective i)).f := by
      change ((Hr (oprojective i)).isoPullback.hom ≫ Q.inv) ≫ _ = _
      rw [Category.assoc, hQ]
      exact (Hr (oprojective i)).isoPullback_hom_snd
    have hEp : (N₃ (oprojective i)).p ≫ E.hom =
        ProjectiveSpace.map (stage R L l.left.unop).val.toRingHom
          (ULift.{u} (Fin (n i + 1))) := by
      apply (cancel_mono Q.hom).mp
      rw [Category.assoc, hEcomp]
      have hfst : (Hr (oprojective i)).isoPullback.hom ≫
          pullback.fst (ProjectiveSpace.toSpec (stage R L s)
            (ULift.{u} (Fin (n i + 1)))) (Spec.map (CommRingCat.ofHom ψ)) =
          r (oprojective i) := (Hr (oprojective i)).isoPullback_hom_fst
      have hsnd : (Hr (oprojective i)).isoPullback.hom ≫
          pullback.snd (ProjectiveSpace.toSpec (stage R L s)
            (ULift.{u} (Fin (n i + 1)))) (Spec.map (CommRingCat.ofHom ψ)) =
          (N₃ (oprojective i)).f := (Hr (oprojective i)).isoPullback_hom_snd
      apply pullback.hom_ext
      · rw [Category.assoc, hfst, hr (oprojective i)]
        rw [Category.assoc, ProjectiveSpace.baseChangeIso_hom_fst, ← ProjectiveSpace.map_comp]
        exact congrArg (fun φ : stage R L s →+* L =>
          ProjectiveSpace.map φ (ULift.{u} (Fin (n i + 1))))
          (show (stage R L s).val.toRingHom =
            (stage R L l.left.unop).val.toRingHom.comp ψ from RingHom.ext fun _ => rfl)
      · rw [Category.assoc, hsnd]
        rw [Category.assoc, ProjectiveSpace.baseChangeIso_hom_snd,
          ProjectiveSpace.map_toSpec]
        exact (N₃ (oprojective i)).square.w
    have hclosed : IsClosedImmersion (a₃ (emb i)).hom.left :=
      MorphismProperty.overPullbackMap (P := @IsClosedImmersion) δ₃ (a₂ (emb i)).hom (hk i)
    have hclosedE : IsClosedImmersion ((a₃ (emb i)).hom.left ≫ E.hom) :=
      MorphismProperty.comp_mem (@IsClosedImmersion) _ _ hclosed inferInstance
    refine ⟨(a₃ (emb i)).hom.left ≫ E.hom, hclosedE, ?_, ?_⟩
    · have hw : (a₃ (emb i)).hom.left ≫ (N₃ (oprojective i)).f =
          (N₃ (obranch i)).f := Over.w (a₃ (emb i)).hom
      rw [Category.assoc, hE, hw]
    · have hm : (N₃ (obranch i)).p ≫ (a₃ (emb i)).hom.left =
          e i ≫ (N₃ (oprojective i)).p := (a₃ (emb i)).comm
      rw [← Category.assoc, hm, Category.assoc, hEp]

end AlgebraicGeometry.Scheme.OverField.Curve.Normalization.GenericCover
