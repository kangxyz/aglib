/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Normalization.GeometricCover
public import Aglib.AlgebraicGeometry.Curves.Normalization.FiniteFieldModel
public import Aglib.AlgebraicGeometry.Dimension.Integral
public import Aglib.AlgebraicGeometry.Morphisms.Finite.Coproduct
public import Aglib.AlgebraicGeometry.Morphisms.Finite.SurjectiveBaseChange
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Finite normal curve covers after one finite field extension

The geometric cover is constructed over the original algebraic closure and all
its source models, arrows and sections descend to one common actual finite field
stage. The target is identified with the literal base change of the original X.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Algebra.FiniteTypeSubalgebraLimit
open AlgebraicGeometry.Scheme.FinitePresentationDescent

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Normalization.FiniteField

variable (K : Type u) [Field K]

private abbrev inclusion (s : Finset (AlgebraicClosure K)) :=
  Spec.map (CommRingCat.ofHom (stage K s).val.toRingHom)

/-- The original coefficient map of the actual finite field stage. -/
abbrev stageStructureMap (s : Finset (AlgebraicClosure K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (stage K s)))

private abbrev closureMap :=
  Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))

private theorem inclusion_structure (s : Finset (AlgebraicClosure K)) :
    inclusion K s ≫ stageStructureMap K s = closureMap K := by
  rw [← Spec.map_comp]
  rfl

private theorem stage_structure {s t : Finset (AlgebraicClosure K)} (q : s ⟶ t) :
    Spec.map ((ringDiagram K (AlgebraicClosure K)).map q) ≫ stageStructureMap K s =
      stageStructureMap K t := by
  dsimp only [ringDiagram, subalgebraDiagram, stageStructureMap]
  rw [← Spec.map_comp]
  rfl

private def originalTargetModel
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (s : Finset (AlgebraicClosure K)) :
    Model (inclusion K s) (pullback.snd p (closureMap K)) := by
  let H : IsPullback (pullback.fst p (closureMap K))
      (pullback.snd p (closureMap K)) p (inclusion K s ≫ stageStructureMap K s) := by
    rw [inclusion_structure]
    exact IsPullback.of_hasPullback p (closureMap K)
  let Q := IsPullback.of_hasPullback p (stageStructureMap K s)
  exact {
    X := pullback p (stageStructureMap K s)
    f := pullback.snd p (stageStructureMap K s)
    locallyOfFinitePresentation := inferInstance
    quasiCompact := inferInstance
    quasiSeparated := inferInstance
    p := Q.lift (pullback.fst p (closureMap K))
      (pullback.snd p (closureMap K) ≫ inclusion K s) (by
        simpa only [Category.assoc] using H.w)
    square := H.of_right' Q }

private def originalBaseModel (s : Finset (AlgebraicClosure K)) :
    Model (inclusion K s) (𝟙 (Spec (.of (AlgebraicClosure K)))) where
  X := Spec (.of (stage K s))
  f := 𝟙 _
  locallyOfFinitePresentation := inferInstance
  quasiCompact := inferInstance
  quasiSeparated := inferInstance
  p := inclusion K s
  square := IsPullback.of_id_snd

set_option backward.isDefEq.respectTransparency false in
/-- Classify the same descended model using its actual cartesian comparison
and its descended section. No new geometric model is selected. -/
private theorem model_point_or_curve
    {L Ω : Type u} [Field L] [Field Ω]
    {C : Scheme.{u}} (q : C ⟶ Spec (.of Ω))
    (b : Spec (.of Ω) ⟶ Spec (.of L))
    (M : Model b q) [IsProper M.f]
    (o : Spec (.of L) ⟶ M.X) (ho : o ≫ M.f = 𝟙 _)
    (hC : IsIso q ∨ Properties (Over.mk q)) :
    IsIso M.f ∨ (Properties (Over.mk M.f) ∧
      ∃ (N : ℕ) (i : M.X ⟶ ProjectiveSpace L (ULift.{u} (Fin (N + 1)))),
        IsClosedImmersion i ∧
          i ≫ ProjectiveSpace.toSpec L (ULift.{u} (Fin (N + 1))) = M.f) := by
  let : Surjective b := Scheme.Geometrically.fieldSpec_surjective b
  have hb : ((@Surjective ⊓ @Flat ⊓ @QuasiCompact :
      MorphismProperty Scheme.{u}) b) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  rcases hC with hpoint | hcurve
  · left
    exact MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) M.square.flip hb hpoint
  · right
    let : SmoothOfRelativeDimension 1 q := hcurve.smooth
    let : Smooth M.f := MorphismProperty.of_isPullback_of_descendsAlong
      (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      M.square.flip hb (SmoothOfRelativeDimension.smooth 1 q)
    let : SmoothOfRelativeDimension 1 (pullback.snd M.f b) := by
      have hw : M.overIso.hom.left ≫ q = pullback.snd M.f b := M.overIso.hom.w
      rw [← hw]
      let : IsIso M.overIso.hom.left :=
        inferInstanceAs (IsIso ((Over.forget (Spec (.of Ω))).map M.overIso.hom))
      exact smoothOfRelativeDimension_comp 0 1 M.overIso.hom.left q
    let : SmoothOfRelativeDimension 1 M.f :=
      Scheme.smoothOfRelativeDimension_of_dominant_fieldBaseChange M.f b 1
    let : ConnectedSpace C := curveProperties_connectedSpace hcurve
    let : Surjective M.p := MorphismProperty.of_isPullback
      (P := @Surjective) M.square.flip inferInstance
    let : ConnectedSpace M.X := M.p.surjective.connectedSpace M.p.continuous
    have hconn : GeometricallyConnected M.f :=
      Scheme.Geometrically.geometricallyConnected_of_connectedSpace_of_section M.f o ho
    let : IsProper (Over.mk M.f).hom := ‹IsProper M.f›
    have hM : Properties (Over.mk M.f) :=
      ⟨(inferInstance : SmoothOfRelativeDimension 1 M.f), ‹IsProper M.f›, hconn⟩
    exact ⟨hM, Projectivity.curveProperties_exists_projectiveEmbedding hM⟩

set_option backward.isDefEq.respectTransparency false in
/-- After one actual finite field extension, the original proper scheme of
dimension at most one has a finite surjective cover by points and pointed smooth
projective geometrically connected curves. All maps, sections and the common
field stage are constructed internally from the original geometric cover. -/
theorem exists_finite_field_component_cover
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) :
    ∃ s : Finset (AlgebraicClosure K), ∃ I : Type u, Finite I ∧
      ∃ (C : I → Scheme.{u})
        (ν : ∀ i, C i ⟶ pullback p (stageStructureMap K s)),
        (∀ i, IsFinite (ν i)) ∧ IsFinite (Sigma.desc ν) ∧ Surjective (Sigma.desc ν) ∧
        ∀ i, ∃ o : Spec (.of (stage K s)) ⟶ C i,
          o ≫ (ν i ≫ pullback.snd p (stageStructureMap K s)) = 𝟙 _ ∧
          (IsIso (ν i ≫ pullback.snd p (stageStructureMap K s)) ∨
            (Properties (Over.mk (ν i ≫ pullback.snd p (stageStructureMap K s))) ∧
              ∃ (N : ℕ) (j : C i ⟶ ProjectiveSpace (stage K s) (ULift.{u} (Fin (N + 1)))),
                IsClosedImmersion j ∧
                  j ≫ ProjectiveSpace.toSpec (stage K s) (ULift.{u} (Fin (N + 1))) =
                    ν i ≫ pullback.snd p (stageStructureMap K s))) := by
  classical
  let Ω := AlgebraicClosure K
  let b := closureMap K
  let Y := pullback p b
  let q : Y ⟶ Spec (.of Ω) := pullback.snd p b
  let : IsIntegralHom b := IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr inferInstance)
  have hdim : topologicalKrullDim Y ≤ 1 :=
    (pullback.fst p b).topologicalKrullDim_le_of_isIntegralHom.trans hd
  obtain ⟨hI, C₀, ν₀, hfin₀, hrange₀, htotal₀, hsurj₀, hmodel₀⟩ :=
    Normalization.exists_finite_normal_component_cover Ω Y q hdim
  let I := ↥(irreducibleComponents Y)
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let q₀ (i : I) := ν₀ i ≫ q
  choose o₀ ho₀ hshape₀ using fun i => (hmodel₀ i).2
  have hproper₀ (i : I) : IsProper (q₀ i) := by
    rcases hshape₀ i with hi | hi
    · let : IsIso (q₀ i) := hi
      infer_instance
    · exact hi.1.proper
  let (i : I) : IsProper (q₀ i) := hproper₀ i
  choose s₀ M₀ hM₀ using fun i => exists_proper_model K (q₀ i)
  let F := ringDiagram K Ω
  let D : (Finset Ω)ᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (ringCocone K Ω).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit K Ω).op
  have (i : (Finset Ω)ᵒᵖ) : CompactSpace (D.obj i) :=
    inferInstanceAs (CompactSpace (Spec (.of (stage K i.unop))))
  have (i : (Finset Ω)ᵒᵖ) : QuasiSeparatedSpace (D.obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of (stage K i.unop))))
  have (i : (Finset Ω)ᵒᵖ) : IsAffine (D.obj i) :=
    inferInstanceAs (IsAffine (Spec (.of (stage K i.unop))))
  have {i j : (Finset Ω)ᵒᵖ} (r : i ⟶ j) : IsAffineHom (D.map r) := inferInstance
  let s : Finset Ω := Finset.univ.biUnion s₀
  have hsub (i : I) : s₀ i ⊆ s := Finset.subset_biUnion_of_mem s₀ (Finset.mem_univ i)
  let Ms (i : I) : Model (c.π.app (op s)) (q₀ i) :=
    (M₀ i).rebase D c (op (s₀ i)) (Over.mk (homOfLE (hsub i)).op)
  have hMs (i : I) : IsProper (Ms i).f := by
    let : IsProper (M₀ i).f := hM₀ i
    change IsProper (pullback.snd (M₀ i).f (D.map (homOfLE (hsub i)).op))
    exact MorphismProperty.pullback_snd (P := @IsProper) _ _ (hM₀ i)
  let O := Bool ⊕ I
  let Z : O → Scheme.{u} := Sum.elim (Bool.rec (Spec (.of Ω)) Y) C₀
  let t : ∀ z : O, Z z ⟶ Spec (.of Ω) := fun z => by
    rcases z with z | i
    · cases z
      · exact 𝟙 _
      · exact q
    · exact q₀ i
  let M : ∀ z : O, Model (c.π.app (op s)) (t z) := fun z => by
    rcases z with z | i
    · cases z
      · exact originalBaseModel K s
      · exact originalTargetModel K p s
    · exact Ms i
  let src : I ⊕ I → O := Sum.elim Sum.inr (fun _ => Sum.inl false)
  let dst : I ⊕ I → O := Sum.elim (fun _ => Sum.inl true) Sum.inr
  let m : ∀ a : I ⊕ I, Over.mk (t (src a)) ⟶ Over.mk (t (dst a)) := fun a => by
    rcases a with i | i
    · exact Over.homMk (ν₀ i) rfl
    · exact Over.homMk (o₀ i) (ho₀ i)
  obtain ⟨j, hj⟩ := Model.exists_common_maps D c hc (op s) src dst Z t M m
  let N (z : O) := (M z).rebase D c (op s) j
  let a (i : I) := Classical.choice (hj (Sum.inl i))
  let o (i : I) := Classical.choice (hj (Sum.inr i))
  let δ := D.map j.hom
  have hδ : δ ≫ stageStructureMap K s = stageStructureMap K j.left.unop :=
    stage_structure K j.hom.unop
  let e : (N (Sum.inl true)).X ≅ pullback p (stageStructureMap K j.left.unop) :=
    pullbackLeftPullbackSndIso p (stageStructureMap K s) δ ≪≫ pullback.congrHom rfl hδ
  have he : e.hom ≫ pullback.snd p (stageStructureMap K j.left.unop) =
      (N (Sum.inl true)).f := by
    change e.hom ≫ pullback.snd p (stageStructureMap K j.left.unop) =
      pullback.snd (pullback.snd p (stageStructureMap K s)) δ
    simp only [e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
      pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  let C (i : I) := (N (Sum.inr i)).X
  let ν (i : I) : C i ⟶ pullback p (stageStructureMap K j.left.unop) :=
    (a i).hom.left ≫ e.hom
  have hν (i : I) : ν i ≫ pullback.snd p (stageStructureMap K j.left.unop) =
      (N (Sum.inr i)).f := by
    dsimp only [ν]
    rw [Category.assoc, he]
    exact (a i).hom.w
  let : IsIso (N (Sum.inl false)).f := by
    change IsIso (pullback.snd (𝟙 _) δ)
    infer_instance
  let sec (i : I) : Spec (.of (stage K j.left.unop)) ⟶ C i :=
    inv (N (Sum.inl false)).f ≫ (o i).hom.left
  have hsection (i : I) : sec i ≫ (N (Sum.inr i)).f = 𝟙 _ := by
    dsimp only [sec]
    have hw : (o i).hom.left ≫ (N (Sum.inr i)).f =
        (N (Sum.inl false)).f := (o i).hom.w
    rw [Category.assoc, hw]
    simp
  have hproper (i : I) : IsProper (N (Sum.inr i)).f := by
    let : IsProper (Ms i).f := hMs i
    change IsProper (pullback.snd (Ms i).f δ)
    exact MorphismProperty.pullback_snd (P := @IsProper) _ _ (hMs i)
  let B := (N (Sum.inl true)).p
  let : Surjective (c.π.app j.left) :=
    Scheme.Geometrically.fieldSpec_surjective (c.π.app j.left)
  let : Surjective B := MorphismProperty.of_isPullback (P := @Surjective)
    (N (Sum.inl true)).square.flip inferInstance
  let : IsProper (N (Sum.inl true)).f := by
    change IsProper (pullback.snd (pullback.snd p (stageStructureMap K s)) δ)
    infer_instance
  have hfinite (i : I) : IsFinite (ν i) := by
    let : IsProper (N (Sum.inr i)).f := hproper i
    let : IsProper ((a i).hom.left ≫ (N (Sum.inl true)).f) := by
      have hw : (a i).hom.left ≫ (N (Sum.inl true)).f =
          (N (Sum.inr i)).f := (a i).hom.w
      rw [hw]
      exact hproper i
    let : IsProper (a i).hom.left := IsProper.of_comp (a i).hom.left
      (N (Sum.inl true)).f
    let : IsFinite (ν₀ i) := hfin₀ i
    have hcart : IsPullback (N (Sum.inr i)).p (ν₀ i) (a i).hom.left B :=
      (a i).isPullback.flip
    let : IsFinite (a i).hom.left :=
      isFinite_of_isProper_of_isPullback hcart
    exact inferInstanceAs (IsFinite ((a i).hom.left ≫ e.hom))
  let : ∀ i, IsFinite (ν i) := hfinite
  have hsurj : Surjective (Sigma.desc ν) := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := B.surjective (e.inv x)
    let i : I := ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    have hmem : y ∈ Set.range (ν₀ i) := by
      rw [hrange₀ i]
      exact mem_irreducibleComponent
    obtain ⟨z, hz⟩ := hmem
    refine ⟨Sigma.ι C i ((N (Sum.inr i)).p z), ?_⟩
    have hmap := congrArg (fun f : C₀ i ⟶ (N (Sum.inl true)).X => f z) (a i).comm
    have hdesc := congrArg (fun f : C i ⟶ pullback p (stageStructureMap K j.left.unop) =>
      f ((N (Sum.inr i)).p z)) (Sigma.ι_comp_desc ν i)
    calc
      _ = ν i ((N (Sum.inr i)).p z) := hdesc
      _ = e.hom (B (ν₀ i z)) := congrArg e.hom hmap
      _ = x := by
        rw [hz, hy]
        exact congrArg (fun f : pullback p (stageStructureMap K j.left.unop) ⟶
          pullback p (stageStructureMap K j.left.unop) => f.base x) e.inv_hom_id
  refine ⟨j.left.unop, I, inferInstance, C, ν, hfinite,
    Scheme.Hom.isFinite_sigmaDesc C _ ν, hsurj, ?_⟩
  intro i
  refine ⟨sec i, (by rw [hν]; exact hsection i), ?_⟩
  rw [hν]
  let : IsProper (N (Sum.inr i)).f := hproper i
  exact model_point_or_curve (q₀ i) (c.π.app j.left) (N (Sum.inr i))
    (sec i) (hsection i) ((hshape₀ i).imp id And.left)

end AlgebraicGeometry.Scheme.OverField.Curve.Normalization.FiniteField
