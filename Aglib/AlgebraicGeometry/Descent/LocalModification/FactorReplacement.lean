/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.LocalModification

/-!
# Spreading a specified factorization together with a stalk replacement

The target model is the actual base change of the prescribed global target.
Maps are descended with their original cartesian comparison, not selected
merely between abstractly isomorphic schemes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.LocalModification

/-- The actual target localization has a model at every original affine
neighborhood, with its original projection to the global target. -/
def targetNeighborhoodModel {X B : Scheme.{u}} (b : B ⟶ X)
    [LocallyOfFinitePresentation b] [QuasiCompact b] [QuasiSeparated b]
    (x : X) (i : (AffineNeighborhood X x)ᵒᵖᵒᵖ) :
    FinitePresentationDescent.Model ((affineNeighborhoodCone X x).π.app i)
      (pullback.snd b (X.fromSpecStalk x)) := by
  let n := affineNeighborhoodToBase X x i
  let c := X.fromSpecStalk x
  let π := (affineNeighborhoodCone X x).π.app i
  let Q := IsPullback.of_hasPullback b n
  have H : IsPullback (pullback.fst b c) (pullback.snd b c) b (π ≫ n) := by
    rw [show π ≫ n = c from affineNeighborhoodCone_comp X x i]
    exact IsPullback.of_hasPullback b c
  exact
    { X := pullback b n
      f := pullback.snd b n
      locallyOfFinitePresentation := inferInstance
      quasiCompact := inferInstance
      quasiSeparated := inferInstance
      p := Q.lift (pullback.fst b c) (pullback.snd b c ≫ π)
        (by simpa only [Category.assoc] using H.w)
      square := H.of_right' Q }

@[reassoc (attr := simp)]
theorem targetNeighborhoodModel_p_fst {X B : Scheme.{u}} (b : B ⟶ X)
    [LocallyOfFinitePresentation b] [QuasiCompact b] [QuasiSeparated b]
    (x : X) (i : (AffineNeighborhood X x)ᵒᵖᵒᵖ) :
    (targetNeighborhoodModel b x i).p ≫
      pullback.fst b (affineNeighborhoodToBase X x i) =
        pullback.fst b (X.fromSpecStalk x) := by
  simp [targetNeighborhoodModel]

/-- Spread the actual arrow into a prescribed proper model as well as the
proper punctured-isomorphism stalk modification. Both original triangles
are retained by the output; the factor is constructed by open gluing. -/
theorem exists_stalkReplacement_factor
    {X B T : Scheme.{u}} [IsLocallyNoetherian X]
    (x : X) (hx : IsClosed ({x} : Set X)) (b : B ⟶ X) [IsProper b]
    (hb : IsIso (b ∣_ pointComplement x hx))
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p]
    (hp : IsIso (p ∣_ X.fromSpecStalk x ⁻¹ᵁ pointComplement x hx))
    (a : T ⟶ B) (ha : a ≫ b = p ≫ X.fromSpecStalk x) :
    ∃ R : StalkReplacement x hx p, ∃ r : R.Y ⟶ B,
      IsProper r ∧ r ≫ b = R.h ∧ R.a ≫ r = a := by
  let U := pointComplement x hx
  let c := X.fromSpecStalk x
  let D := affineNeighborhoodDiagram X x
  let C := affineNeighborhoodCone X x
  let : LocallyOfFinitePresentation b :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := b)).mpr inferInstance
  obtain ⟨i, M, hMproper, hMiso⟩ :=
    exists_proper_affineNeighborhood_model_isIso X x U p hp
  let := hMproper
  let n := affineNeighborhoodToBase X x i
  let N := targetNeighborhoodModel b x i
  let m : Over.mk p ⟶ Over.mk (pullback.snd b c) :=
    Over.homMk (pullback.lift a p ha) (by simp)
  obtain ⟨j, ⟨d⟩⟩ := FinitePresentationDescent.Model.exists_map D C
    (affineNeighborhoodConeIsLimit X x) i M N m
  let M' := M.rebase D C i j
  let N' := N.rebase D C i j
  let n' := affineNeighborhoodToBase X x j.left
  let iB : N'.X ⟶ B :=
    pullback.fst N.f (D.map j.hom) ≫ pullback.fst b n
  have HN : IsPullback iB N'.f b n' := by
    have H := (IsPullback.of_hasPullback N.f (D.map j.hom)).paste_horiz
      (IsPullback.of_hasPullback b n)
    change IsPullback iB N'.f b (D.map j.hom ≫ n) at H
    have hn : D.map j.hom ≫ n = n' := affineNeighborhoodToBase_naturality X x j.hom
    rw [hn] at H
    exact H
  let : IsOpenImmersion iB := MorphismProperty.of_isPullback HN.flip inferInstance
  let : IsProper N'.f := MorphismProperty.of_isPullback HN inferInstance
  let : IsProper M'.f := by
    change IsProper (pullback.snd M.f (D.map j.hom))
    infer_instance
  let q : M'.X ⟶ N'.X := d.hom.left
  have hq : q ≫ N'.f = M'.f := Over.w d.hom
  let : IsProper q := by
    have : IsProper (q ≫ N'.f) := by rw [hq]; infer_instance
    exact IsProper.of_comp q N'.f
  let W := n' ⁻¹ᵁ U
  have hW : W = D.map j.hom ⁻¹ᵁ (n ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage]
    exact congrArg (fun k => k ⁻¹ᵁ U)
      (affineNeighborhoodToBase_naturality X x j.hom).symm
  have hM'iso : IsIso (M'.f ∣_ W) := by
    apply (isIso_restrict_iff_pullback_snd
      (pullback.fst M.f (D.map j.hom)) (pullback.snd M.f (D.map j.hom))
      M.f (D.map j.hom) (IsPullback.of_hasPullback M.f (D.map j.hom))
      (n ⁻¹ᵁ U) W hW).mpr
    let := hMiso
    infer_instance
  have hN'iso : IsIso (N'.f ∣_ W) := by
    apply (isIso_restrict_iff_pullback_snd iB N'.f b n' HN U W rfl).mpr
    let := hb
    infer_instance
  have hV : iB ⁻¹ᵁ (b ⁻¹ᵁ U) = N'.f ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, HN.w, Scheme.Hom.comp_preimage]
  have hqiso : IsIso (q ∣_ iB ⁻¹ᵁ (b ⁻¹ᵁ U)) := by
    rw [hV]
    let := hN'iso
    have : IsIso ((q ≫ N'.f) ∣_ W) := by rw [hq]; exact hM'iso
    rw [morphismRestrict_comp] at this
    exact IsIso.of_isIso_comp_right (q ∣_ N'.f ⁻¹ᵁ W) (N'.f ∣_ W)
  have hcentre : n' (C.π.app j.left
      (IsLocalRing.closedPoint (X.presheaf.stalk x))) = x := by
    calc
      _ = (C.π.app j.left ≫ n')
          (IsLocalRing.closedPoint (X.presheaf.stalk x)) :=
        (Scheme.Hom.comp_apply _ _ _).symm
      _ = c (IsLocalRing.closedPoint (X.presheaf.stalk x)) :=
        congrArg (fun k : Spec (X.presheaf.stalk x) ⟶ X =>
          k (IsLocalRing.closedPoint (X.presheaf.stalk x)))
          (affineNeighborhoodCone_comp X x j.left)
      _ = x := Scheme.fromSpecStalk_closedPoint
  have hcover : ∀ z : B, z ∈ Set.range iB ∨ z ∈ b ⁻¹ᵁ U := by
    intro z
    by_cases hz : b z = x
    · obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback HN z
        (C.π.app j.left (IsLocalRing.closedPoint (X.presheaf.stalk x)))
        (hz.trans hcentre.symm)
      exact Or.inl ⟨w, hw⟩
    · exact Or.inr hz
  let G := glueNeighborhood iB (b ⁻¹ᵁ U) hcover q hqiso
  have hNp : N'.p ≫ iB = pullback.fst b c := by
    dsimp only [iB, N']
    rw [FinitePresentationDescent.Model.rebase_p_fst_assoc]
    exact targetNeighborhoodModel_p_fst b x i
  let a' := M'.p ≫ G.j
  have Hlocal : IsPullback a' p (G.h ≫ b) c := by
    have H := d.isPullback.flip.paste_horiz G.square
    rw [hNp] at H
    have H' := H.paste_vert (IsPullback.of_hasPullback b c)
    change IsPullback a' (pullback.lift a p ha ≫ pullback.snd b c) (G.h ≫ b) c at H'
    rw [pullback.lift_snd] at H'
    exact H'
  have hproper : IsProper (G.h ≫ b) := by
    let := G.proper
    infer_instance
  have hiso : IsIso ((G.h ≫ b) ∣_ U) := by
    rw [morphismRestrict_comp]
    let := G.isoRestriction
    let := hb
    infer_instance
  let R : StalkReplacement x hx p :=
    { Y := G.Y
      h := G.h ≫ b
      proper := hproper
      a := a'
      square := Hlocal
      isoRestriction := hiso }
  refine ⟨R, G.h, G.proper, rfl, ?_⟩
  change (M'.p ≫ G.j) ≫ G.h = a
  rw [Category.assoc, G.square.w, ← Category.assoc, d.comm, Category.assoc, hNp]
  exact pullback.lift_fst a p ha

end AlgebraicGeometry.Scheme.LocalModification
