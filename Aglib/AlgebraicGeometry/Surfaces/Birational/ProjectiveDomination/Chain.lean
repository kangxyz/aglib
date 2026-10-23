/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.Embedding
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.Principalization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Literal pullbacks and finite embeddings of original point-blowup chains

The cons step of a point-blowup chain is regrouped by the canonical pullback
pasting isomorphism. Both projections and the original structural triangles
are retained. Local Noetherianity propagates along the original blowups;
no base-changed blowup is identified with a blowup of an image ideal.
The concrete single-step projective embedding then gives a finite embedding
of the literal chain pullback, retaining its original structural map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup

section PullbackStep

variable {X Y W : Scheme.{u}} {I : X.IdealSheafData}
  (B : BlowupDatum I) (g : Y ⟶ B.Y) (π : W ⟶ X)

/-- The canonical map from the pullback of the original composite to the
pullback of its first original blowup. -/
def BlowupDatum.chainPullbackStepMap :
    pullback (g ≫ B.map) π ⟶ pullback B.map π :=
  pullback.lift (pullback.fst (g ≫ B.map) π ≫ g) (pullback.snd (g ≫ B.map) π)
    (by
      simpa only [Category.assoc] using
        (pullback.condition (f := g ≫ B.map) (g := π)))

/-- The first projection is the original chain-source projection followed
by the original tail map. -/
@[reassoc (attr := simp)]
theorem BlowupDatum.chainPullbackStepMap_fst :
    B.chainPullbackStepMap g π ≫ pullback.fst B.map π =
      pullback.fst (g ≫ B.map) π ≫ g :=
  pullback.lift_fst _ _ _

/-- The second projection is the original projection to `W`. -/
@[reassoc (attr := simp)]
theorem BlowupDatum.chainPullbackStepMap_snd :
    B.chainPullbackStepMap g π ≫ pullback.snd B.map π =
      pullback.snd (g ≫ B.map) π :=
  pullback.lift_snd _ _ _

/-- The canonical step map retains the triangle over the original scheme. -/
@[reassoc]
theorem BlowupDatum.chainPullbackStepMap_triangle :
    B.chainPullbackStepMap g π ≫ pullback.fst B.map π ≫ B.map =
      pullback.snd (g ≫ B.map) π ≫ π := by
  rw [← Category.assoc, chainPullbackStepMap_fst, Category.assoc]
  exact pullback.condition

/-- Regroup the actual pullback of an original cons composite as the
pullback of its original tail over the first pulled-back step. -/
def BlowupDatum.chainPullbackIso :
    pullback (g ≫ B.map) π ≅ pullback g (pullback.fst B.map π) :=
  (pullbackRightPullbackFstIso B.map π g).symm

/-- The regrouping retains the original projection to the chain source. -/
@[reassoc (attr := simp)]
theorem BlowupDatum.chainPullbackIso_hom_fst :
    (B.chainPullbackIso g π).hom ≫ pullback.fst g (pullback.fst B.map π) =
      pullback.fst (g ≫ B.map) π :=
  pullbackRightPullbackFstIso_inv_fst B.map π g

/-- On the first original blowup, the second projection retains the original
tail map. -/
@[reassoc]
theorem BlowupDatum.chainPullbackIso_hom_snd_fst :
    (B.chainPullbackIso g π).hom ≫ pullback.snd g (pullback.fst B.map π) ≫
        pullback.fst B.map π =
      pullback.fst (g ≫ B.map) π ≫ g :=
  pullbackRightPullbackFstIso_inv_snd_fst B.map π g

/-- On `W`, the second projection is the original composite-pullback
projection. -/
@[reassoc]
theorem BlowupDatum.chainPullbackIso_hom_snd_snd :
    (B.chainPullbackIso g π).hom ≫ pullback.snd g (pullback.fst B.map π) ≫
        pullback.snd B.map π =
      pullback.snd (g ≫ B.map) π :=
  pullbackRightPullbackFstIso_inv_snd_snd B.map π g

/-- The second projection of the regrouping is the canonical actual step
map, as an equality into the literal pullback. -/
@[reassoc (attr := simp)]
theorem BlowupDatum.chainPullbackIso_hom_snd :
    (B.chainPullbackIso g π).hom ≫ pullback.snd g (pullback.fst B.map π) =
      B.chainPullbackStepMap g π := by
  apply pullback.hom_ext
  · simp only [Category.assoc, chainPullbackIso_hom_snd_fst, chainPullbackStepMap_fst]
  · simp only [Category.assoc, chainPullbackIso_hom_snd_snd, chainPullbackStepMap_snd]

/-- The inverse regrouping retains the original chain-source projection. -/
@[reassoc (attr := simp)]
theorem BlowupDatum.chainPullbackIso_inv_fst :
    (B.chainPullbackIso g π).inv ≫ pullback.fst (g ≫ B.map) π =
      pullback.fst g (pullback.fst B.map π) :=
  pullbackRightPullbackFstIso_hom_fst B.map π g

/-- The inverse regrouping retains the original projection to `W`. -/
@[reassoc (attr := simp)]
theorem BlowupDatum.chainPullbackIso_inv_snd :
    (B.chainPullbackIso g π).inv ≫ pullback.snd (g ≫ B.map) π =
      pullback.snd g (pullback.fst B.map π) ≫ pullback.snd B.map π :=
  pullbackRightPullbackFstIso_hom_snd B.map π g

/-- The inverse regrouping also retains the projection to the first
literal pulled-back step. -/
@[reassoc (attr := simp)]
theorem BlowupDatum.chainPullbackIso_inv_stepMap :
    (B.chainPullbackIso g π).inv ≫ B.chainPullbackStepMap g π =
      pullback.snd g (pullback.fst B.map π) := by
  apply (cancel_epi (B.chainPullbackIso g π).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, chainPullbackIso_hom_snd]

/-- The regrouping retains the structural triangle through the original
blowup map and the original map `W → X`. -/
@[reassoc]
theorem BlowupDatum.chainPullbackIso_hom_triangle :
    (B.chainPullbackIso g π).hom ≫ pullback.snd g (pullback.fst B.map π) ≫
        pullback.fst B.map π ≫ B.map =
      pullback.snd (g ≫ B.map) π ≫ π := by
  rw [← Category.assoc, chainPullbackIso_hom_snd]
  exact B.chainPullbackStepMap_triangle g π

/-- Every original structural map out of `W` is unchanged by regrouping.
In the projective-embedding induction this is the original map to the base. -/
@[reassoc]
theorem BlowupDatum.chainPullbackIso_hom_structure {S : Scheme.{u}} (s : W ⟶ S) :
    (B.chainPullbackIso g π).hom ≫ pullback.snd g (pullback.fst B.map π) ≫
        pullback.snd B.map π ≫ s =
      pullback.snd (g ≫ B.map) π ≫ s := by
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ s) (B.chainPullbackIso_hom_snd_snd g π)

end PullbackStep

/-- Local Noetherianity propagates along the actual finite point-blowup
chain. Its original closed centres and local dimension-two proofs remain
the data of `PointBlowupChain.cons`. -/
theorem PointBlowupChain.isLocallyNoetherian {X Y : Scheme.{u}} {f : Y ⟶ X}
    (c : PointBlowupChain f) : IsLocallyNoetherian X → IsLocallyNoetherian Y := by
  induction c with
  | refl X => exact fun hX ↦ hX
  | @cons X _Y x _hx _hd _g _tail ih =>
    intro hX
    let : IsLocallyNoetherian X := hX
    exact ih (BlowupDatum.isLocallyNoetherian
      (blowupDatum (X.fromSpecResidueField x).ker))

private theorem exists_projective_embedding_pullback_aux
    {A : Type u} [CommRing A] {X Y : Scheme.{u}} {β : Y ⟶ X}
    (c : PointBlowupChain β) :
    IsLocallyNoetherian X →
      ∀ {W : Scheme.{u}} (π : W ⟶ X) {κ : Type u} [Finite κ]
        (j : W ⟶ ProjectiveSpace A κ) [IsClosedImmersion j],
        ∃ (J : Type u) (_ : Finite J)
          (k : pullback β π ⟶ ProjectiveSpace A J),
          IsClosedImmersion k ∧
            k ≫ ProjectiveSpace.toSpec A J =
              pullback.snd β π ≫ j ≫ ProjectiveSpace.toSpec A κ := by
  induction c with
  | refl X =>
    intro _hX W π κ hκ j _hj
    refine ⟨κ, hκ, pullback.snd (𝟙 X) π ≫ j, ?_, ?_⟩
    · infer_instance
    · exact Category.assoc _ _ _
  | @cons X _Y x _hx _hd g _tail ih =>
    intro hX W π κ _hκ j _hj
    let : IsLocallyNoetherian X := hX
    let B := blowupDatum (X.fromSpecResidueField x).ker
    obtain ⟨J, hJ, j₁, hj₁, hj₁_base⟩ :=
      ProjectivePresentation.exists_projective_embedding B π j
    let : Finite J := hJ
    let : IsClosedImmersion j₁ := hj₁
    obtain ⟨K, hK, k₁, hk₁, hk₁_base⟩ :=
      ih (BlowupDatum.isLocallyNoetherian B) (pullback.fst B.map π) j₁
    refine ⟨K, hK, (B.chainPullbackIso g π).hom ≫ k₁, ?_, ?_⟩
    · let : IsClosedImmersion k₁ := hk₁
      infer_instance
    · calc
        ((B.chainPullbackIso g π).hom ≫ k₁) ≫ ProjectiveSpace.toSpec A K =
            (B.chainPullbackIso g π).hom ≫ (k₁ ≫ ProjectiveSpace.toSpec A K) :=
          Category.assoc _ _ _
        _ = (B.chainPullbackIso g π).hom ≫
            (pullback.snd g (pullback.fst B.map π) ≫
              j₁ ≫ ProjectiveSpace.toSpec A J) :=
          congrArg (fun k ↦ (B.chainPullbackIso g π).hom ≫ k) hk₁_base
        _ = (B.chainPullbackIso g π).hom ≫
            pullback.snd g (pullback.fst B.map π) ≫
              pullback.snd B.map π ≫ j ≫ ProjectiveSpace.toSpec A κ := by
          rw [hj₁_base]
        _ = pullback.snd (g ≫ B.map) π ≫ j ≫ ProjectiveSpace.toSpec A κ := by
          simpa only [Category.assoc] using
            B.chainPullbackIso_hom_structure g π (j ≫ ProjectiveSpace.toSpec A κ)

/-- Embed the literal pullback of the original finite point-blowup chain,
retaining the original structural map determined by the supplied embedding. -/
theorem PointBlowupChain.exists_projective_embedding_pullback
    {A : Type u} [CommRing A] {X Y W : Scheme.{u}} [IsLocallyNoetherian X]
    {β : Y ⟶ X} (c : PointBlowupChain β) (π : W ⟶ X)
    {κ : Type u} [Finite κ] (j : W ⟶ ProjectiveSpace A κ) [IsClosedImmersion j] :
    ∃ (J : Type u) (_ : Finite J)
      (k : pullback β π ⟶ ProjectiveSpace A J),
      IsClosedImmersion k ∧
        k ≫ ProjectiveSpace.toSpec A J =
          pullback.snd β π ≫ j ≫ ProjectiveSpace.toSpec A κ :=
  exists_projective_embedding_pullback_aux c inferInstance π j

end AlgebraicGeometry.Scheme.Blowup
