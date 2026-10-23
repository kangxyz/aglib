/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.Principalization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Literal pullbacks of original point-blowup chains

The cons step of a point-blowup chain is regrouped by the canonical pullback
pasting isomorphism. Both projections and the original structural triangles
are retained. Local Noetherianity propagates along the original blowups;
no base-changed blowup is identified with a blowup of an image ideal.
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

end AlgebraicGeometry.Scheme.Blowup
