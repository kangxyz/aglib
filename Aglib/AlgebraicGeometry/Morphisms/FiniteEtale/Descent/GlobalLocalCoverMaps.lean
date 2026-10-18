/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalAffineFieldCharts
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalPullbackReflection

/-!
# GlobalLocalCoverMaps

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

universe u

variable {X T U V : Scheme.{u}} (f : T ⟶ X) (i : U ⟶ X)

/-- Base change of a local object, compared to first base changing over the
local chart and then composing its structural map. -/
def localPullbackPushforwardIso (A : Over U) :
    (Over.pullback f).obj ((Over.map i).obj A) ≅
      (Over.map (pullback.snd i f)).obj ((Over.pullback (pullback.fst i f)).obj A) :=
  Over.isoMk (pullbackRightPullbackFstIso i f A.hom).symm
    (pullbackRightPullbackFstIso_inv_snd_snd i f A.hom)

@[reassoc (attr := simp)] theorem localPullbackPushforwardIso_inv_fst (A : Over U) :
    (localPullbackPushforwardIso f i A).inv.left ≫ pullback.fst (A.hom ≫ i) f =
      pullback.fst A.hom (pullback.fst i f) :=
  pullbackRightPullbackFstIso_hom_fst i f A.hom

@[reassoc (attr := simp)] theorem localPullbackPushforwardIso_hom_fst (A : Over U) :
    (localPullbackPushforwardIso f i A).hom.left ≫ pullback.fst A.hom (pullback.fst i f) =
      pullback.fst (A.hom ≫ i) f :=
  pullbackRightPullbackFstIso_inv_fst i f A.hom

theorem localPullbackPushforwardIso_structure (A : Over U) :
    ((Over.pullback f).map (Over.homMk A.hom rfl : (Over.map i).obj A ⟶ Over.mk i)).left =
      (localPullbackPushforwardIso f i A).hom.left ≫ pullback.snd A.hom (pullback.fst i f) := by
  apply pullback.hom_ext
  · change pullback.lift (pullback.fst (A.hom ≫ i) f ≫ A.hom)
        (pullback.snd (A.hom ≫ i) f) _ ≫ pullback.fst i f =
      ((localPullbackPushforwardIso f i A).hom.left ≫
        pullback.snd A.hom (pullback.fst i f)) ≫ pullback.fst i f
    rw [pullback.lift_fst, Category.assoc, ← pullback.condition,
      ← Category.assoc, localPullbackPushforwardIso_hom_fst]
  · change pullback.lift (pullback.fst (A.hom ≫ i) f ≫ A.hom)
        (pullback.snd (A.hom ≫ i) f) _ ≫ pullback.snd i f =
      ((localPullbackPushforwardIso f i A).hom.left ≫
        pullback.snd A.hom (pullback.fst i f)) ≫ pullback.snd i f
    rw [pullback.lift_snd, Category.assoc]
    exact (Over.w (localPullbackPushforwardIso f i A).hom).symm

/-- Local fullness lifts arrows between covers of nested open charts, even
after those covers are viewed merely as schemes over the whole base. -/
theorem local_overMap_surjective (j : V ⟶ X) [Mono j]
    (d : U ⟶ V) (hd : d ≫ j = i)
    [(baseChange (pullback.fst i f)).Full]
    (A : Scheme.FiniteEtale U) (B : Scheme.FiniteEtale V) :
    Function.Surjective ((Over.pullback f).map :
      ((Over.map i).obj A.obj ⟶ (Over.map j).obj B.obj) → _) := by
  intro q
  let e := localPullbackPushforwardIso f i A.obj
  let q' := e.inv ≫ q
  let z : pullback A.obj.hom (pullback.fst i f) ⟶ B.obj.left :=
    q'.left ≫ pullback.fst (B.obj.hom ≫ j) f
  have hz : z ≫ B.obj.hom =
      pullback.snd A.obj.hom (pullback.fst i f) ≫ pullback.fst i f ≫ d := by
    apply (cancel_mono j).mp
    have H : q'.left ≫ pullback.snd (B.obj.hom ≫ j) f =
        pullback.snd A.obj.hom (pullback.fst i f) ≫ pullback.snd i f := Over.w q'
    calc
      (z ≫ B.obj.hom) ≫ j = q'.left ≫
          pullback.fst (B.obj.hom ≫ j) f ≫ (B.obj.hom ≫ j) := by simp [z, Category.assoc]
      _ = q'.left ≫ pullback.snd (B.obj.hom ≫ j) f ≫ f := by rw [pullback.condition]
      _ = (pullback.snd A.obj.hom (pullback.fst i f) ≫ pullback.snd i f) ≫ f := by
        rw [← Category.assoc, H]
      _ = pullback.snd A.obj.hom (pullback.fst i f) ≫ pullback.fst i f ≫ i := by
        rw [Category.assoc, ← pullback.condition]
      _ = (pullback.snd A.obj.hom (pullback.fst i f) ≫ pullback.fst i f ≫ d) ≫ j := by
        simp [Category.assoc, hd]
  let φleft : pullback A.obj.hom (pullback.fst i f) ⟶
      pullback (pullback.snd B.obj.hom d) (pullback.fst i f) :=
    pullback.lift
      (pullback.lift z (pullback.snd A.obj.hom (pullback.fst i f) ≫ pullback.fst i f)
        (by simpa only [Category.assoc] using hz))
      (pullback.snd A.obj.hom (pullback.fst i f)) (pullback.lift_snd _ _ _)
  let φ : (baseChange (pullback.fst i f)).obj A ⟶
      (baseChange (pullback.fst i f)).obj ((baseChange d).obj B) :=
    ObjectProperty.homMk (Over.homMk φleft (pullback.lift_snd _ _ _))
  obtain ⟨b, hb⟩ := (baseChange (pullback.fst i f)).map_surjective φ
  have hbbase : b.hom.left ≫ pullback.snd B.obj.hom d = A.obj.hom := Over.w b.hom
  let g : (Over.map i).obj A.obj ⟶ (Over.map j).obj B.obj :=
    Over.homMk (b.hom.left ≫ pullback.fst B.obj.hom d) (by
      change (b.hom.left ≫ pullback.fst B.obj.hom d) ≫ (B.obj.hom ≫ j) = A.obj.hom ≫ i
      rw [Category.assoc, pullback.condition_assoc, ← Category.assoc, hbbase,
        hd])
  refine ⟨g, ?_⟩
  apply (cancel_epi e.inv).mp
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have Hb := congrArg (fun k ↦ k.hom.left ≫
        pullback.fst ((baseChange d).obj B).obj.hom (pullback.fst i f)) hb
    rw [baseChangeMap_fst] at Hb
    have H := congrArg (fun k ↦ k ≫ pullback.fst B.obj.hom d) Hb
    change (pullback.fst A.obj.hom (pullback.fst i f) ≫ b.hom.left) ≫
        pullback.fst B.obj.hom d =
      (φleft ≫ pullback.fst (pullback.snd B.obj.hom d) (pullback.fst i f)) ≫
        pullback.fst B.obj.hom d at H
    have H' : pullback.fst A.obj.hom (pullback.fst i f) ≫ b.hom.left ≫
        pullback.fst B.obj.hom d = z := by
      simpa only [φleft, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc] using H
    change e.inv.left ≫ ((Over.pullback f).map g).left ≫
      pullback.fst (B.obj.hom ≫ j) f = q'.left ≫ pullback.fst (B.obj.hom ≫ j) f
    have Hmap : ((Over.pullback f).map g).left ≫ pullback.fst (B.obj.hom ≫ j) f =
        pullback.fst (A.obj.hom ≫ i) f ≫ g.left := pullback.lift_fst _ _ _
    rw [Hmap]
    change e.inv.left ≫ pullback.fst (A.obj.hom ≫ i) f ≫
      b.hom.left ≫ pullback.fst B.obj.hom d = z
    rw [localPullbackPushforwardIso_inv_fst_assoc]
    exact H'
  · exact (Over.w (e.inv ≫ (Over.pullback f).map g)).trans (Over.w q').symm

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 230b8163683f57fd3cad70eef0b9f7eb069189c8b3fa789c7b27da17fb51eae7.
Definitions, hypotheses and universes are retained modulo native names. -/
