/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldGalois
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldPoint

/-! # Pointed Galois descent through actual finite field stages

A descended cover is pulled back once more to the finite field of definition
of its prescribed point. Connectedness of this particular pullback is reflected
from the original extension-valued cover; no unconditional field-invariance
claim for Galois covers is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

universe u

/-- The original finite cover remains Galois with unchanged order after a
particular base change whose further surjective pullback is connected. -/
private theorem galois_furtherStage {U V W : Scheme.{u}}
    [ConnectedSpace U] [ConnectedSpace V]
    (g : V ⟶ U) (v : W ⟶ V) [Surjective v]
    (Z : FiniteEtale U) [IsGalois Z]
    [ConnectedSpace ((baseChange (v ≫ g)).obj Z).obj.left] :
    IsGalois ((baseChange g).obj Z) ∧
      Nat.card (Aut ((baseChange g).obj Z)) = Nat.card (Aut Z) := by
  let ZF := (baseChange g).obj Z
  let e : ((baseChange (v ≫ g)).obj Z).obj.left ≅
      ((baseChange v).obj ZF).obj.left :=
    (forgetToScheme W).mapIso ((baseChangeComp g v).app Z)
  let : ConnectedSpace ((baseChange v).obj ZF).obj.left :=
    e.hom.surjective.connectedSpace e.hom.continuous
  let : ConnectedSpace (pullback ZF.obj.hom v : Scheme.{u}) :=
    inferInstanceAs (ConnectedSpace ((baseChange v).obj ZF).obj.left)
  let : ConnectedSpace ZF.obj.left :=
    (pullback.fst ZF.obj.hom v).surjective.connectedSpace (pullback.fst ZF.obj.hom v).continuous
  exact ⟨baseChange_isGalois_of_connected g Z, baseChange_card_aut_of_connected g Z⟩

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
  {U W : Scheme.{u}} (p : U ⟶ Spec (.of k))
  (v₀ : W ⟶ U) (w : W ⟶ Spec (.of Ω))
  (H : IsPullback v₀ w p (Spec.algebraMap k Ω))

/-- The single further-stage field. -/
abbrev pointField (t : Finset Ω) := FieldLimit.finiteField k Ω t

/-- The single further-stage base scheme. -/
abbrev pointBase (t : Finset Ω) : Scheme.{u} :=
  pullback p (Spec.algebraMap k (pointField k Ω t))

private theorem pointField_tower (t : Finset Ω) :
    Spec.algebraMap (pointField k Ω t) Ω ≫ Spec.algebraMap k (pointField k Ω t) =
      Spec.algebraMap k Ω := by
  rw [← Spec.map_comp]
  congr 1

/-- The original extension scheme maps to the native further-stage pullback. -/
def pointProjection (t : Finset Ω) : W ⟶ pointBase k Ω p t :=
  pullback.lift v₀ (w ≫ Spec.algebraMap (pointField k Ω t) Ω) (by
    rw [Category.assoc, pointField_tower]
    exact H.w)

@[reassoc] theorem pointProjection_fst (t : Finset Ω) :
    pointProjection k Ω p v₀ w H t ≫
      pullback.fst p (Spec.algebraMap k (pointField k Ω t)) = v₀ :=
  pullback.lift_fst _ _ _

@[reassoc] theorem pointProjection_snd (t : Finset Ω) :
    pointProjection k Ω p v₀ w H t ≫
      pullback.snd p (Spec.algebraMap k (pointField k Ω t)) =
        w ≫ Spec.algebraMap (pointField k Ω t) Ω := pullback.lift_snd _ _ _

/-- This original projection is an actual field-base-change square. -/
theorem pointProjection_isPullback (t : Finset Ω) :
    IsPullback (pointProjection k Ω p v₀ w H t) w
      (pullback.snd p (Spec.algebraMap k (pointField k Ω t)))
      (Spec.algebraMap (pointField k Ω t) Ω) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst p
    (Spec.algebraMap k (pointField k Ω t)))
    (h₂₂ := Spec.algebraMap k (pointField k Ω t))
  · rw [pointProjection_fst, pointField_tower]
    exact H
  · exact pointProjection_snd k Ω p v₀ w H t
  · exact IsPullback.of_hasPullback _ _

/-- The native reconstruction of the same cover across the further point field. -/
def pointCoverIso (t : Finset Ω) (Z : FiniteEtale U) :
    (baseChange (pointProjection k Ω p v₀ w H t)).obj
      ((baseChange (pullback.fst p (Spec.algebraMap k (pointField k Ω t)))).obj Z) ≅
      (baseChange v₀).obj Z :=
  ((baseChangeComp (pullback.fst p (Spec.algebraMap k (pointField k Ω t)))
    (pointProjection k Ω p v₀ w H t)).app Z).symm ≪≫
      eqToIso (congrArg (fun g => (baseChange g).obj Z)
        (pointProjection_fst k Ω p v₀ w H t))

local instance point_baseConnected [GeometricallyConnected p] (t : Finset Ω) :
    ConnectedSpace (pointBase k Ω p t) :=
  GeometricallyConnected.connectedSpace_of_subsingleton
    (pullback.snd p (Spec.algebraMap k (pointField k Ω t)))

local instance point_limitConnected [GeometricallyConnected p] :
    ConnectedSpace (pullback p (Spec.algebraMap k Ω) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p (Spec.algebraMap k Ω))

local instance point_stageConnected [GeometricallyConnected p] (s : Finset Ω) :
    ConnectedSpace (((FieldLimit.schemeDiagram k Ω p).obj (op s)).left) := by
  change ConnectedSpace
    (pullback (Spec.algebraMap k (FieldLimit.finiteField k Ω s)) p : Scheme.{u})
  exact GeometricallyConnected.connectedSpace_of_subsingleton
    (pullback.fst (Spec.algebraMap k (FieldLimit.finiteField k Ω s)) p)

variable [Algebra.IsAlgebraic k Ω]

include w H in
/-- A Galois cover with connected original extension has a rational lift at a
finite further field, on the same actual iterated cover and with unchanged order. -/
theorem exists_pointed_further_galois_stage
    [GeometricallyConnected p] [ConnectedSpace U]
    (Z : FiniteEtale U) [IsGalois Z]
    [ConnectedSpace ((baseChange v₀).obj Z).obj.left]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    (z : Spec (.of Ω) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = Spec.algebraMap k Ω ≫ x) :
    ∃ (t : Finset Ω),
      let F := pointField k Ω t
      let g := pullback.fst p (Spec.algebraMap k F)
      let ZF := (baseChange g).obj Z
      ∃ (xF : Spec (.of F) ⟶ pointBase k Ω p t) (zF : Spec (.of F) ⟶ ZF.obj.left),
        xF ≫ pullback.snd p (Spec.algebraMap k F) = 𝟙 _ ∧
        xF ≫ g = Spec.algebraMap k F ≫ x ∧
        zF ≫ ZF.obj.hom = xF ∧
        Spec.algebraMap F Ω ≫ (zF ≫ pullback.fst Z.obj.hom g) = z ∧
        IsGalois ZF ∧ Nat.card (Aut ZF) = Nat.card (Aut Z) := by
  obtain ⟨t, a, ha, he⟩ := exists_finite_field_point k Ω Z.obj.hom x z hz
  let F := pointField k Ω t
  let b := Spec.algebraMap k F
  let g : pointBase k Ω p t ⟶ U := pullback.fst p b
  let v := pointProjection k Ω p v₀ w H t
  let : ConnectedSpace U := GeometricallyConnected.connectedSpace_of_subsingleton p
  let : ConnectedSpace (pointBase k Ω p t) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p b)
  let : Surjective v := MorphismProperty.of_isPullback
    (pointProjection_isPullback k Ω p v₀ w H t).flip
    (inferInstanceAs (Surjective (Spec.algebraMap F Ω)))
  let : ConnectedSpace ((baseChange (v ≫ g)).obj Z).obj.left := by
    rw [pointProjection_fst]
    infer_instance
  obtain ⟨hG, hcard⟩ := galois_furtherStage g v Z
  let xF : Spec (.of F) ⟶ pointBase k Ω p t :=
    pullback.lift (b ≫ x) (𝟙 _) (by
      rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
  have hxF : xF ≫ g = b ≫ x := pullback.lift_fst _ _ _
  let zF : Spec (.of F) ⟶ ((baseChange g).obj Z).obj.left :=
    pullback.lift a xF (ha.trans hxF.symm)
  refine ⟨t, xF, zF, pullback.lift_snd _ _ _, hxF, pullback.lift_snd _ _ _, ?_, hG, hcard⟩
  have hzF : zF ≫ pullback.fst Z.obj.hom g = a := pullback.lift_fst _ _ _
  exact (congrArg (fun q => Spec.algebraMap F Ω ≫ q) hzF).trans he

omit [Algebra.IsAlgebraic k Ω] in
/-- The same iterated point-field base remains a native pullback of the original base. -/
theorem pointBase_original_isPullback
    {X : Scheme.{u}} (p₀ : X ⟶ Spec (.of k)) (s : Finset Ω)
    (t : Finset Ω) :
    let k₀ := FieldLimit.finiteField k Ω s
    let U₀ := ((FieldLimit.schemeDiagram k Ω p₀).obj (op s)).left
    let q₀ : U₀ ⟶ Spec (.of k₀) := pullback.fst (Spec.algebraMap k k₀) p₀
    let F := pointField k₀ Ω t
    IsPullback
      (pullback.fst q₀ (Spec.algebraMap k₀ F) ≫ pullback.snd (Spec.algebraMap k k₀) p₀)
      (pullback.snd q₀ (Spec.algebraMap k₀ F)) p₀ (Spec.algebraMap k F) := by
  dsimp only
  have h := (IsPullback.of_hasPullback
    (pullback.fst (Spec.algebraMap k (FieldLimit.finiteField k Ω s)) p₀)
    (Spec.algebraMap (FieldLimit.finiteField k Ω s)
      (pointField (FieldLimit.finiteField k Ω s) Ω t))).paste_horiz
        (IsPullback.of_hasPullback
          (Spec.algebraMap k (FieldLimit.finiteField k Ω s)) p₀).flip
  have he : Spec.algebraMap (FieldLimit.finiteField k Ω s)
      (pointField (FieldLimit.finiteField k Ω s) Ω t) ≫
      Spec.algebraMap k (FieldLimit.finiteField k Ω s) =
      Spec.algebraMap k (pointField (FieldLimit.finiteField k Ω s) Ω t) := by
    rw [← Spec.map_comp]
    congr 1
  exact he ▸ h

/-- An original pointed Galois cover over an algebraic extension descends
through two native finite field stages, preserving its order and prescribed point.
The second stage is the literal pullback of the first; no flattened cover is chosen. -/
theorem exists_qcqs_pointed_galois_cover
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (p₀ : X ⟶ Spec (.of k)) [GeometricallyConnected p₀]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ p₀ = 𝟙 _)
    (Y : FiniteEtale (pullback p₀ (Spec.algebraMap k Ω))) [IsGalois Y]
    (z : Spec (.of Ω) ⟶ Y.obj.left)
    (hz₁ : z ≫ Y.obj.hom ≫ pullback.fst p₀ (Spec.algebraMap k Ω) =
      Spec.algebraMap k Ω ≫ x)
    (hz₂ : z ≫ Y.obj.hom ≫ pullback.snd p₀ (Spec.algebraMap k Ω) = 𝟙 _) :
    ∃ (s : Finset Ω)
      (Z : FiniteEtale (((FieldLimit.schemeDiagram k Ω p₀).obj (op s)).left))
      (E : (baseChange (FieldLimit.fieldProjection k Ω p₀ (op s))).obj Z ≅ Y),
      IsGalois Z ∧ Nat.card (Aut Z) = Nat.card (Aut Y) ∧
      ∃ (t : Finset Ω),
        let k₀ := FieldLimit.finiteField k Ω s
        let q₀ := pullback.fst (Spec.algebraMap k k₀) p₀
        let F := pointField k₀ Ω t
        let g := pullback.fst q₀ (Spec.algebraMap k₀ F)
        let ZF := (baseChange g).obj Z
        ∃ (xF : Spec (.of F) ⟶ pointBase k₀ Ω q₀ t)
          (zF : Spec (.of F) ⟶ ZF.obj.left),
          Module.Finite k F ∧
          IsPullback (g ≫ pullback.snd (Spec.algebraMap k k₀) p₀)
            (pullback.snd q₀ (Spec.algebraMap k₀ F)) p₀ (Spec.algebraMap k F) ∧
          xF ≫ pullback.snd q₀ (Spec.algebraMap k₀ F) = 𝟙 _ ∧
          xF ≫ g ≫ pullback.snd (Spec.algebraMap k k₀) p₀ = Spec.algebraMap k F ≫ x ∧
          zF ≫ ZF.obj.hom = xF ∧
          Spec.algebraMap F Ω ≫ (zF ≫ pullback.fst Z.obj.hom g) =
            z ≫ E.inv.hom.left ≫ pullback.fst Z.obj.hom
              (FieldLimit.fieldProjection k Ω p₀ (op s)) ∧
          IsGalois ZF ∧ Nat.card (Aut ZF) = Nat.card (Aut Y) ∧
          Nonempty ((baseChange (pointProjection k₀ Ω q₀
            (FieldLimit.fieldProjection k Ω p₀ (op s))
            (pullback.snd p₀ (Spec.algebraMap k Ω))
            (fieldProjection_isPullback k Ω p₀ s) t)).obj ZF ≅ Y) := by
  obtain ⟨s, Z, hG, hcard, ⟨E⟩⟩ := exists_qcqs_galois_cover k Ω p₀ Y
  let k₀ := FieldLimit.finiteField k Ω s
  let U₀ := ((FieldLimit.schemeDiagram k Ω p₀).obj (op s)).left
  let q₀ : U₀ ⟶ Spec (.of k₀) := pullback.fst (Spec.algebraMap k k₀) p₀
  let u₀ : U₀ ⟶ X := pullback.snd (Spec.algebraMap k k₀) p₀
  let v₀ : pullback p₀ (Spec.algebraMap k Ω) ⟶ U₀ :=
    FieldLimit.fieldProjection k Ω p₀ (op s)
  let w := pullback.snd p₀ (Spec.algebraMap k Ω)
  let : GeometricallyConnected q₀ :=
    inferInstanceAs (GeometricallyConnected (pullback.fst (Spec.algebraMap k k₀) p₀))
  let : IsGalois Z := hG
  let : ConnectedSpace (pullback p₀ (Spec.algebraMap k Ω) : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton w
  let : ConnectedSpace Y.obj.left := Connectedness.connectedSpace_of_categoricalConnected Y
  let eY : ((baseChange v₀).obj Z).obj.left ≅ Y.obj.left :=
    (forgetToScheme (pullback p₀ (Spec.algebraMap k Ω))).mapIso E
  let : ConnectedSpace ((baseChange v₀).obj Z).obj.left :=
    eY.inv.surjective.connectedSpace eY.inv.continuous
  let x₀ : Spec (.of k₀) ⟶ pullback (Spec.algebraMap k k₀) p₀ :=
    pullback.lift (𝟙 _) (Spec.algebraMap k k₀ ≫ x) (by
      rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
  have hx₀ : x₀ ≫ q₀ = 𝟙 _ := pullback.lift_fst _ _ _
  have hx₀u : x₀ ≫ u₀ = Spec.algebraMap k k₀ ≫ x := pullback.lift_snd _ _ _
  let z₀ : Spec (.of Ω) ⟶ Z.obj.left := z ≫ E.inv.hom.left ≫ pullback.fst Z.obj.hom v₀
  have hpoint : (z ≫ Y.obj.hom) ≫ v₀ = Spec.algebraMap k₀ Ω ≫ x₀ := by
    have hv₁ : v₀ ≫ q₀ = w ≫ Spec.algebraMap k₀ Ω := fieldProjection_field k Ω p₀ s
    have hv₂ : v₀ ≫ u₀ = pullback.fst p₀ (Spec.algebraMap k Ω) :=
      FieldLimit.fieldProjection_base k Ω p₀ (op s)
    apply pullback.hom_ext
    · change ((z ≫ Y.obj.hom) ≫ v₀) ≫ q₀ = (Spec.algebraMap k₀ Ω ≫ x₀) ≫ q₀
      rw [Category.assoc, hv₁, ← Category.assoc, Category.assoc z, hz₂,
        Category.id_comp, Category.assoc, hx₀, Category.comp_id]
    · change ((z ≫ Y.obj.hom) ≫ v₀) ≫ u₀ = (Spec.algebraMap k₀ Ω ≫ x₀) ≫ u₀
      rw [Category.assoc, hv₂, Category.assoc z, hz₁, Category.assoc, hx₀u,
        ← Category.assoc, pointField_tower]
  have hz₀ : z₀ ≫ Z.obj.hom = Spec.algebraMap k₀ Ω ≫ x₀ := by
    have hE : E.inv.hom.left ≫ pullback.snd Z.obj.hom v₀ = Y.obj.hom := Over.w E.inv.hom
    have hsquare : (E.inv.hom.left ≫ pullback.fst Z.obj.hom v₀) ≫ Z.obj.hom =
        Y.obj.hom ≫ v₀ :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun a => E.inv.hom.left ≫ a)
          (pullback.condition (f := Z.obj.hom) (g := v₀))).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ v₀) hE)))
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => z ≫ a) hsquare).trans
        ((Category.assoc _ _ _).symm.trans hpoint))
  obtain ⟨t, xF, zF, hxF, hxFg, hzF, he, hGF, hcardF⟩ :=
    exists_pointed_further_galois_stage k₀ Ω q₀ v₀ w
      (fieldProjection_isPullback k Ω p₀ s) Z x₀ hx₀ z₀ hz₀
  refine ⟨s, Z, E, hG, hcard, t, xF, zF, ?_,
    pointBase_original_isPullback k Ω p₀ s t, hxF, ?_, hzF, he, hGF,
    hcardF.trans hcard, ?_⟩
  · exact Module.Finite.trans k₀ (pointField k₀ Ω t)
  · change xF ≫ pullback.fst q₀ (Spec.algebraMap k₀ (pointField k₀ Ω t)) ≫ u₀ =
      Spec.algebraMap k (pointField k₀ Ω t) ≫ x
    have htower : Spec.algebraMap k₀ (pointField k₀ Ω t) ≫ Spec.algebraMap k k₀ =
        Spec.algebraMap k (pointField k₀ Ω t) := by
      rw [← Spec.map_comp]
      congr 1
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ u₀) hxFg).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun a => Spec.algebraMap k₀ (pointField k₀ Ω t) ≫ a) hx₀u).trans
            ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ x) htower)))))
  · exact ⟨pointCoverIso k₀ Ω q₀ v₀ w
      (fieldProjection_isPullback k Ω p₀ s) t Z ≪≫ E⟩

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
