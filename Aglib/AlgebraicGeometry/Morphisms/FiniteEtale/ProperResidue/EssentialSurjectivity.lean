/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Graph
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperResidue
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Fullness from universal essential surjectivity on proper closed fibres

The graph of a closed-fibre morphism is lifted as an actual finite etale cover
of the product. Reflection of isomorphisms makes its first projection invertible.
The hypothesis is essential surjectivity for every proper scheme over the same
local ring; it is not a henselian comparison theorem by itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.ProperResidue

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem baseChange_essSurj_of_isIso {Y S : Scheme.{u}} (i : S ⟶ Y) [IsIso i] :
    (baseChange i).EssSurj := by
  let e : baseChange (inv i) ⋙ baseChange i ≅ 𝟭 (FiniteEtale S) :=
    (baseChangeComp (inv i) i).symm ≪≫
      eqToIso (congrArg baseChange (IsIso.hom_inv_id i)) ≪≫ baseChangeId S
  exact ⟨fun C ↦ ⟨(baseChange (inv i)).obj C, ⟨e.app C⟩⟩⟩

/-- Essential surjectivity over a cover lifts any arrow into its restriction,
with the actual arrow retained in the comparison equation. -/
theorem exists_arrow_lift_of_essSurj {Y S : Scheme.{u}} (i : S ⟶ Y)
    (P : FiniteEtale Y) [(baseChange (pullback.fst P.obj.hom i)).EssSurj]
    {T : FiniteEtale S} (m : T ⟶ (baseChange i).obj P) :
    ∃ (W : FiniteEtale Y) (j : W ⟶ P)
      (e : T ≅ (baseChange i).obj W),
      e.hom ≫ (baseChange i).map j = m := by
  let : IsFinite m.hom.left := Connectedness.hom_isFinite m
  let : Etale m.hom.left := Connectedness.hom_etale m
  let G := baseChange (pullback.fst P.obj.hom i)
  let M : FiniteEtale (pullback P.obj.hom i) := mk m.hom.left
  let Q := G.objPreimage M
  let d := G.objObjPreimageIso M
  let W : FiniteEtale Y := mk (Q.obj.hom ≫ P.obj.hom)
  let j : W ⟶ P := ObjectProperty.homMk (Over.homMk Q.obj.hom rfl)
  let b := pullbackRightPullbackFstIso P.obj.hom i Q.obj.hom
  have hb₁ : b.hom ≫ pullback.fst W.obj.hom i =
      pullback.fst Q.obj.hom (pullback.fst P.obj.hom i) :=
    pullbackRightPullbackFstIso_hom_fst P.obj.hom i Q.obj.hom
  have hb₂ : b.hom ≫ pullback.snd W.obj.hom i =
      pullback.snd Q.obj.hom (pullback.fst P.obj.hom i) ≫ pullback.snd P.obj.hom i :=
    pullbackRightPullbackFstIso_hom_snd P.obj.hom i Q.obj.hom
  have hj : j.hom.left = Q.obj.hom := rfl
  let eScheme : T.obj.left ≅ ((baseChange i).obj W).obj.left :=
    ((forgetToScheme _).mapIso d).symm ≪≫ b
  have hd : d.inv.hom.left ≫ pullback.snd Q.obj.hom (pullback.fst P.obj.hom i) =
      m.hom.left := Over.w d.inv.hom
  have heS : eScheme.hom ≫ pullback.snd W.obj.hom i = T.obj.hom := by
    change (d.inv.hom.left ≫ b.hom) ≫ pullback.snd W.obj.hom i = _
    rw [Category.assoc, hb₂, ← Category.assoc, hd]
    exact Over.w m.hom
  let e : T ≅ (baseChange i).obj W :=
    ObjectProperty.isoMk _ (Over.isoMk eScheme heS)
  refine ⟨W, j, e, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change (d.inv.hom.left ≫ b.hom) ≫ ((baseChange i).map j).hom.left = m.hom.left
  apply pullback.hom_ext (f := P.obj.hom) (g := i)
  · calc
      _ = d.inv.hom.left ≫ (b.hom ≫ pullback.fst W.obj.hom i) ≫ Q.obj.hom := by
        simp only [Category.assoc, baseChange_map_first, hj]
      _ = d.inv.hom.left ≫
          pullback.fst Q.obj.hom (pullback.fst P.obj.hom i) ≫ Q.obj.hom := by
        rw [hb₁]
      _ = d.inv.hom.left ≫
          pullback.snd Q.obj.hom (pullback.fst P.obj.hom i) ≫
            pullback.fst P.obj.hom i := by rw [pullback.condition]
      _ = m.hom.left ≫ pullback.fst P.obj.hom i := by rw [← Category.assoc, hd]
  · rw [Category.assoc, baseChange_map_second]
    exact heS.trans (Over.w m.hom).symm

section LocalBase

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Universal essential surjectivity on proper schemes over a local base
implies fullness of the original closed-fibre pullback functor. -/
theorem closedFiber_baseChange_full_of_universal_essSurj
    (h : ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of R)), IsProper f →
      (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).EssSurj)
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) [IsProper π] :
    (baseChange (pullback.fst π (LocalRing.residueSpecMap R))).Full where
  map_surjective {C D} φ := by
    let i := LocalRing.ResidueFiber.projection π
    let F := baseChange i
    let P : FiniteEtale Y := productCover C D
    let : IsFinite P.obj.hom := P.property.1
    let : IsProper P.obj.hom := inferInstance
    let : IsProper (P.obj.hom ≫ π) := inferInstance
    let a := pullbackRightPullbackFstIso π (LocalRing.residueSpecMap R) P.obj.hom
    let ip := pullback.fst (P.obj.hom ≫ π) (LocalRing.residueSpecMap R)
    let : (baseChange ip).EssSurj := h _ (P.obj.hom ≫ π) inferInstance
    let : (baseChange a.hom).EssSurj := baseChange_essSurj_of_isIso _
    have hc : a.hom ≫ ip = pullback.fst P.obj.hom i :=
      pullbackRightPullbackFstIso_hom_fst _ _ _
    let : (baseChange (pullback.fst P.obj.hom i)).EssSurj := by
      rw [← hc]
      exact Functor.essSurj_of_iso (baseChangeComp ip a.hom).symm
    let m : F.obj C ⟶ F.obj P := residueGraph i φ
    obtain ⟨W, j, e, he⟩ := exists_arrow_lift_of_essSurj i P m
    let p : W ⟶ C := j ≫ productFirst C D
    have hep : e.hom ≫ F.map p = 𝟙 (F.obj C) := by
      rw [Functor.map_comp, ← Category.assoc, he]
      exact residueGraph_first i φ
    have hpmap : F.map p = e.inv := by
      apply (cancel_epi e.hom).mp
      rw [hep, Iso.hom_inv_id]
    have : IsIso (F.map p) := by rw [hpmap]; infer_instance
    have : IsIso p := isIso_of_reflects_iso p F
    have hinv : F.map (inv p) = e.hom := by
      apply (cancel_mono (F.map p)).mp
      have hl : F.map (inv p) ≫ F.map p = 𝟙 _ := by
        rw [← Functor.map_comp, IsIso.inv_hom_id]
        exact F.map_id C
      exact hl.trans hep.symm
    refine ⟨inv p ≫ j ≫ productSecond C D, ?_⟩
    change F.map (inv p ≫ j ≫ productSecond C D) = φ
    rw [Functor.map_comp, Functor.map_comp, hinv, ← Category.assoc, he]
    exact residueGraph_second i φ

/-- Universal essential surjectivity, together with the unconditional closed-fibre
faithfulness theorem, makes the original functor an equivalence. -/
theorem closedFiber_baseChange_isEquivalence_of_universal_essSurj
    (h : ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of R)), IsProper f →
      (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).EssSurj)
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) [IsProper π] :
    (baseChange (pullback.fst π (LocalRing.residueSpecMap R))).IsEquivalence := by
  let : (baseChange (pullback.fst π (LocalRing.residueSpecMap R))).EssSurj :=
    h Y π inferInstance
  let : (baseChange (pullback.fst π (LocalRing.residueSpecMap R))).Full :=
    closedFiber_baseChange_full_of_universal_essSurj h π
  exact { }

end LocalBase

end AlgebraicGeometry.Scheme.FiniteEtale.ProperResidue
