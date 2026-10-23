/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineSchemeSectionEquality

/-! # A common stage for finitely many equalities of original representatives -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

private lemma transport_equality
    {X S : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) (U V : X.Etale)
    {f f' : S ⟶ X} {a a' : S ⟶ U.left} {b b' : S ⟶ V.left}
    (ha : a ≫ U.hom = f) (hb : b ≫ V.hom = f)
    (ha' : a' ≫ U.hom = f') (hb' : b' ≫ V.hom = f')
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (hf : f = f') (hA : a = a') (hB : b = b')
    (h : etaleRepresentativeSection F (Over.mk f) U (Over.homMk a ha) s =
      etaleRepresentativeSection F (Over.mk f) V (Over.homMk b hb) t) :
    etaleRepresentativeSection F (Over.mk f') U (Over.homMk a' ha') s =
      etaleRepresentativeSection F (Over.mk f') V (Over.homMk b' hb') t := by
  cases hf
  cases hA
  cases hB
  exact h

/-- Finite families of original representative equalities on affine limits
hold at one common stage. In gluing, the finite index is the set of pairs of
charts; the diagrams are their actual overlaps. -/
theorem exists_common_affineScheme_representatives_eventually_equal
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {J : Type v} [Finite J] (D : J → I ⥤ Scheme.{u})
    (c : ∀ j, Cone (D j)) (hc : ∀ j, IsLimit (c j))
    [∀ j i, IsAffine ((D j).obj i)]
    (i : I) {X : Scheme.{u}} (r : ∀ j, (D j).obj i ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (U V : J → X.Etale)
    (a : ∀ j, (D j).obj i ⟶ (U j).left)
    (b : ∀ j, (D j).obj i ⟶ (V j).left)
    (ha : ∀ j, a j ≫ (U j).hom = r j)
    (hb : ∀ j, b j ≫ (V j).hom = r j)
    (s : ∀ j, F.obj.obj (op (U j))) (t : ∀ j, F.obj.obj (op (V j)))
    (h : ∀ j,
      etaleRepresentativeSection F (Over.mk ((c j).π.app i ≫ r j)) (U j)
        (Over.homMk ((c j).π.app i ≫ a j) ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ (c j).π.app i ≫ z) (ha j)))) (s j) =
      etaleRepresentativeSection F (Over.mk ((c j).π.app i ≫ r j)) (V j)
        (Over.homMk ((c j).π.app i ≫ b j) ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ (c j).π.app i ≫ z) (hb j)))) (t j)) :
    ∃ (k : I) (q : k ⟶ i), ∀ j,
      etaleRepresentativeSection F (Over.mk ((D j).map q ≫ r j)) (U j)
        (Over.homMk ((D j).map q ≫ a j) ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ (D j).map q ≫ z) (ha j)))) (s j) =
      etaleRepresentativeSection F (Over.mk ((D j).map q ≫ r j)) (V j)
        (Over.homMk ((D j).map q ≫ b j) ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ (D j).map q ≫ z) (hb j)))) (t j) := by
  classical
  choose k q hq using fun j ↦ exists_affineScheme_representatives_eventually_equal
    (D j) (c j) (hc j) i (r j) F (U j) (V j) (a j) (b j)
      (ha j) (hb j) (s j) (t j) (h j)
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨l, w, v, hv⟩ := IsCofiltered.wideCospan q
  refine ⟨l, w, fun j ↦ ?_⟩
  let A : Over.mk ((D j).map (q j) ≫ r j) ⟶ (Etale.forget X).obj (U j) :=
    Over.homMk ((D j).map (q j) ≫ a j)
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (D j).map (q j) ≫ z) (ha j)))
  let B : Over.mk ((D j).map (q j) ≫ r j) ⟶ (Etale.forget X).obj (V j) :=
    Over.homMk ((D j).map (q j) ≫ b j)
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (D j).map (q j) ≫ z) (hb j)))
  let g : Over.mk ((D j).map (v j) ≫ ((D j).map (q j) ≫ r j)) ⟶
      Over.mk ((D j).map (q j) ≫ r j) := Over.homMk ((D j).map (v j))
  have heq := (etaleRepresentativeSection_restrict F g (U j) A (s j)).symm.trans
    ((congrArg ((pullbackSectionsFunctor F).map g.op) (hq j)).trans
      (etaleRepresentativeSection_restrict F g (V j) B (t j)))
  have hw {T : Scheme.{u}} (z : (D j).obj i ⟶ T) :
      (D j).map (v j) ≫ ((D j).map (q j) ≫ z) = (D j).map w ≫ z :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ z) ((D j).map_comp (v j) (q j)).symm).trans
        (congrArg (fun k ↦ (D j).map k ≫ z) (hv j)))
  exact transport_equality F (U j) (V j) (Over.w (g ≫ A)) (Over.w (g ≫ B))
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (D j).map w ≫ z) (ha j)))
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (D j).map w ≫ z) (hb j)))
    (s j) (t j) (hw (r j)) (hw (a j)) (hw (b j)) heq

end AlgebraicGeometry.Scheme.EtaleAffineBasis
