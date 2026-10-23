/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteRepresentativeEqualities
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Diagrams

/-! # Eventual representative equality on finite actual base-change families -/

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

/-- Equality on finitely many actual limit base changes holds on one common
stage base change. The affine sources may in particular be the pairwise
overlaps of a finite affine covering family. -/
theorem exists_common_baseChange_representatives_eventually_equal
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) {X : Scheme.{u}}
    (r : D.obj i ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} [Finite J] (Z : J → Over (D.obj i))
    [∀ j, IsAffine (Z j).left] (U V : J → X.Etale)
    (a : ∀ j, (Z j).left ⟶ (U j).left) (b : ∀ j, (Z j).left ⟶ (V j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (Z j).hom ≫ r)
    (hb : ∀ j, b j ≫ (V j).hom = (Z j).hom ≫ r)
    (s : ∀ j, F.obj.obj (op (U j))) (t : ∀ j, F.obj.obj (op (V j)))
    (h : ∀ j,
      etaleRepresentativeSection F
        (Over.mk (pullback.snd (c.π.app i) (Z j).hom ≫ (Z j).hom ≫ r)) (U j)
        (Over.homMk (pullback.snd (c.π.app i) (Z j).hom ≫ a j)
          ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ pullback.snd (c.π.app i) (Z j).hom ≫ z) (ha j)))) (s j) =
      etaleRepresentativeSection F
        (Over.mk (pullback.snd (c.π.app i) (Z j).hom ≫ (Z j).hom ≫ r)) (V j)
        (Over.homMk (pullback.snd (c.π.app i) (Z j).hom ≫ b j)
          ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ pullback.snd (c.π.app i) (Z j).hom ≫ z) (hb j)))) (t j)) :
    ∃ k : Over i, ∀ j,
      etaleRepresentativeSection F
        (Over.mk (pullback.snd (D.map k.hom) (Z j).hom ≫ (Z j).hom ≫ r)) (U j)
        (Over.homMk (pullback.snd (D.map k.hom) (Z j).hom ≫ a j)
          ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ pullback.snd (D.map k.hom) (Z j).hom ≫ z) (ha j)))) (s j) =
      etaleRepresentativeSection F
        (Over.mk (pullback.snd (D.map k.hom) (Z j).hom ≫ (Z j).hom ≫ r)) (V j)
        (Over.homMk (pullback.snd (D.map k.hom) (Z j).hom ≫ b j)
          ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ pullback.snd (D.map k.hom) (Z j).hom ≫ z) (hb j)))) (t j) := by
  let E (j : J) := Scheme.baseChangeDiagram D i (Z j).hom
  let e (j : J) := Scheme.baseChangeCone D c i (Z j).hom
  have he (j : J) : IsLimit (e j) := Scheme.isLimitBaseChangeCone D c hc i (Z j).hom
  have (j : J) (k : Over i) : IsAffine ((E j).obj k) :=
    inferInstanceAs (IsAffine (pullback (D.map k.hom) (Z j).hom))
  let i₀ : Over i := Over.mk (𝟙 i)
  let p (j : J) := pullback.snd (D.map i₀.hom) (Z j).hom
  let R (j : J) := p j ≫ (Z j).hom ≫ r
  let A (j : J) := p j ≫ a j
  let B (j : J) := p j ≫ b j
  have hA (j : J) : A j ≫ (U j).hom = R j :=
    (Category.assoc _ _ _).trans (congrArg (fun z ↦ p j ≫ z) (ha j))
  have hB (j : J) : B j ≫ (V j).hom = R j :=
    (Category.assoc _ _ _).trans (congrArg (fun z ↦ p j ≫ z) (hb j))
  have hlimit (j : J) {T : Scheme.{u}} (z : (Z j).left ⟶ T) :
      (e j).π.app i₀ ≫ (p j ≫ z) = pullback.snd (c.π.app i) (Z j).hom ≫ z :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun w ↦ w ≫ z) (Over.w ((Over.pullback (Z j).hom).map
        (((Over.conePost D i).obj c).π.app i₀))))
  have h' (j : J) := transport_equality F (U j) (V j)
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ pullback.snd (c.π.app i) (Z j).hom ≫ z) (ha j)))
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ pullback.snd (c.π.app i) (Z j).hom ≫ z) (hb j)))
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (e j).π.app i₀ ≫ z) (hA j)))
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (e j).π.app i₀ ≫ z) (hB j)))
    (s j) (t j) (hlimit j ((Z j).hom ≫ r)).symm
      (hlimit j (a j)).symm (hlimit j (b j)).symm (h j)
  obtain ⟨k, q, hq⟩ := exists_common_affineScheme_representatives_eventually_equal
    E e he i₀ R F U V A B hA hB s t h'
  refine ⟨k, fun j ↦ ?_⟩
  have hstage {T : Scheme.{u}} (z : (Z j).left ⟶ T) :
      (E j).map q ≫ (p j ≫ z) = pullback.snd (D.map k.hom) (Z j).hom ≫ z :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun w ↦ w ≫ z)
        (Over.w ((Over.pullback (Z j).hom).map ((Over.post D).map q))))
  exact transport_equality F (U j) (V j)
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (E j).map q ≫ z) (hA j)))
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (E j).map q ≫ z) (hB j)))
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ pullback.snd (D.map k.hom) (Z j).hom ≫ z) (ha j)))
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ pullback.snd (D.map k.hom) (Z j).hom ≫ z) (hb j)))
    (s j) (t j) (hstage ((Z j).hom ≫ r)) (hstage (a j)) (hstage (b j)) (hq j)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
