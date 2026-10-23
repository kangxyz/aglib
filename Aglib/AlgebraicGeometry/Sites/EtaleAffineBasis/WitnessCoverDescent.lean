/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteWitnessModels
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Diagrams
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Descent of finite covering witnesses with both original target triangles

Starting with a covering family modeled at a stage, descend its local maps
and both equality-witness triangles to a common refinement. The output family
is still an actual covering family, not merely a collection of local models.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

/-- Finite covering witnesses descend with their two target equations and
literal limit comparison, while retaining joint surjectivity. -/
theorem exists_covering_witness_models
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    {J : Type v} [Finite J] (Z : J → Over (D.obj i))
    [∀ j, QuasiCompact (Z j).hom] [∀ j, QuasiSeparated (Z j).hom]
    (hcover : ∀ x : D.obj i, ∃ j, ∃ y : (Z j).left, (Z j).hom y = x)
    (T U V : J → X.Etale)
    (a : ∀ j, D.obj i ⟶ (U j).left) (b : ∀ j, D.obj i ⟶ (V j).left)
    (ha : ∀ j, a j ≫ (U j).hom = r) (hb : ∀ j, b j ≫ (V j).hom = r)
    (p : ∀ j, T j ⟶ U j) (q : ∀ j, T j ⟶ V j)
    (s : ∀ j, pullback (c.π.app i) (Z j).hom ⟶ (T j).left)
    (hs : ∀ j, s j ≫ (T j).hom =
      pullback.snd (c.π.app i) (Z j).hom ≫ (Z j).hom ≫ r)
    (hp : ∀ j, s j ≫ (p j).left =
      pullback.snd (c.π.app i) (Z j).hom ≫ (Z j).hom ≫ a j)
    (hq : ∀ j, s j ≫ (q j).left =
      pullback.snd (c.π.app i) (Z j).hom ≫ (Z j).hom ≫ b j) :
    ∃ (k : Over i)
      (t : ∀ j, (Scheme.baseChangeDiagram D i (Z j).hom).obj k ⟶ (T j).left),
      (∀ j, t j ≫ (p j).left =
        pullback.snd (D.map k.hom) (Z j).hom ≫ (Z j).hom ≫ a j) ∧
      (∀ j, t j ≫ (q j).left =
        pullback.snd (D.map k.hom) (Z j).hom ≫ (Z j).hom ≫ b j) ∧
      (∀ j, (Scheme.baseChangeCone D c i (Z j).hom).π.app k ≫ t j = s j) ∧
      ∀ x : D.obj k.left, ∃ j,
        ∃ y : (pullback (D.map k.hom) (Z j).hom : Scheme),
          pullback.fst (D.map k.hom) (Z j).hom y = x := by
  let E (j : J) : Over i ⥤ Over X :=
    Over.post D ⋙ Over.pullback (Z j).hom ⋙ Over.map ((Z j).hom ≫ r)
  let e (j : J) : Cone (E j) :=
    (Over.pullback (Z j).hom ⋙ Over.map ((Z j).hom ≫ r)).mapCone
      ((Over.conePost D i).obj c)
  have he (j : J) : IsLimit ((Over.forget X).mapCone (e j)) :=
    Scheme.isLimitBaseChangeCone D c hc i (Z j).hom
  have (j : J) (k : Over i) : CompactSpace ((E j).obj k).left :=
    inferInstanceAs (CompactSpace ((Scheme.baseChangeDiagram D i (Z j).hom).obj k))
  have (j : J) (k : Over i) : QuasiSeparatedSpace ((E j).obj k).left :=
    inferInstanceAs (QuasiSeparatedSpace ((Scheme.baseChangeDiagram D i (Z j).hom).obj k))
  have (j : J) {k l : Over i} (f : k ⟶ l) : IsAffineHom ((E j).map f).left :=
    inferInstanceAs (IsAffineHom ((Scheme.baseChangeDiagram D i (Z j).hom).map f))
  let i₀ : Over i := Over.mk (𝟙 i)
  let A (j : J) : (E j).obj i₀ ⟶ Over.mk (U j).hom :=
    Over.homMk (pullback.snd (D.map i₀.hom) (Z j).hom ≫ (Z j).hom ≫ a j)
      ((Category.assoc _ _ _).trans
        (congrArg (fun z ↦ pullback.snd (D.map i₀.hom) (Z j).hom ≫ z)
          ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (Z j).hom ≫ z) (ha j)))))
  let B (j : J) : (E j).obj i₀ ⟶ Over.mk (V j).hom :=
    Over.homMk (pullback.snd (D.map i₀.hom) (Z j).hom ≫ (Z j).hom ≫ b j)
      ((Category.assoc _ _ _).trans
        (congrArg (fun z ↦ pullback.snd (D.map i₀.hom) (Z j).hom ≫ z)
          ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (Z j).hom ≫ z) (hb j)))))
  let S (j : J) : (e j).pt ⟶ Over.mk (T j).hom := Over.homMk (s j) (hs j)
  have hA (j : J) : S j ≫ (Etale.forget X).map (p j) = (e j).π.app i₀ ≫ A j := by
    apply Over.OverMorphism.ext
    have hw := Over.w ((Over.pullback (Z j).hom).map
      (((Over.conePost D i).obj c).π.app i₀))
    exact (hp j).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ (Z j).hom ≫ a j) hw)).symm
  have hB (j : J) : S j ≫ (Etale.forget X).map (q j) = (e j).π.app i₀ ≫ B j := by
    apply Over.OverMorphism.ext
    have hw := Over.w ((Over.pullback (Z j).hom).map
      (((Over.conePost D i).obj c).π.app i₀))
    exact (hq j).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ (Z j).hom ≫ b j) hw)).symm
  obtain ⟨k, f, t, htp, htq, hts⟩ :=
    exists_common_etale_witness_models E e he T U V i₀ A B p q S hA hB
  refine ⟨k, fun j ↦ (t j).left, ?_, ?_, ?_, ?_⟩
  · intro j
    have ht := congrArg (fun z ↦ z.left) (htp j)
    have hw := Over.w ((Over.pullback (Z j).hom).map ((Over.post D).map f))
    exact ht.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ (Z j).hom ≫ a j) hw))
  · intro j
    have ht := congrArg (fun z ↦ z.left) (htq j)
    have hw := Over.w ((Over.pullback (Z j).hom).map ((Over.post D).map f))
    exact ht.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ (Z j).hom ≫ b j) hw))
  · intro j
    exact congrArg (fun z ↦ z.left) (hts j)
  · intro x
    obtain ⟨j, y, hy⟩ := hcover (D.map k.hom x)
    refine ⟨j, ?_⟩
    have hx : x ∈ Set.range (pullback.fst (D.map k.hom) (Z j).hom) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨y, hy⟩
    exact hx

end AlgebraicGeometry.Scheme.EtaleAffineBasis
