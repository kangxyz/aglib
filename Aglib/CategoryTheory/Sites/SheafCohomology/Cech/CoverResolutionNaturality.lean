/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.CoverResolution

/-!
# Naturality of free abelian Čech resolutions

A commuting square of set-valued presheaf maps induces the actual maps on fibre
tuples, free complexes and sheafified nonpositive resolutions. The maps commute
with the original free-target augmentations. Tuple cochains, their literal
primitives and their degree-two derived roofs retain these same maps and signs.
No limits or chosen natural splitting in the site category are required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped Simplicial

universe u v w

namespace CategoryTheory.Presheaf.Cech

variable {C : Type u} [Category.{v} C]

section ArrowSquareNaturality

variable {F₁ G₁ F₂ G₂ : Cᵒᵖ ⥤ Type w} {f₁ : F₁ ⟶ G₁} {f₂ : F₂ ⟶ G₂}
    (sq : Arrow.mk f₁ ⟶ Arrow.mk f₂)

/-- An actual arrow square maps a tuple by its two original vertical maps. -/
def tupleMap (n : ℕ) : tuplePresheaf f₁ n ⟶ tuplePresheaf f₂ n where
  app U := ↾fun a => ⟨sq.right.app U a.1, fun i =>
    ⟨sq.left.app U (a.2 i).1, by
      have h := ConcreteCategory.congr_hom (NatTrans.congr_app sq.w U) (a.2 i).1
      change f₂.app U (sq.left.app U (a.2 i).1) = sq.right.app U a.1
      change f₂.app U (sq.left.app U (a.2 i).1) =
        sq.right.app U (f₁.app U (a.2 i).1) at h
      exact h.trans (congrArg (sq.right.app U) (a.2 i).2)⟩⟩
  naturality U V g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply tuple_ext
    · exact NatTrans.naturality_apply sq.right g a.1
    · intro i
      exact NatTrans.naturality_apply sq.left g (a.2 i).1

/-- The literal presheaf Cech nerve is functorial in commuting arrow squares. -/
def nerveMap : nerve f₁ ⟶ nerve f₂ where
  app n := tupleMap sq n.unop.len
  naturality _ _ _ := by ext U a; rfl

/-- Functoriality retains the actual target augmentation. -/
def augmentedNerveMap : augmentedNerve f₁ ⟶ augmentedNerve f₂ where
  left := nerveMap sq
  right := sq.right
  w := by ext n U a; rfl

/-- The map of the actual free abelian face complexes. -/
def freeComplexMap : freeComplex f₁ ⟶ freeComplex f₂ :=
  AlgebraicTopology.AlternatingFaceMapComplex.map
    (((SimplicialObject.whiskering _ _).obj freeFunctor).map (nerveMap sq))

/-- The original free augmentations commute with the square's original target map. -/
theorem freeAugmentation_naturality :
    freeComplexMap sq ≫ freeAugmentation f₂ = freeAugmentation f₁ ≫
      (ChainComplex.single₀ _).map (whiskerRight sq.right AddCommGrpCat.free) := by
  exact AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality
    (((SimplicialObject.Augmented.whiskering _ _).obj freeFunctor).map
      (augmentedNerveMap sq))

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- Exact sheafification maps the actual free Cech complexes and the same arrow square. -/
def sheafComplexMap : sheafComplex f₁ J ⟶ sheafComplex f₂ J :=
  ((presheafToSheaf J AddCommGrpCat).mapHomologicalComplex _).map (freeComplexMap sq)

/-- The map on the two original free target sheaves. -/
def targetMap : (presheafToSheaf J AddCommGrpCat).obj (G₁ ⋙ AddCommGrpCat.free) ⟶
    (presheafToSheaf J AddCommGrpCat).obj (G₂ ⋙ AddCommGrpCat.free) :=
  (presheafToSheaf J AddCommGrpCat).map (whiskerRight sq.right AddCommGrpCat.free)

set_option backward.isDefEq.respectTransparency false in
/-- The original sheaf augmentations commute with their original target maps. -/
theorem sheafAugmentation_naturality :
    sheafComplexMap sq J ≫ sheafAugmentation f₂ J =
      sheafAugmentation f₁ J ≫ (ChainComplex.single₀ _).map (targetMap sq J) := by
  let S := presheafToSheaf J AddCommGrpCat.{w}
  have h₂ := (HomologicalComplex.singleMapHomologicalComplex S (.down ℕ) 0).hom.naturality
    (whiskerRight sq.right AddCommGrpCat.free)
  unfold sheafComplexMap sheafAugmentation targetMap
  rw [← Category.assoc, ← Functor.map_comp, freeAugmentation_naturality,
    Functor.map_comp, Category.assoc]
  erw [h₂]
  exact (Category.assoc _ _ _).symm

/-- The actual map on the nonpositive integer-indexed Cech resolutions. -/
def resolutionMap : resolution f₁ J ⟶ resolution f₂ J :=
  HomologicalComplex.extendMap (sheafComplexMap sq J) ComplexShape.embeddingDownNat

/-- The native single-complex extension comparison is natural in its coefficient map. -/
private theorem extendSingle_naturality {A : Type*} [Category* A]
    [HasZeroObject A] [HasZeroMorphisms A] {ι ι' : Type*}
    [DecidableEq ι] [DecidableEq ι'] {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') {i : ι} {i' : ι'} (hi : e.f i = i')
    {X Y : A} (g : X ⟶ Y) :
    HomologicalComplex.extendMap ((HomologicalComplex.single A c i).map g) e ≫
        (HomologicalComplex.extendSingleIso e Y i i' hi).hom =
      (HomologicalComplex.extendSingleIso e X i i' hi).hom ≫
        (HomologicalComplex.single A c' i').map g := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ e hi,
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The resolution map commutes with both original augmentations, not merely their classes. -/
theorem resolutionAugmentation_naturality :
    resolutionMap sq J ≫ resolutionAugmentation f₂ J =
      resolutionAugmentation f₁ J ≫
        (CochainComplex.singleFunctor _ 0).map (targetMap sq J) := by
  unfold resolutionMap resolutionAugmentation
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    sheafAugmentation_naturality, HomologicalComplex.extendMap_comp, Category.assoc]
  erw [extendSingle_naturality (i := (0 : ℕ)) (i' := (0 : ℤ))
    ComplexShape.embeddingDownNat rfl (targetMap sq J)]
  exact (Category.assoc _ _ _).symm

/-- In every nonpositive degree, the map uses the original map of free tuple sheaves. -/
theorem resolutionMap_f_neg (n : ℕ) :
    (resolutionMap sq J).f (-(n : ℤ)) =
      (resolutionTermIso f₁ J n).hom ≫
        (presheafToSheaf J AddCommGrpCat).map
          (whiskerRight (tupleMap sq n) AddCommGrpCat.free) ≫
            (resolutionTermIso f₂ J n).inv :=
  HomologicalComplex.extendMap_f (sheafComplexMap sq J)
    ComplexShape.embeddingDownNat rfl


/-- Every literal differential identity is preserved by the actual resolution map. -/
theorem resolutionMap_precomp_differential_eq {A : Sheaf J AddCommGrpCat.{w}}
    {i j : ℤ} (p : (resolution f₂ J).X j ⟶ A) (c : (resolution f₂ J).X i ⟶ A)
    (hp : (resolution f₂ J).d i j ≫ p = c) :
    (resolution f₁ J).d i j ≫ ((resolutionMap sq J).f j ≫ p) =
      (resolutionMap sq J).f i ≫ c := by
  rw [← HomologicalComplex.Hom.comm_assoc, hp]

end ArrowSquareNaturality

section TupleLiftNaturality

variable {F₁ G₁ F₂ G₂ : Cᵒᵖ ⥤ Type w} {f₁ : F₁ ⟶ G₁} {f₂ : F₂ ⟶ G₂}
    (sq : Arrow.mk f₁ ⟶ Arrow.mk f₂)
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- The two actual adjunctions preserve precomposition by the original tuple map. -/
theorem tupleLift_precomp {n : ℕ} {A : Sheaf J AddCommGrpCat.{w}}
    (c : tuplePresheaf f₂ n ⟶ A.obj ⋙ forget AddCommGrpCat) :
    (presheafToSheaf J AddCommGrpCat).map
        (whiskerRight (tupleMap sq n) AddCommGrpCat.free) ≫ tupleLift f₂ J c =
      tupleLift f₁ J (tupleMap sq n ≫ c) := by
  dsimp only [tupleLift, tupleSectionsEquiv, Equiv.symm_trans_apply]
  erw [(AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left_symm
    (tupleMap sq n) c]
  exact ((sheafificationAdjunction J AddCommGrpCat).homEquiv_naturality_left_symm
    (whiskerRight (tupleMap sq n) AddCommGrpCat.free)
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ A.obj).symm c)).symm

/-- Restriction of a natural tuple cochain uses the actual resolution map in every degree. -/
theorem resolutionTupleLift_precomp {n : ℕ} {A : Sheaf J AddCommGrpCat.{w}}
    (c : tuplePresheaf f₂ n ⟶ A.obj ⋙ forget AddCommGrpCat) :
    (resolutionMap sq J).f (-(n : ℤ)) ≫ resolutionTupleLift f₂ J c =
      resolutionTupleLift f₁ J (tupleMap sq n ≫ c) := by
  rw [resolutionMap_f_neg]
  unfold resolutionTupleLift
  simp only [Category.assoc, Iso.inv_hom_id_assoc, tupleLift_precomp]

/-- An alternating tuple identity gives the literal differential identity after sheafification. -/
theorem tupleLift_differential_eq {n : ℕ} {A : Sheaf J AddCommGrpCat.{w}}
    (p : tuplePresheaf f₁ n ⟶ A.obj ⋙ forget AddCommGrpCat)
    (c : tuplePresheaf f₁ (n + 1) ⟶ A.obj ⋙ forget AddCommGrpCat)
    (h : ∀ (U : Cᵒᵖ) (a : Tuple f₁ (n + 1) U),
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        p.app U (tupleReindex f₁ i.succAbove a) = c.app U a) :
    (sheafComplex f₁ J).d (n + 1) n ≫ tupleLift f₁ J p = tupleLift f₁ J c := by
  apply (tupleSectionsEquiv f₁ J (n + 1) A).injective
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro a
  change (tupleSectionsEquiv f₁ J (n + 1) A
    ((sheafComplex f₁ J).d (n + 1) n ≫ tupleLift f₁ J p)).app U a = _
  rw [tupleSectionsEquiv_d f₁ J n A (tupleLift f₁ J p) U a]
  simpa only [tupleLift, Equiv.apply_symm_apply] using h U a


/-- A literal alternating primitive identity remains the same identity in cochain degrees. -/
theorem resolutionTupleLift_differential_eq {n : ℕ} {A : Sheaf J AddCommGrpCat.{w}}
    (p : tuplePresheaf f₁ n ⟶ A.obj ⋙ forget AddCommGrpCat)
    (c : tuplePresheaf f₁ (n + 1) ⟶ A.obj ⋙ forget AddCommGrpCat)
    (h : ∀ (U : Cᵒᵖ) (a : Tuple f₁ (n + 1) U),
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        p.app U (tupleReindex f₁ i.succAbove a) = c.app U a) :
    (resolution f₁ J).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
        resolutionTupleLift f₁ J p = resolutionTupleLift f₁ J c := by
  let d : (presheafToSheaf J AddCommGrpCat).obj
      (tuplePresheaf f₁ (n + 1) ⋙ AddCommGrpCat.free) ⟶
      (presheafToSheaf J AddCommGrpCat).obj
        (tuplePresheaf f₁ n ⋙ AddCommGrpCat.free) := (sheafComplex f₁ J).d (n + 1) n
  have hd : (resolution f₁ J).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (resolutionTermIso f₁ J (n + 1)).hom ≫ d ≫ (resolutionTermIso f₁ J n).inv :=
    resolution_d_term f₁ J n
  have hdc : d ≫ tupleLift f₁ J p = tupleLift f₁ J c :=
    tupleLift_differential_eq J p c h
  rw [hd]
  change ((resolutionTermIso f₁ J (n + 1)).hom ≫ d ≫ (resolutionTermIso f₁ J n).inv) ≫
      ((resolutionTermIso f₁ J n).hom ≫ tupleLift f₁ J p) =
    (resolutionTermIso f₁ J (n + 1)).hom ≫ tupleLift f₁ J c
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hdc]

end TupleLiftNaturality


section DegreeTwoCocycleNaturality

variable {F₁ G₁ F₂ G₂ : Cᵒᵖ ⥤ Type (max u v)} {f₁ : F₁ ⟶ G₁} {f₂ : F₂ ⟶ G₂}
    (sq : Arrow.mk f₁ ⟶ Arrow.mk f₂)
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v}]

open CochainComplex CochainComplex.HomComplex

/-- The degree-two cocycle uses the original chain map under precomposition. -/
theorem degreeTwoCocycle_precomp {A : Sheaf J AddCommGrpCat.{max u v}}
    (c : (resolution f₂ J).X (-2) ⟶ A)
    (hc : (resolution f₂ J).d (-3) (-2) ≫ c = 0) :
    degreeTwoCocycle f₁ J ((resolutionMap sq J).f (-2) ≫ c)
        (by simp only [← HomologicalComplex.Hom.comm_assoc, hc, comp_zero]) =
      (degreeTwoCocycle f₂ J c hc).precomp (resolutionMap sq J) :=
  Cocycle.toSingleMk_precomp c (by norm_num) (-3) (by norm_num) hc (resolutionMap sq J)

/-- A null-homotopy pulls back along the original resolution map. -/
def degreeTwoCocycle_nullHomotopy_precomp {A : Sheaf J AddCommGrpCat.{max u v}}
    (c : (resolution f₂ J).X (-2) ⟶ A)
    (hc : (resolution f₂ J).d (-3) (-2) ≫ c = 0)
    (h : Homotopy (Cocycle.equivHomShift.symm (degreeTwoCocycle f₂ J c hc)) 0) :
    Homotopy
      (Cocycle.equivHomShift.symm
        (degreeTwoCocycle f₁ J ((resolutionMap sq J).f (-2) ≫ c)
          (by simp only [← HomologicalComplex.Hom.comm_assoc, hc, comp_zero]))) 0 := by
  rw [degreeTwoCocycle_precomp, Cocycle.equivHomShift_symm_precomp]
  simpa only [comp_zero] using h.compLeft (resolutionMap sq J)

/-- A literal primitive pulls back to a primitive of the pulled-back degree-two cocycle. -/
theorem degreeTwoCocycle_nullHomotopic_precomp_of_primitive
    {A : Sheaf J AddCommGrpCat.{max u v}}
    (c : (resolution f₂ J).X (-2) ⟶ A)
    (hc : (resolution f₂ J).d (-3) (-2) ≫ c = 0)
    (p : (resolution f₂ J).X (-1) ⟶ A)
    (hp : (resolution f₂ J).d (-2) (-1) ≫ p = c) :
    Nonempty (Homotopy
      (Cocycle.equivHomShift.symm
        (degreeTwoCocycle f₁ J ((resolutionMap sq J).f (-2) ≫ c)
          (by simp only [← HomologicalComplex.Hom.comm_assoc, hc, comp_zero]))) 0) :=
  degreeTwoCocycle_nullHomotopic f₁ J _ _ ((resolutionMap sq J).f (-1) ≫ p)
    (resolutionMap_precomp_differential_eq sq J p c hp)

end DegreeTwoCocycleNaturality

section DerivedArrowSquareNaturality

universe z

variable {F₁ G₁ F₂ G₂ : Cᵒᵖ ⥤ Type (max u v)} {f₁ : F₁ ⟶ G₁} {f₂ : F₂ ⟶ G₂}
    (sq : Arrow.mk f₁ ⟶ Arrow.mk f₂)
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v}]
    [IsLocallySurjective J f₁] [IsLocallySurjective J f₂]
    [HasDerivedCategory.{z} (Sheaf J AddCommGrpCat.{max u v})]

open CochainComplex CochainComplex.HomComplex

/-- Naturality of the literal derived roof under a square of locally surjective presheaf maps. -/
theorem degreeTwoClass_precomp {A : Sheaf J AddCommGrpCat.{max u v}}
    (c : (resolution f₂ J).X (-2) ⟶ A)
    (hc : (resolution f₂ J).d (-3) (-2) ≫ c = 0) :
    degreeTwoClass f₁ J ((resolutionMap sq J).f (-2) ≫ c)
        (by simp only [← HomologicalComplex.Hom.comm_assoc, hc, comp_zero]) =
      (DerivedCategory.singleFunctor _ 0).map (targetMap sq J) ≫
        degreeTwoClass f₂ J c hc := by
  have := resolutionAugmentation_quasiIso f₁ J
  have := resolutionAugmentation_quasiIso f₂ J
  let L := resolutionMap sq J
  have hz : degreeTwoCocycle f₁ J (L.f (-2) ≫ c)
      (by simp only [← HomologicalComplex.Hom.comm_assoc, hc, comp_zero]) =
      (degreeTwoCocycle f₂ J c hc).precomp L :=
    Cocycle.toSingleMk_precomp c (by norm_num) (-3) (by norm_num) hc L
  have hmap : Cocycle.equivHomShift.symm
      (degreeTwoCocycle f₁ J (L.f (-2) ≫ c)
        (by simp only [← HomologicalComplex.Hom.comm_assoc, hc, comp_zero])) =
      L ≫ Cocycle.equivHomShift.symm (degreeTwoCocycle f₂ J c hc) := by
    rw [hz, Cocycle.equivHomShift_symm_precomp]
  have haug := congrArg (fun r => DerivedCategory.Q.map r)
    (resolutionAugmentation_naturality sq J)
  simp only [Functor.map_comp] at haug
  have hinv : inv (DerivedCategory.Q.map (resolutionAugmentation f₁ J)) ≫
        DerivedCategory.Q.map L =
      (DerivedCategory.singleFunctor _ 0).map (targetMap sq J) ≫
        inv (DerivedCategory.Q.map (resolutionAugmentation f₂ J)) := by
    apply (cancel_mono (DerivedCategory.Q.map (resolutionAugmentation f₂ J))).mp
    rw [Category.assoc, haug]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id,
      Category.comp_id]
    rfl
  unfold degreeTwoClass
  rw [hmap, Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun r => r ≫ DerivedCategory.Q.map
      (Cocycle.equivHomShift.symm (degreeTwoCocycle f₂ J c hc)) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
        ((CochainComplex.singleFunctor _ 0).obj A)) hinv

end DerivedArrowSquareNaturality

end CategoryTheory.Presheaf.Cech
