/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.CechFamily
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.CechComparison

/-! # Original tuple and cochain maps under a site functor

A functor, an isomorphism of family targets, and isomorphisms of the family
members in the actual slice categories map the original represented tuples.
All tuple reindexings commute with this map, hence so do the original free
alternating face differentials and the original additive Hom differentials.

The comparison of free presheaves is only a morphism. No full faithfulness of
the site functor, preservation of injectives, or cohomological comparison is
assumed. Invertibility on additive Hom cochains is a separate finite-product
argument, not invertibility of this tuple-presheaf morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Presheaf.Cech.FamilyBaseChange

universe u v w

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (P : C ⥤ D) {W : C} {W' : D} {ι : Type w}
  (U : ι → Over W) (V : ι → Over W') (e : P.obj W ≅ W')
  (eU : ∀ i, (Over.post P ⋙ Over.map e.hom).obj (U i) ≅ V i)

/-- The family isomorphism transports the original lift triangle. -/
theorem mappedLift_triangle {T : C} (h : T ⟶ W) (i : ι)
    (g : T ⟶ (U i).left) (hg : g ≫ (U i).hom = h) :
    (P.map g ≫ (eU i).hom.left) ≫ (V i).hom = P.map h ≫ e.hom := by
  let b : P.obj (U i).left ⟶ (V i).left := (eU i).hom.left
  have hb : b ≫ (V i).hom = P.map (U i).hom ≫ e.hom := Over.w (eU i).hom
  change (P.map g ≫ b) ≫ (V i).hom = _
  rw [Category.assoc, hb, ← Category.assoc, ← P.map_comp, hg]

/-- Applying the site functor respects precomposition of the target section. -/
theorem mappedTarget_precomp {T T' : C} (g : T' ⟶ T) (h : T ⟶ W) :
    P.map (g ≫ h) ≫ e.hom = P.map g ≫ (P.map h ≫ e.hom) := by
  rw [P.map_comp, Category.assoc]

/-- Applying the site functor respects precomposition of each family lift. -/
theorem mappedLift_precomp {T T' : C} (g : T' ⟶ T)
    (s : Σ i, T ⟶ (U i).left) :
    (⟨s.1, P.map (g ≫ s.2) ≫ (eU s.1).hom.left⟩ :
      Σ i, P.obj T' ⟶ (V i).left) =
      ⟨s.1, P.map g ≫ (P.map s.2 ≫ (eU s.1).hom.left)⟩ := by
  let b : P.obj (U s.1).left ⟶ (V s.1).left := (eU s.1).hom.left
  have hb : P.map (g ≫ s.2) ≫ b = P.map g ≫ (P.map s.2 ≫ b) := by
    rw [P.map_comp, Category.assoc]
  exact congrArg (fun k => (⟨s.1, k⟩ : Σ i, P.obj T' ⟶ (V i).left)) hb

/-- Apply the original site functor to each represented lift and then the
specified family comparison, retaining the actual target section. -/
def tupleMap {n : ℕ} {X : Cᵒᵖ} (t : Tuple (familyMap U) n X) :
    Tuple (familyMap V) n (P.op.obj X) :=
  ⟨⟨P.map t.1.down ≫ e.hom⟩, fun k =>
    ⟨⟨(t.2 k).1.1, P.map (t.2 k).1.2 ≫ (eU (t.2 k).1.1).hom.left⟩,
      ULift.ext _ _ (mappedLift_triangle P U V e eU t.1.down
        (t.2 k).1.1 (t.2 k).1.2 (congrArg ULift.down (t.2 k).2))⟩⟩

/-- Every reindexing, in particular every deletion face, commutes with the
literal tuple map. -/
theorem tupleMap_reindex {m n : ℕ} {X : Cᵒᵖ}
    (a : Fin (m + 1) → Fin (n + 1)) (t : Tuple (familyMap U) n X) :
    tupleMap P U V e eU (tupleReindex (familyMap U) a t) =
      tupleReindex (familyMap V) a (tupleMap P U V e eU t) := rfl

/-- The tuple map is a natural transformation on the original source site. -/
def tupleNatTrans (n : ℕ) :
    tuplePresheaf (familyMap U) n ⟶ P.op ⋙ tuplePresheaf (familyMap V) n where
  app X := ↾(tupleMap P U V e eU)
  naturality X Y g := by
    apply ConcreteCategory.hom_ext
    intro t
    apply tuple_ext
    · exact ULift.ext _ _ (mappedTarget_precomp P e g.unop t.1.down)
    · intro k
      exact mappedLift_precomp P U V e eU g.unop (t.2 k).1

/-- The original represented tuple nerves are related by these same maps in
all simplicial degrees. -/
def nerveMap : nerve (familyMap U) ⟶
    ((SimplicialObject.whiskering _ _).obj
      ((Functor.whiskeringLeft _ _ (Type (max w v))).obj P.op)).obj
        (nerve (familyMap V)) where
  app n := tupleNatTrans P U V e eU n.unop.len
  naturality n m g := by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro t
    exact tupleMap_reindex P U V e eU g.unop.toOrderHom t

/-- Ordinary precomposition of the original abelian presheaves. -/
abbrev abelianPrecomposition :
    (Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max w v} :=
  (Functor.whiskeringLeft _ _ _).obj P.op

/-- The free nerve map is obtained from the original tuple map, without an
isomorphism assertion about represented presheaves. -/
def freeNerveMap :
    ((SimplicialObject.whiskering _ _).obj freeFunctor).obj (nerve (familyMap U)) ⟶
      ((SimplicialObject.whiskering _ _).obj (abelianPrecomposition.{u, v, w} P)).obj
        (((SimplicialObject.whiskering _ _).obj freeFunctor).obj (nerve (familyMap V))) :=
  ((SimplicialObject.whiskering _ _).obj freeFunctor).map (nerveMap P U V e eU)

/-- The actual free chain map, using the native comparison between applying
an additive functor and taking the alternating face complex. -/
def freeComplexMap : freeComplex (familyMap U) ⟶
    ((abelianPrecomposition.{u, v, w} P).mapHomologicalComplex (.down ℕ)).obj
      (freeComplex (familyMap V)) :=
  AlgebraicTopology.AlternatingFaceMapComplex.map (freeNerveMap P U V e eU) ≫
    (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (abelianPrecomposition.{u, v, w} P)).inv.app
        (((SimplicialObject.whiskering _ _).obj freeFunctor).obj (nerve (familyMap V)))

/-- In every degree the free chain map is the free map of the original tuple
comparison; the alternating-complex transport inserts only identities. -/
@[simp]
theorem freeComplexMap_f (n : ℕ) :
    (freeComplexMap P U V e eU).f n =
      Functor.whiskerRight (tupleNatTrans P U V e eU n) AddCommGrpCat.free := rfl

/-- The actual additive map on the original Hom groups in one degree. -/
def additiveHomMapDegree (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) (n : ℕ) :
    AddCommGrpCat.of ((freeComplex (familyMap V)).X n ⟶ A) ⟶
      AddCommGrpCat.of ((freeComplex (familyMap U)).X n ⟶ P.op ⋙ A) :=
  AddCommGrpCat.ofHom
    { toFun q := (freeComplexMap P U V e eU).f n ≫
        (abelianPrecomposition.{u, v, w} P).map q
      map_zero' := by rw [Functor.map_zero, comp_zero]
      map_add' q r := by rw [Functor.map_add, Preadditive.comp_add] }

/-- The original free chain-map square, evaluated on an actual cochain. -/
theorem additiveHomMap_comm_apply (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v})
    (i j : ℕ) (q : (freeComplex (familyMap V)).X i ⟶ A) :
    (freeComplex (familyMap U)).d j i ≫
        ((freeComplexMap P U V e eU).f i ≫
          (abelianPrecomposition.{u, v, w} P).map q) =
      (freeComplexMap P U V e eU).f j ≫
        (abelianPrecomposition.{u, v, w} P).map
          ((freeComplex (familyMap V)).d j i ≫ q) := by
  have h : (freeComplexMap P U V e eU).f j ≫
      (abelianPrecomposition.{u, v, w} P).map ((freeComplex (familyMap V)).d j i) =
      (freeComplex (familyMap U)).d j i ≫ (freeComplexMap P U V e eU).f i :=
    (freeComplexMap P U V e eU).comm j i
  calc
    _ = ((freeComplex (familyMap U)).d j i ≫
        (freeComplexMap P U V e eU).f i) ≫
          (abelianPrecomposition.{u, v, w} P).map q := (Category.assoc _ _ _).symm
    _ = ((freeComplexMap P U V e eU).f j ≫
        (abelianPrecomposition.{u, v, w} P).map ((freeComplex (familyMap V)).d j i)) ≫
          (abelianPrecomposition.{u, v, w} P).map q :=
      congrArg (fun k => k ≫ (abelianPrecomposition.{u, v, w} P).map q) h.symm
    _ = _ := by rw [Functor.map_comp, Category.assoc]

/-- Restrict actual target-family cochains to the source family with
precomposed coefficients. The original face differential is retained. -/
def additiveHomMap (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) :
    additiveHomComplex (familyMap V) A ⟶
      additiveHomComplex (familyMap U) (P.op ⋙ A) where
  f n := additiveHomMapDegree P U V e eU A n
  comm' i j _ :=
    ConcreteCategory.hom_ext _ _ (fun q => additiveHomMap_comm_apply P U V e eU A i j q)

/-- The cochain comparison is evaluation of the original free tuple map,
followed by ordinary precomposition of the coefficient morphism. -/
theorem additiveHomMap_f_apply (A : Dᵒᵖ ⥤ AddCommGrpCat.{max w v}) (n : ℕ)
    (q : (freeComplex (familyMap V)).X n ⟶ A) :
    (additiveHomMap P U V e eU A).f n q =
      Functor.whiskerRight (tupleNatTrans P U V e eU n) AddCommGrpCat.free ≫
        Functor.whiskerLeft P.op q :=
  congrArg
    (fun k : (freeComplex (familyMap U)).X n ⟶ P.op ⋙ (freeComplex (familyMap V)).X n =>
      k ≫ Functor.whiskerLeft P.op q)
    (freeComplexMap_f P U V e eU n)

end CategoryTheory.Presheaf.Cech.FamilyBaseChange
