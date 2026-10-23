/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FamilyProjective
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.CechComparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.ExactSequences
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-! # Tuple Hom cochains and product Čech cochains

The comparison evaluates an original tuple cochain on the universal tuple of
projections. Both the cover and all cofaces remain the original ones.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Presheaf.Cech

universe c h w

variable {C : Type c} [Category.{h} C] {W : C} [HasFiniteProducts (Over W)]
  {ι : Type (max c w)} (U : ι → Over W)
  (F : Cᵒᵖ ⥤ AddCommGrpCat.{max c h w})

/-- Evaluation of a free tuple cochain on the universal tuples of projections. -/
def tupleHomSectionsAddEquiv (n : ℕ) :
    (tuplePresheaf (familyMap U) n ⋙ AddCommGrpCat.free ⟶ F) ≃+
      (∀ a : Fin (n + 1) → ι, F.obj (op (∏ᶜ fun i => U (a i)).left)) := by
  let V := fun a : Fin (n + 1) → ι => (∏ᶜ fun i => U (a i)).left
  let e := ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).mapIso (tupleProductIso U n)
  refine {
    toFun := fun f => freeFamilyHomEquiv V F (e.inv ≫ f)
    invFun := fun s => e.hom ≫ (freeFamilyHomEquiv V F).symm s
    left_inv := ?_
    right_inv := ?_
    map_add' := ?_ }
  · intro f
    simp only [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  · intro s
    simp only [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  · intro f g
    funext a
    rw [Preadditive.comp_add]
    rfl

/-- The component formula uses the actual universal tuple, not a chosen
objectwise identification of cohomology groups. -/
lemma tupleHomSectionsAddEquiv_apply (n : ℕ)
    (f : tuplePresheaf (familyMap U) n ⋙ AddCommGrpCat.free ⟶ F)
    (a : Fin (n + 1) → ι) :
    tupleHomSectionsAddEquiv U F n f a =
      f.app (op (∏ᶜ fun i => U (a i)).left)
        (FreeAbelianGroup.of (productToTuple U ⟨a, 𝟙 _⟩)) := rfl

/-- Forgetting one coordinate is the original product projection in the slice. -/
def tupleProductProjection {n : ℕ} (a : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    (∏ᶜ fun i => U (a i)) ⟶ ∏ᶜ fun k => U (a (j.succAbove k)) :=
  Pi.lift fun k => Pi.π (fun i => U (a i)) (j.succAbove k)

/-- The universal tuple commutes with every original coface. -/
lemma tupleReindex_universal {n : ℕ} (a : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    tupleReindex (familyMap U) j.succAbove (productToTuple U ⟨a, 𝟙 _⟩) =
      tupleRestrict (familyMap U) (tupleProductProjection U a j).left.op
        (productToTuple U ⟨fun k => a (j.succAbove k), 𝟙 _⟩) := by
  apply tuple_ext
  · apply ULift.ext
    change 𝟙 _ ≫ (∏ᶜ fun i => U (a i)).hom =
      (tupleProductProjection U a j).left ≫
        (𝟙 _ ≫ (∏ᶜ fun k => U (a (j.succAbove k))).hom)
    simpa only [Category.id_comp] using (Over.w (tupleProductProjection U a j)).symm
  · intro k
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      change 𝟙 _ ≫ (Pi.π (fun i => U (a i)) (j.succAbove k)).left =
        (tupleProductProjection U a j).left ≫
          (𝟙 _ ≫ (Pi.π (fun i => U (a (j.succAbove i))) k).left)
      simpa only [Category.id_comp, Over.comp_left, tupleProductProjection] using
        (congrArg (fun f => f.left)
          (Pi.lift_comp_π (fun k => Pi.π (fun i => U (a i)) (j.succAbove k)) k)).symm

omit [HasFiniteProducts (Over W)] in
/-- The original free differential evaluated on a generator. -/
lemma freeHom_d_apply (n : ℕ)
    (f : tuplePresheaf (familyMap U) n ⋙ AddCommGrpCat.free ⟶ F)
    (X : Cᵒᵖ) (a : Tuple (familyMap U) (n + 1) X) :
    (((freeComplex (familyMap U)).d (n + 1) n ≫ f).app X) (FreeAbelianGroup.of a) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        f.app X (FreeAbelianGroup.of (tupleReindex (familyMap U) j.succAbove a)) := by
  let d := (freeComplex (familyMap U)).d (n + 1) n
  let ev : (AddCommGrpCat.free.obj (Tuple (familyMap U) (n + 1) X) ⟶
      AddCommGrpCat.free.obj (Tuple (familyMap U) n X)) →+
      FreeAbelianGroup (Tuple (familyMap U) n X) :=
    { toFun g := g (FreeAbelianGroup.of a)
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hd : d.app X = ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      AddCommGrpCat.free.map (↾(tupleReindex (familyMap U) j.succAbove)) := by
    simp [d, freeComplex, AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
      SimplicialObject.δ, SimplexCategory.δ, nerve, freeFunctor]
    rfl
  change (f.app X).hom (ev (d.app X)) = _
  erw [hd, _root_.map_sum, _root_.map_sum]
  simp only [_root_.map_zsmul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1

/-- Evaluation on universal tuples identifies the original alternating
Hom differential with the original alternating restriction differential. -/
lemma tupleHomSectionsAddEquiv_d (n : ℕ)
    (f : tuplePresheaf (familyMap U) n ⋙ AddCommGrpCat.free ⟶ F)
    (a : Fin (n + 2) → ι) :
    tupleHomSectionsAddEquiv U F (n + 1) ((freeComplex (familyMap U)).d (n + 1) n ≫ f) a =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        F.map (tupleProductProjection U a j).left.op
          (tupleHomSectionsAddEquiv U F n f (fun k => a (j.succAbove k))) := by
  rw [tupleHomSectionsAddEquiv_apply]
  change (((freeComplex (familyMap U)).d (n + 1) n ≫ f).app
    (op (∏ᶜ fun i => U (a i)).left)) (FreeAbelianGroup.of (productToTuple U ⟨a, 𝟙 _⟩)) = _
  erw [freeHom_d_apply]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [tupleReindex_universal, tupleHomSectionsAddEquiv_apply]
  let p := (tupleProductProjection U a j).left.op
  let z := productToTuple U
    (X := op (∏ᶜ fun k => U (a (j.succAbove k))).left)
    ⟨fun k => a (j.succAbove k), 𝟙 _⟩
  have h := f.naturality_apply p (FreeAbelianGroup.of z)
  change f.app _ (FreeAbelianGroup.map (tupleRestrict (familyMap U) p)
    (FreeAbelianGroup.of z)) = F.map p (f.app _ (FreeAbelianGroup.of z)) at h
  simpa only [FreeAbelianGroup.map_of_apply] using h

universe r s

/-- The concrete product equivalence is additive. -/
def productSectionsAddEquiv {κ : Type r} (A : κ → AddCommGrpCat.{max r s}) :
    ↑(∏ᶜ A : AddCommGrpCat.{max r s}) ≃+ (∀ k, A k) where
  toEquiv := Concrete.productEquiv A
  map_add' x y := by
    funext k
    change Concrete.productEquiv A (x + y) k =
      Concrete.productEquiv A x k + Concrete.productEquiv A y k
    rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply,
      Concrete.productEquiv_apply_apply]
    exact (Pi.π A k).hom.map_add x y

/-- The actual degreewise comparison from tuple Hom cochains to product cochains. -/
def tupleHomProductIso (n : ℕ) :
    (additiveHomComplex (familyMap U) F).X n ≅
      ((cechComplexFunctor U).obj ((Over.forget W).op ⋙ F)).X n :=
  AddEquiv.toAddCommGrpIso
    ((tupleHomSectionsAddEquiv U F n).trans
      (productSectionsAddEquiv.{max c w, h} (fun a : Fin (n + 1) → ι =>
        F.obj (op (∏ᶜ fun i => U (a i)).left))).symm)

/-- Each product component is evaluation on its original universal tuple. -/
lemma tupleHomProductIso_hom_π (n : ℕ)
    (f : tuplePresheaf (familyMap U) n ⋙ AddCommGrpCat.free ⟶ F)
    (a : Fin (n + 1) → ι) :
    Pi.π (fun b : Fin (n + 1) → ι => F.obj (op (∏ᶜ fun i => U (b i)).left)) a
      ((tupleHomProductIso U F n).hom f) = tupleHomSectionsAddEquiv U F n f a :=
  Concrete.productEquiv_symm_apply_π _ _ _


lemma hom_sum_apply {A B : AddCommGrpCat.{r}}
    {κ : Type*} (s : Finset κ) (f : κ → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  let e : (A ⟶ B) →+ B :=
    { toFun := fun f => f x
      map_zero' := rfl
      map_add' _ _ := rfl }
  exact _root_.map_sum e _ _

lemma hom_zsmul_apply {A B : AddCommGrpCat.{r}}
    (n : ℤ) (f : A ⟶ B) (x : A) : (n • f) x = n • f x := rfl

/-- The original tuple Hom complex and the native product Čech complex are
isomorphic, with every alternating coface identified by the universal tuple. -/
def tupleHomCechIso : additiveHomComplex (familyMap U) F ≅
    (cechComplexFunctor U).obj ((Over.forget W).op ⋙ F) := by
  refine HomologicalComplex.Hom.isoOfComponents (tupleHomProductIso U F) ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, CategoryTheory.Cech.cech_d_comp_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, ← Category.assoc]
  apply AddCommGrpCat.ext
  intro f
  simp only [hom_sum_apply, hom_zsmul_apply, ConcreteCategory.comp_apply]
  change (∑ x : Fin (i + 2), (-1 : ℤ) ^ (x : ℕ) •
    F.map (tupleProductProjection U a x).left.op
      (Pi.π (fun b : Fin (i + 1) → ι => F.obj (op (∏ᶜ fun k => U (b k)).left))
        (fun k => a (x.succAbove k)) ((tupleHomProductIso U F i).hom f))) =
    Pi.π (fun b : Fin (i + 2) → ι => F.obj (op (∏ᶜ fun k => U (b k)).left)) a
      ((tupleHomProductIso U F (i + 1)).hom ((freeComplex (familyMap U)).d (i + 1) i ≫ f))
  simp only [tupleHomProductIso_hom_π]
  exact (tupleHomSectionsAddEquiv_d U F i f a).symm

end CategoryTheory.Presheaf.Cech
