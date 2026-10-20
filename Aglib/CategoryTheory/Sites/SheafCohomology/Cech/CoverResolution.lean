/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Free abelian resolutions of locally surjective presheaf maps

For a map of set-valued presheaves, the degree-`n` tuples consist of a target
section and `n + 1` source sections above it. This construction requires no
limits in the underlying site category.

The first consumer is the ordered degree-two coordinate Kummer cocycle. Its
literal tuple-of-lifts formula extends to the free abelian terms constructed
here. The image-augmented nerve is already a resolution before sheafification;
local surjectivity is used only to identify its sheafified image with the target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped Simplicial

universe u v w

namespace CategoryTheory.Presheaf.Cech

variable {C : Type u} [Category.{v} C]
  {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G)

/-- A source section with the specified image. -/
abbrev Lift (U : Cᵒᵖ) (y : G.obj U) := {x : F.obj U // f.app U x = y}

/-- Ordered tuples in one fibre, including their actual target section. -/
abbrev Tuple (n : ℕ) (U : Cᵒᵖ) := Σ y : G.obj U, Fin (n + 1) → Lift f U y

@[ext]
theorem tuple_ext {n : ℕ} {U : Cᵒᵖ} {a b : Tuple f n U}
    (hy : a.1 = b.1) (hx : ∀ i, (a.2 i).1 = (b.2 i).1) : a = b := by
  rcases a with ⟨y, a⟩
  rcases b with ⟨z, b⟩
  dsimp at hy hx
  subst z
  congr 1
  funext i
  exact Subtype.ext (hx i)

/-- Restriction retains the target section and each original lift. -/
def tupleRestrict {n : ℕ} {U V : Cᵒᵖ} (g : U ⟶ V) (a : Tuple f n U) :
    Tuple f n V :=
  ⟨G.map g a.1, fun i => ⟨F.map g (a.2 i).1, by
    rw [NatTrans.naturality_apply, (a.2 i).2]⟩⟩

/-- Reindexing a tuple defines all simplicial operators. -/
def tupleReindex {m n : ℕ} {U : Cᵒᵖ} (g : Fin (m + 1) → Fin (n + 1))
    (a : Tuple f n U) : Tuple f m U := ⟨a.1, a.2 ∘ g⟩

/-- The presheaf of ordered tuples in the fibres of the original map. -/
def tuplePresheaf (n : ℕ) : Cᵒᵖ ⥤ Type w where
  obj U := Tuple f n U
  map g := ↾(tupleRestrict f g)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro a
    apply tuple_ext
    · exact G.map_id_apply U a.1
    · intro i
      exact F.map_id_apply U (a.2 i).1
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro a
    apply tuple_ext
    · exact G.map_comp_apply g h a.1
    · intro i
      exact F.map_comp_apply g h (a.2 i).1

/-- The presheaf Čech nerve, constructed independently of pullbacks in `C`. -/
def nerve : SimplicialObject (Cᵒᵖ ⥤ Type w) where
  obj n := tuplePresheaf f n.unop.len
  map g :=
    { app U := ↾(tupleReindex f g.unop.toOrderHom)
      naturality _ _ _ := rfl }
  map_id _ := by ext U a; rfl
  map_comp _ _ := by ext U a; rfl

/-- The augmentation to the original target presheaf. -/
def augmentedNerve : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w) where
  left := nerve f
  right := G
  hom :=
    { app _ := { app _ := ↾Sigma.fst }
      naturality _ _ _ := rfl }

/-- The same nerve augmented to the pointwise image of the original map. -/
def imageAugmentedNerve : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w) where
  left := nerve f
  right := (Subfunctor.range f).toFunctor
  hom :=
    { app _ :=
        { app _ := ↾fun a => ⟨a.1, ⟨(a.2 0).1, (a.2 0).2⟩⟩
          naturality _ _ _ := rfl }
      naturality _ _ _ := rfl }

/-- Free abelian groups are taken objectwise on the presheaf category. -/
abbrev freeFunctor : (Cᵒᵖ ⥤ Type w) ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free

/-- The actual free abelian Čech chain complex of the presheaf map. -/
def freeComplex : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj
    (((SimplicialObject.whiskering _ _).obj freeFunctor).obj (nerve f))

/-- The actual free augmentation to the original target in degree zero. -/
def freeAugmentation : freeComplex f ⟶
    (ChainComplex.single₀ _).obj (G ⋙ AddCommGrpCat.free) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((SimplicialObject.Augmented.whiskering _ _).obj freeFunctor).obj (augmentedNerve f))

/-- The free augmentation to the pointwise image in degree zero. -/
def freeImageAugmentation : freeComplex f ⟶
    (ChainComplex.single₀ _).obj ((Subfunctor.range f).toFunctor ⋙ AddCommGrpCat.free) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((SimplicialObject.Augmented.whiskering _ _).obj freeFunctor).obj
      (imageAugmentedNerve f))

/-- A lift is chosen only in a nonempty fibre at one test object. -/
def chosenLift (U : Cᵒᵖ) (y : (Subfunctor.range f).toFunctor.obj U) : Lift f U y.1 :=
  ⟨y.2.choose, y.2.choose_spec⟩

/-- Prepending the chosen lift contracts each nonempty fibre. -/
def prepend {n : ℕ} {U : Cᵒᵖ} (a : Tuple f n U) : Tuple f (n + 1) U :=
  ⟨a.1, Fin.cons (chosenLift f U ⟨a.1, ⟨(a.2 0).1, (a.2 0).2⟩⟩) a.2⟩

/-- Evaluation at one object has an extra degeneracy; no natural global splitting is chosen. -/
def evaluatedImageExtraDegeneracy (U : Cᵒᵖ) :
    (((SimplicialObject.Augmented.whiskering _ _).obj
      ((evaluation _ _).obj U)).obj (imageAugmentedNerve f)).ExtraDegeneracy where
  s' := ↾fun y => ⟨y.1, fun _ => chosenLift f U y⟩
  s n := ↾(prepend f)
  s'_comp_ε := by ext y; rfl
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro a
    apply tuple_ext
    · rfl
    · intro i
      fin_cases i
      rfl
  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    intro a
    change tupleReindex f (SimplexCategory.δ 0).toOrderHom (prepend f a) = a
    apply tuple_ext
    · rfl
    · intro i
      simp [SimplexCategory.δ, tupleReindex, prepend]
  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    intro a
    change tupleReindex f (SimplexCategory.δ i.succ).toOrderHom (prepend f a) =
      prepend f (tupleReindex f (SimplexCategory.δ i).toOrderHom a)
    apply tuple_ext
    · rfl
    · intro j
      induction j using Fin.cases <;>
        simp [SimplexCategory.δ, tupleReindex, prepend]
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    intro a
    change tupleReindex f (SimplexCategory.σ i.succ).toOrderHom (prepend f a) =
      prepend f (tupleReindex f (SimplexCategory.σ i).toOrderHom a)
    apply tuple_ext
    · rfl
    · intro j
      induction j using Fin.cases <;>
        simp [SimplexCategory.σ, tupleReindex, prepend]

section MapAugmentation

variable {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
    (E : A ⥤ B) [E.Additive] (X : SimplicialObject.Augmented A)

/-- Mapping an actual augmented face complex retains its original augmentation. -/
def mapAugmentationArrowIso :
    Arrow.mk ((E.mapHomologicalComplex _).map
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app X)) ≅
    Arrow.mk (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (((SimplicialObject.Augmented.whiskering _ _).obj E).obj X)) :=
  Arrow.isoMk
    ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso E).app X.left)
    ((HomologicalComplex.singleMapHomologicalComplex E (.down ℕ) 0).app X.right)
    (by
      apply HomologicalComplex.to_single_hom_ext
      dsimp only [Arrow.mk, Arrow.hom]
      erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      simp only [Functor.comp_obj, SimplicialObject.Augmented.drop_obj,
        SimplicialObject.Augmented.point_obj, ChainComplex.single₀_obj_zero, Iso.app_hom,
        AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso_hom_app_f,
        AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero, Functor.id_obj,
        Functor.mapHomologicalComplex_map_f, AlgebraicTopology.alternatingFaceMapComplex_obj_X,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self, ChainComplex.single₀ObjXSelf,
        Iso.refl_hom, Functor.map_id, Iso.refl_inv, Category.comp_id]
      erw [Category.id_comp, Category.comp_id]
      change E.map (X.hom.app (op ⦋0⦌)) ≫ 𝟙 _ = E.map (X.hom.app (op ⦋0⦌))
      exact Category.comp_id _)

end MapAugmentation

/-- The image augmentation is a quasi-isomorphism for every map of presheaves of sets. -/
theorem freeImageAugmentation_quasiIso : QuasiIso (freeImageAugmentation f) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro U
  let E := (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
  let X := ((SimplicialObject.Augmented.whiskering _ _).obj freeFunctor).obj
    (imageAugmentedNerve f)
  apply (quasiIso_iff_of_arrow_mk_iso _ _
    (mapAugmentationArrowIso E X)).2
  exact inferInstanceAs
    (QuasiIso (((evaluatedImageExtraDegeneracy f U).map
      AddCommGrpCat.free).homotopyEquiv.hom))

/-- The original augmentation factors through the actual pointwise-image augmentation. -/
theorem freeAugmentation_factor :
    freeAugmentation f = freeImageAugmentation f ≫
      (ChainComplex.single₀ _).map
        (whiskerRight (Subfunctor.range f).ι AddCommGrpCat.free) := by
  let v : imageAugmentedNerve f ⟶ augmentedNerve f :=
    { left := 𝟙 _
      right := (Subfunctor.range f).ι
      w := by ext n U a; rfl }
  have h := AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality
    (((SimplicialObject.Augmented.whiskering _ _).obj freeFunctor).map v)
  have hl :
      (((SimplicialObject.Augmented.whiskering _ _).obj freeFunctor).map v).left =
        𝟙 _ := by
    change whiskerRight (𝟙 (nerve f)) freeFunctor = 𝟙 _
    simp
  have hr :
      (((SimplicialObject.Augmented.whiskering _ _).obj freeFunctor).map v).right =
        whiskerRight (Subfunctor.range f).ι AddCommGrpCat.free := rfl
  simp only [Functor.comp_map, SimplicialObject.Augmented.drop_map,
    SimplicialObject.Augmented.point_map, hl, hr] at h
  erw [Functor.map_id, Category.id_comp] at h
  exact h

section Sheafification

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- The free Čech resolution after the original exact abelian sheafification. -/
def sheafComplex : ChainComplex (Sheaf J AddCommGrpCat.{w}) ℕ :=
  ((presheafToSheaf J AddCommGrpCat).mapHomologicalComplex _).obj (freeComplex f)

/-- The original sheafified augmentation, with the free target in degree zero. -/
def sheafAugmentation : sheafComplex f J ⟶
    (ChainComplex.single₀ _).obj ((presheafToSheaf J AddCommGrpCat).obj
      (G ⋙ AddCommGrpCat.free)) :=
  ((presheafToSheaf J AddCommGrpCat).mapHomologicalComplex _).map (freeAugmentation f) ≫
    (HomologicalComplex.singleMapHomologicalComplex (presheafToSheaf J AddCommGrpCat)
      (.down ℕ) 0).hom.app (G ⋙ AddCommGrpCat.free)

end Sheafification

section StandardUniverse

variable {F' G' : Cᵒᵖ ⥤ Type (max u v)} (coverMap : F' ⟶ G')
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v}]
    [IsLocallySurjective J coverMap]

/-- Local surjectivity makes the pointwise image and the target have the same free sheaf. -/
theorem freeImageInclusion_sheafify_isIso :
    IsIso ((presheafToSheaf J AddCommGrpCat).map
      (whiskerRight (Subfunctor.range coverMap).ι AddCommGrpCat.free)) := by
  have hi : IsLocallyInjective J (Subfunctor.range coverMap).ι := by
    apply isLocallyInjective_of_injective
    intro U
    exact Subtype.val_injective
  have hs : IsLocallySurjective J (Subfunctor.range coverMap).ι :=
    isLocallySurjective_of_isLocallySurjective_fac J (Subfunctor.toRange_ι coverMap)
  rw [← J.W_iff]
  apply J.W_of_preservesSheafification AddCommGrpCat.free
  exact J.W_of_isLocallyBijective (Subfunctor.range coverMap).ι

/-- A locally surjective set-presheaf map has the genuine sheafified free Čech resolution. -/
theorem sheafAugmentation_quasiIso : QuasiIso (sheafAugmentation coverMap J) := by
  have := freeImageAugmentation_quasiIso coverMap
  have := freeImageInclusion_sheafify_isIso coverMap J
  let S := presheafToSheaf J AddCommGrpCat.{max u v}
  have hq : QuasiIso ((S.mapHomologicalComplex _).map (freeImageAugmentation coverMap)) :=
    inferInstance
  have hm : IsIso ((S.mapHomologicalComplex _).map
      ((ChainComplex.single₀ _).map
        (whiskerRight (Subfunctor.range coverMap).ι AddCommGrpCat.free))) := by
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso
        (HomologicalComplex.singleMapHomologicalComplex S (.down ℕ) 0)
        (Arrow.mk (whiskerRight (Subfunctor.range coverMap).ι AddCommGrpCat.free)))).2
      (by
        change IsIso ((ChainComplex.single₀ _).map
          (S.map (whiskerRight (Subfunctor.range coverMap).ι AddCommGrpCat.free)))
        infer_instance)
  have hmid : QuasiIso ((S.mapHomologicalComplex _).map
      ((ChainComplex.single₀ _).map
        (whiskerRight (Subfunctor.range coverMap).ι AddCommGrpCat.free))) := by
    infer_instance
  unfold sheafAugmentation
  rw [freeAugmentation_factor, Functor.map_comp]
  exact quasiIso_comp _ _ (hφ := quasiIso_comp _ _ (hφ := hq) (hφ' := hmid))

end StandardUniverse


section CochainResolution

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- The actual Čech resolution in cochain degree `-n`, extended by zero in positive degrees. -/
def resolution : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ :=
  (sheafComplex f J).extend ComplexShape.embeddingDownNat

/-- The native identification of the degree `-n` term with the free sheaf on actual tuples. -/
def resolutionTermIso (n : ℕ) :
    (resolution f J).X (-(n : ℤ)) ≅
      (presheafToSheaf J AddCommGrpCat).obj (tuplePresheaf f n ⋙ AddCommGrpCat.free) :=
  (sheafComplex f J).extendXIso ComplexShape.embeddingDownNat rfl

/-- The original augmentation to the actual free target in cochain degree zero. -/
def resolutionAugmentation : resolution f J ⟶
    (CochainComplex.singleFunctor _ 0).obj
      ((presheafToSheaf J AddCommGrpCat).obj (G ⋙ AddCommGrpCat.free)) :=
  HomologicalComplex.extendMap (sheafAugmentation f J) ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      ((presheafToSheaf J AddCommGrpCat).obj (G ⋙ AddCommGrpCat.free)) 0 0 rfl).hom

/-- Morphisms from a free tuple sheaf are exactly natural values on its original generators. -/
def tupleSectionsEquiv (n : ℕ) (A : Sheaf J AddCommGrpCat.{w}) :
    ((presheafToSheaf J AddCommGrpCat).obj
      (tuplePresheaf f n ⋙ AddCommGrpCat.free) ⟶ A) ≃
    (tuplePresheaf f n ⟶ A.obj ⋙ forget AddCommGrpCat) :=
  ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ A).trans
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ A.obj)

/-- The section equivalence reads the original free generator after the canonical adjunction. -/
theorem tupleSectionsEquiv_apply (n : ℕ) (A : Sheaf J AddCommGrpCat.{w})
    (m : (presheafToSheaf J AddCommGrpCat).obj
      (tuplePresheaf f n ⋙ AddCommGrpCat.free) ⟶ A) (U : Cᵒᵖ) (a : Tuple f n U) :
    (tupleSectionsEquiv f J n A m).app U a =
      (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ A m).app U)
        (FreeAbelianGroup.of a) := rfl

/-- A natural tuple-valued cochain extends along the two actual free/sheafification adjunctions. -/
def tupleLift {n : ℕ} {A : Sheaf J AddCommGrpCat.{w}}
    (c : tuplePresheaf f n ⟶ A.obj ⋙ forget AddCommGrpCat) :
    (presheafToSheaf J AddCommGrpCat).obj
      (tuplePresheaf f n ⋙ AddCommGrpCat.free) ⟶ A :=
  (tupleSectionsEquiv f J n A).symm c

/-- The extension to the actual degree `-n` term. -/
def resolutionTupleLift {n : ℕ} {A : Sheaf J AddCommGrpCat.{w}}
    (c : tuplePresheaf f n ⟶ A.obj ⋙ forget AddCommGrpCat) :
    (resolution f J).X (-(n : ℤ)) ⟶ A :=
  (resolutionTermIso f J n).hom ≫ tupleLift f J c

end CochainResolution

section StandardCochainResolution

variable {F' G' : Cᵒᵖ ⥤ Type (max u v)} (coverMap : F' ⟶ G')
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v}]
    [IsLocallySurjective J coverMap]

/-- The actual nonpositive free Čech cochain augmentation is a quasi-isomorphism. -/
theorem resolutionAugmentation_quasiIso : QuasiIso (resolutionAugmentation coverMap J) := by
  have hq : QuasiIso (HomologicalComplex.extendMap (sheafAugmentation coverMap J)
      ComplexShape.embeddingDownNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr
      (sheafAugmentation_quasiIso coverMap J)
  unfold resolutionAugmentation
  exact quasiIso_comp _ _ (hφ := hq)

end StandardCochainResolution

section TupleCocycles

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- The original alternating differential on the sheaf complex, read on free generators. -/
theorem tupleSectionsEquiv_d (n : ℕ) (A : Sheaf J AddCommGrpCat.{w})
    (m : (presheafToSheaf J AddCommGrpCat).obj
      (tuplePresheaf f n ⋙ AddCommGrpCat.free) ⟶ A) (U : Cᵒᵖ)
    (a : Tuple f (n + 1) U) :
    (tupleSectionsEquiv f J (n + 1) A
      ((sheafComplex f J).d (n + 1) n ≫ m)).app U a =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (tupleSectionsEquiv f J n A m).app U (tupleReindex f i.succAbove a) := by
  rw [tupleSectionsEquiv_apply]
  let d : tuplePresheaf f (n + 1) ⋙ AddCommGrpCat.free ⟶
      tuplePresheaf f n ⋙ AddCommGrpCat.free := (freeComplex f).d (n + 1) n
  change (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ A
    ((presheafToSheaf J AddCommGrpCat).map d ≫ m)).app U)
      (FreeAbelianGroup.of a) = _
  rw [Adjunction.homEquiv_naturality_left]
  change (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ A m).app U)
    ((d.app U) (FreeAbelianGroup.of a)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ A m).app U)
          (FreeAbelianGroup.of (tupleReindex f i.succAbove a))
  let b : FreeAbelianGroup (Tuple f n U) →+ A.obj.obj U :=
    (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ A m).app U).hom
  let ev : (AddCommGrpCat.free.obj (Tuple f (n + 1) U) ⟶
      AddCommGrpCat.free.obj (Tuple f n U)) →+ FreeAbelianGroup (Tuple f n U) :=
    { toFun g := g (FreeAbelianGroup.of a)
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hd : d.app U = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      AddCommGrpCat.free.map (↾(tupleReindex f i.succAbove)) := by
    simp [d, freeComplex, AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
      SimplicialObject.δ, SimplexCategory.δ, nerve, freeFunctor]
    rfl
  change b (ev (d.app U)) = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    b (FreeAbelianGroup.of (tupleReindex f i.succAbove a))
  erw [hd, _root_.map_sum, _root_.map_sum]
  simp only [_root_.map_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  change (-1 : ℤ) ^ (i : ℕ) •
      b (FreeAbelianGroup.map (tupleReindex f i.succAbove) (FreeAbelianGroup.of a)) =
    (-1 : ℤ) ^ (i : ℕ) • b (FreeAbelianGroup.of (tupleReindex f i.succAbove a))
  rw [FreeAbelianGroup.map_of_apply]

/-- The extension of a natural, closed tuple cochain is closed on the actual sheaf resolution. -/
theorem tupleLift_closed {n : ℕ} {A : Sheaf J AddCommGrpCat.{w}}
    (c : tuplePresheaf f n ⟶ A.obj ⋙ forget AddCommGrpCat)
    (hc : ∀ (U : Cᵒᵖ) (a : Tuple f (n + 1) U),
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        c.app U (tupleReindex f i.succAbove a) = 0) :
    (sheafComplex f J).d (n + 1) n ≫ tupleLift f J c = 0 := by
  apply (tupleSectionsEquiv f J (n + 1) A).injective
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro a
  change (tupleSectionsEquiv f J (n + 1) A
    ((sheafComplex f J).d (n + 1) n ≫ tupleLift f J c)).app U a = _
  rw [tupleSectionsEquiv_d f J n A (tupleLift f J c) U a]
  have hz : (tupleSectionsEquiv f J (n + 1) A 0).app U a = 0 := by
    change (((sheafificationAdjunction J AddCommGrpCat).homEquiv
      (tuplePresheaf f (n + 1) ⋙ AddCommGrpCat.free) A
      (0 : (presheafToSheaf J AddCommGrpCat).obj
        (tuplePresheaf f (n + 1) ⋙ AddCommGrpCat.free) ⟶ A)).app U)
          (FreeAbelianGroup.of a) = 0
    rw [Adjunction.homEquiv_unit]
    simp
    rfl
  simp only [tupleLift, Equiv.apply_symm_apply]
  exact (hc U a).trans hz.symm

/-- The cochain extension retains the alternating face differential, with no additional sign. -/
theorem resolution_d_term (n : ℕ) :
    (resolution f J).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (resolutionTermIso f J (n + 1)).hom ≫
        (sheafComplex f J).d (n + 1) n ≫ (resolutionTermIso f J n).inv :=
  (sheafComplex f J).extend_d_eq ComplexShape.embeddingDownNat rfl rfl

/-- A natural tuple cocycle is closed in the actual nonpositive cochain resolution. -/
theorem resolutionTupleLift_closed {n : ℕ} {A : Sheaf J AddCommGrpCat.{w}}
    (c : tuplePresheaf f n ⟶ A.obj ⋙ forget AddCommGrpCat)
    (hc : ∀ (U : Cᵒᵖ) (a : Tuple f (n + 1) U),
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        c.app U (tupleReindex f i.succAbove a) = 0) :
    (resolution f J).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
      resolutionTupleLift f J c = 0 := by
  let d : (presheafToSheaf J AddCommGrpCat).obj
      (tuplePresheaf f (n + 1) ⋙ AddCommGrpCat.free) ⟶
      (presheafToSheaf J AddCommGrpCat).obj
        (tuplePresheaf f n ⋙ AddCommGrpCat.free) := (sheafComplex f J).d (n + 1) n
  have hd : (resolution f J).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (resolutionTermIso f J (n + 1)).hom ≫ d ≫ (resolutionTermIso f J n).inv :=
    resolution_d_term f J n
  have hdc : d ≫ tupleLift f J c = 0 := tupleLift_closed f J c hc
  rw [hd]
  change ((resolutionTermIso f J (n + 1)).hom ≫ d ≫ (resolutionTermIso f J n).inv) ≫
    ((resolutionTermIso f J n).hom ≫ tupleLift f J c) = 0
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hdc, comp_zero]

end TupleCocycles

section DerivedRoof

universe z

variable {F' G' : Cᵒᵖ ⥤ Type (max u v)} (coverMap : F' ⟶ G')
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v}]
    [IsLocallySurjective J coverMap]
    [HasDerivedCategory.{z} (Sheaf J AddCommGrpCat.{max u v})]

open CochainComplex CochainComplex.HomComplex

omit [IsLocallySurjective J coverMap] [HasDerivedCategory (Sheaf J AddCommGrpCat)] in
/-- The actual degree-two cocycle, using the native Hom-complex constructor. -/
def degreeTwoCocycle {A : Sheaf J AddCommGrpCat.{max u v}}
    (c : (resolution coverMap J).X (-2) ⟶ A)
    (hc : (resolution coverMap J).d (-3) (-2) ≫ c = 0) :
    Cocycle (resolution coverMap J) ((CochainComplex.singleFunctor _ 0).obj A) 2 :=
  Cocycle.toSingleMk c (by norm_num) (-3) (by norm_num) hc

/-- The literal derived roof obtained by inverting the proved Čech augmentation. -/
def degreeTwoClass {A : Sheaf J AddCommGrpCat.{max u v}}
    (c : (resolution coverMap J).X (-2) ⟶ A)
    (hc : (resolution coverMap J).d (-3) (-2) ≫ c = 0) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((presheafToSheaf J AddCommGrpCat).obj (G' ⋙ AddCommGrpCat.free)) ⟶
    ((DerivedCategory.singleFunctor _ 0).obj A)⟦(2 : ℤ)⟧ := by
  haveI := resolutionAugmentation_quasiIso coverMap J
  exact inv (DerivedCategory.Q.map (resolutionAugmentation coverMap J)) ≫
    DerivedCategory.Q.map (Cocycle.equivHomShift.symm (degreeTwoCocycle coverMap J c hc)) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
        ((CochainComplex.singleFunctor _ 0).obj A)

omit [IsLocallySurjective J coverMap] [HasDerivedCategory (Sheaf J AddCommGrpCat)] in
/-- A literal primitive makes the actual degree-two cochain map null-homotopic. -/
theorem degreeTwoCocycle_nullHomotopic {A : Sheaf J AddCommGrpCat.{max u v}}
    (c : (resolution coverMap J).X (-2) ⟶ A)
    (hc : (resolution coverMap J).d (-3) (-2) ≫ c = 0)
    (p : (resolution coverMap J).X (-1) ⟶ A)
    (hp : (resolution coverMap J).d (-2) (-1) ≫ p = c) :
    Nonempty (Homotopy
      (Cocycle.equivHomShift.symm (degreeTwoCocycle coverMap J c hc)) 0) := by
  apply (HomotopyCategory.quotient_map_eq_zero_iff _).mp
  apply (CohomologyClass.toHom_mk_eq_zero_iff (degreeTwoCocycle coverMap J c hc)).mpr
  exact (Cocycle.toSingleMk_mem_coboundaries_iff c (by norm_num) (-3)
    (by norm_num) hc (-1) (by norm_num)).mpr ⟨p, hp⟩

/-- A primitive kills the class of the actual roof, retaining the original augmentation. -/
theorem degreeTwoClass_eq_zero_of_primitive {A : Sheaf J AddCommGrpCat.{max u v}}
    (c : (resolution coverMap J).X (-2) ⟶ A)
    (hc : (resolution coverMap J).d (-3) (-2) ≫ c = 0)
    (p : (resolution coverMap J).X (-1) ⟶ A)
    (hp : (resolution coverMap J).d (-2) (-1) ≫ p = c) :
    degreeTwoClass coverMap J c hc = 0 := by
  have h := DerivedCategory.Q_map_eq_of_homotopy (Sheaf J AddCommGrpCat)
    (degreeTwoCocycle_nullHomotopic coverMap J c hc p hp).some
  simp only [Functor.map_zero] at h
  simp [degreeTwoClass, h]

end DerivedRoof

end CategoryTheory.Presheaf.Cech
