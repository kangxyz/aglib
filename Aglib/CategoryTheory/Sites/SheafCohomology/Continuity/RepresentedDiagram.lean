/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.InverseNaturality
public import Aglib.Algebra.Homology.DerivedCategory.Ext.CompositeComparison

/-!
# Represented Ext diagrams in varying abelian categories

The representing objects form an actual system whose left transitions are
isomorphisms. Exact left adjoints transport native Ext, and the coefficient
system supplies the original Yoneda postcomposition. Identity, composition and
coefficient naturality follow from the ordinary system laws, not from assumed
cohomology-transition laws. No site, injective existence or continuity theorem
is required. The current consumer is the original étale cohomology diagram.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.InjectiveSystem

universe uI vI uA vA e

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)] (D : AdjunctionData A)

variable (U : System D)
  [∀ {i j : I} (a : i ⟶ j), IsIso (U.leftMap D a)]

/-- The inverse original source transitions retain the native left composition comparison. -/
lemma System.leftMap_inv_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    inv (U.leftMap D (a ≫ b)) ≫ (D.leftCompIso a b).hom.app (U.obj i) =
      inv (U.leftMap D b) ≫ (D.left b).map (inv (U.leftMap D a)) := by
  apply (cancel_mono ((D.left b).map (U.leftMap D a) ≫ U.leftMap D b)).mp
  calc
    _ = inv (U.leftMap D (a ≫ b)) ≫ U.leftMap D (a ≫ b) := by
      simpa only [Category.assoc] using
        (congrArg
          (fun f : (D.left (a ≫ b)).obj (U.obj i) ⟶ U.obj k =>
            inv (U.leftMap D (a ≫ b)) ≫ f)
          (U.leftMap_comp D a b)).symm
    _ = 𝟙 _ := IsIso.inv_hom_id _
    _ = _ := by
      simp only [Category.assoc, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
        Functor.map_id, Category.id_comp]

variable [∀ i, Abelian (A i)] [∀ i, HasExt.{e} (A i)]
  [∀ {i j : I} (a : i ⟶ j), (D.left a).Additive]
  [∀ {i j : I} (a : i ⟶ j), PreservesFiniteLimits (D.left a)]
  [∀ {i j : I} (a : i ⟶ j), PreservesFiniteColimits (D.left a)]

/-- Native source transport composes through the original exact-functor comparison. -/
lemma representedExtPrecomp_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k)
    (M : A i) (n : ℕ) (x : Ext.{e} (U.obj i) M n) :
    ((D.left (a ≫ b)).extPrecompMap (inv (U.leftMap D (a ≫ b))) M n x).comp
        (Ext.mk₀ ((D.leftCompIso a b).hom.app M)) (add_zero n) =
      (D.left b).extPrecompMap (inv (U.leftMap D b)) ((D.left a).obj M) n
        ((D.left a).extPrecompMap (inv (U.leftMap D a)) M n x) := by
  rw [Functor.extPrecompMap_apply, Ext.comp_assoc_of_third_deg_zero,
    Ext.mapExactFunctor_comp_mk₀_natTransApp, Ext.mk₀_comp_mk₀_assoc,
    System.leftMap_inv_comp]
  exact (D.left a).extPrecompMap_compFunctor (D.left b)
    (inv (U.leftMap D a)) (inv (U.leftMap D b)) M n x

/-- The native represented Ext group at an index, in its independent Ext universe. -/
abbrev representedCohomologyObj (F : System D) (n : ℕ) (i : I) : AddCommGrpCat.{e} :=
  AddCommGrpCat.of (Ext.{e} (U.obj i) (F.obj i) n)

/-- Exact transport of native Ext followed by the actual coefficient transition. -/
def representedCohomologyMap (F : System D) (n : ℕ) {i j : I} (a : i ⟶ j) :
    representedCohomologyObj D U F n i ⟶ representedCohomologyObj D U F n j :=
  AddCommGrpCat.ofHom
    (((Ext.mk₀ (F.leftMap D a)).postcomp (U.obj j) (add_zero n)).comp
      ((D.left a).extPrecompMap (inv (U.leftMap D a)) (F.obj i) n))

/-- The transition is the original exact-functor/source/coefficient formula. -/
lemma representedCohomologyMap_apply (F : System D) (n : ℕ) {i j : I} (a : i ⟶ j)
    (x : Ext.{e} (U.obj i) (F.obj i) n) :
    representedCohomologyMap D U F n a x =
      ((D.left a).extPrecompMap (inv (U.leftMap D a)) (F.obj i) n x).comp
        (Ext.mk₀ (F.leftMap D a)) (add_zero n) := rfl

/-- In degree zero the transition is the actual transported morphism. -/
lemma representedCohomologyMap_mk₀ (F : System D) {i j : I} (a : i ⟶ j)
    (f : U.obj i ⟶ F.obj i) :
    representedCohomologyMap D U F 0 a (Ext.mk₀ f) =
      Ext.mk₀ (inv (U.leftMap D a) ≫ (D.left a).map f ≫ F.leftMap D a) := by
  rw [representedCohomologyMap_apply, Functor.extPrecompMap_mk₀,
    Ext.mk₀_comp_mk₀]
  simp only [Category.assoc]

lemma representedCohomologyMap_id (F : System D) (n : ℕ) (i : I) :
    representedCohomologyMap D U F n (𝟙 i) = 𝟙 _ := by
  ext x
  rw [representedCohomologyMap_apply, Functor.extPrecompMap_apply,
    System.leftMap_id D F, Ext.comp_assoc_of_third_deg_zero,
    Ext.mapExactFunctor_comp_mk₀_natTransApp, Ext.id_mapExactFunctor,
    ← System.leftMap_id D U, Ext.mk₀_comp_mk₀_assoc]
  simp

lemma representedCohomologyMap_comp (F : System D) (n : ℕ) {i j k : I}
    (a : i ⟶ j) (b : j ⟶ k) :
    representedCohomologyMap D U F n (a ≫ b) =
      representedCohomologyMap D U F n a ≫ representedCohomologyMap D U F n b := by
  ext x
  change ((D.left (a ≫ b)).extPrecompMap _ (F.obj i) n x).comp
      (Ext.mk₀ (F.leftMap D (a ≫ b))) (add_zero n) =
    ((D.left b).extPrecompMap _ (F.obj j) n
      (((D.left a).extPrecompMap _ (F.obj i) n x).comp
        (Ext.mk₀ (F.leftMap D a)) (add_zero n))).comp
          (Ext.mk₀ (F.leftMap D b)) (add_zero n)
  rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀,
    ← representedExtPrecomp_comp D U a b, System.leftMap_comp D F a b]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]

/-- The actual represented cohomology diagram, derived from ordinary system laws. -/
def representedCohomologyFunctor (F : System D) (n : ℕ) : I ⥤ AddCommGrpCat.{e} where
  obj := representedCohomologyObj D U F n
  map := representedCohomologyMap D U F n
  map_id := representedCohomologyMap_id D U F n
  map_comp := representedCohomologyMap_comp D U F n

/-- A coefficient-system square gives the original native Ext coefficient square. -/
lemma representedCohomologyMap_naturality {F G : System D} (η : System.Hom D F G)
    (n : ℕ) {i j : I} (a : i ⟶ j) :
    representedCohomologyMap D U F n a ≫
        AddCommGrpCat.ofHom ((Ext.mk₀ (η.app j)).postcomp (U.obj j) (add_zero n)) =
      AddCommGrpCat.ofHom ((Ext.mk₀ (η.app i)).postcomp (U.obj i) (add_zero n)) ≫
        representedCohomologyMap D U G n a := by
  ext x
  change (((D.left a).extPrecompMap _ (F.obj i) n x).comp
      (Ext.mk₀ (F.leftMap D a)) (add_zero n)).comp (Ext.mk₀ (η.app j)) (add_zero n) =
    ((D.left a).extPrecompMap _ (G.obj i) n
      (x.comp (Ext.mk₀ (η.app i)) (add_zero n))).comp
        (Ext.mk₀ (G.leftMap D a)) (add_zero n)
  rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rw [System.Hom.leftMap_naturality]

/-- Actual coefficient-system morphisms act by native Yoneda coefficient maps. -/
def representedCohomologyNatTrans {F G : System D} (η : System.Hom D F G) (n : ℕ) :
    representedCohomologyFunctor D U F n ⟶ representedCohomologyFunctor D U G n where
  app i := AddCommGrpCat.ofHom ((Ext.mk₀ (η.app i)).postcomp (U.obj i) (add_zero n))
  naturality _ _ a := representedCohomologyMap_naturality D U η n a

end CategoryTheory.InjectiveSystem
