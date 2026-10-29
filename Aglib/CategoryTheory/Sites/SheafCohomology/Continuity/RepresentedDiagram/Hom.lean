/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.InverseNaturality
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Plain represented Hom and original value diagrams

Ordinary systems and their actual left comparisons act on represented Hom by
source inverse transport, functoriality and coefficient postcomposition. The
identity, composition and coefficient squares require only preadditivity and
additive left functors.

For the actual value groups, an additive representing equivalence identifies
the supplied original maps with that Hom operation. The resulting functor and
coefficient transformation keep those original groups and maps literally.
The Hom and value universes remain independent. No Ext, derived model, abelian
category, exactness or replacement value carrier is used.
-/

@[expose] public noncomputable section

namespace CategoryTheory.InjectiveSystem

universe uI vI uA vA w

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)] (D : AdjunctionData A)
  [∀ i, Preadditive (A i)]
  (U : System D) [∀ {i j : I} (a : i ⟶ j), IsIso (U.leftMap D a)]
  [∀ {i j : I} (a : i ⟶ j), (D.left a).Additive]

/-- The original represented Hom operation, without an Ext realization. -/
def representedHomMap (F : System D) {i j : I} (a : i ⟶ j) :
    (U.obj i ⟶ F.obj i) →+ (U.obj j ⟶ F.obj j) :=
  AddMonoidHom.mk'
    (fun f => inv (U.leftMap D a) ≫ (D.left a).map f ≫ F.leftMap D a)
    (by
      intro f g
      simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add])

lemma representedHomMap_apply (F : System D) {i j : I} (a : i ⟶ j)
    (f : U.obj i ⟶ F.obj i) :
    representedHomMap D U F a f =
      inv (U.leftMap D a) ≫ (D.left a).map f ≫ F.leftMap D a := rfl

/-- Identity transport follows from the original left identity comparison. -/
lemma representedHomMap_id (F : System D) (i : I) :
    representedHomMap D U F (𝟙 i) = AddMonoidHom.id (U.obj i ⟶ F.obj i) := by
  ext f
  change inv (U.leftMap D (𝟙 i)) ≫ (D.left (𝟙 i)).map f ≫ F.leftMap D (𝟙 i) = f
  rw [System.leftMap_id D F, (D.leftIdIso i).hom.naturality]
  change inv (U.leftMap D (𝟙 i)) ≫ (D.leftIdIso i).hom.app (U.obj i) ≫ f = f
  rw [← System.leftMap_id D U]
  simp only [IsIso.inv_hom_id_assoc]

/-- Composition uses the two actual system laws and the original left comparison. -/
lemma representedHomMap_comp (F : System D) {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    representedHomMap D U F (a ≫ b) =
      (representedHomMap D U F b).comp (representedHomMap D U F a) := by
  ext f
  change inv (U.leftMap D (a ≫ b)) ≫
      (D.left (a ≫ b)).map f ≫ F.leftMap D (a ≫ b) =
    inv (U.leftMap D b) ≫
      (D.left b).map (inv (U.leftMap D a) ≫ (D.left a).map f ≫ F.leftMap D a) ≫
        F.leftMap D b
  apply (cancel_epi (U.leftMap D (a ≫ b))).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [System.leftMap_comp D F a b, System.leftMap_comp D U a b]
  simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id, Functor.map_id, Category.id_comp]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg
      (fun q : (D.left (a ≫ b)).obj (U.obj i) ⟶
          (D.left b).obj ((D.left a).obj (F.obj i)) =>
        q ≫ (D.left b).map (F.leftMap D a) ≫ F.leftMap D b)
      ((D.leftCompIso a b).hom.naturality f)

/-- A genuine coefficient-system square gives the whole original Hom square. -/
lemma representedHomMap_naturality {F G : System D} (η : System.Hom D F G)
    {i j : I} (a : i ⟶ j) :
    (Preadditive.rightComp (U.obj j) (η.app j)).comp (representedHomMap D U F a) =
      (representedHomMap D U G a).comp (Preadditive.rightComp (U.obj i) (η.app i)) := by
  ext f
  change (inv (U.leftMap D a) ≫ (D.left a).map f ≫ F.leftMap D a) ≫ η.app j =
    inv (U.leftMap D a) ≫ (D.left a).map (f ≫ η.app i) ≫ G.leftMap D a
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [System.Hom.leftMap_naturality D η a]

section Values

variable (F : System D) (S : I → AddCommGrpCat.{w})
  (m : ∀ {i j : I}, (i ⟶ j) → (S i ⟶ S j))
  (E : ∀ i, (U.obj i ⟶ F.obj i) ≃+ S i)
  (hm : ∀ {i j : I} (a : i ⟶ j) (f : U.obj i ⟶ F.obj i),
    E j (representedHomMap D U F a f) = m a (E i f))

include E hm

/-- The original value maps obey identity by their independently proved Hom formula. -/
lemma representedHomValuesMap_id (i : I) : m (𝟙 i) = 𝟙 (S i) := by
  ext s
  obtain ⟨f, rfl⟩ := (E i).surjective s
  change m (𝟙 i) (E i f) = E i f
  rw [← hm (𝟙 i) f, representedHomMap_id]
  rfl

/-- The original value maps compose by the ordinary represented Hom law. -/
lemma representedHomValuesMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    m (a ≫ b) = m a ≫ m b := by
  ext s
  obtain ⟨f, rfl⟩ := (E i).surjective s
  change m (a ≫ b) (E i f) = m b (m a (E i f))
  rw [← hm (a ≫ b) f, ← hm a f, ← hm b (representedHomMap D U F a f)]
  exact congrArg (fun q : (U.obj i ⟶ F.obj i) →+ (U.obj k ⟶ F.obj k) => E k (q f))
    (representedHomMap_comp D U F a b)

/-- The actual value diagram keeps the supplied groups and maps. Its laws,
rather than alternative section maps, are derived from the Hom operation. -/
def representedHomValuesFunctor : I ⥤ AddCommGrpCat.{w} where
  obj := S
  map := m
  map_id := representedHomValuesMap_id D U F S m E hm
  map_comp := representedHomValuesMap_comp D U F S m E hm

end Values

section Coefficients

variable {F G : System D} (η : System.Hom D F G)
  (S T : I → AddCommGrpCat.{w})
  (mF : ∀ {i j : I}, (i ⟶ j) → (S i ⟶ S j))
  (mG : ∀ {i j : I}, (i ⟶ j) → (T i ⟶ T j))
  (EF : ∀ i, (U.obj i ⟶ F.obj i) ≃+ S i)
  (EG : ∀ i, (U.obj i ⟶ G.obj i) ≃+ T i)
  (hF : ∀ {i j : I} (a : i ⟶ j) (f : U.obj i ⟶ F.obj i),
    EF j (representedHomMap D U F a f) = mF a (EF i f))
  (hG : ∀ {i j : I} (a : i ⟶ j) (f : U.obj i ⟶ G.obj i),
    EG j (representedHomMap D U G a f) = mG a (EG i f))
  (κ : ∀ i, S i ⟶ T i)
  (hκ : ∀ i (f : U.obj i ⟶ F.obj i), EG i (f ≫ η.app i) = κ i (EF i f))

include EF EG hF hG hκ

/-- Coefficient naturality of the actual value maps follows from their
representing formulas and the actual system morphism. -/
lemma representedHomValues_naturality {i j : I} (a : i ⟶ j) :
    mF a ≫ κ j = κ i ≫ mG a := by
  ext s
  obtain ⟨f, rfl⟩ := (EF i).surjective s
  change κ j (mF a (EF i f)) = mG a (κ i (EF i f))
  rw [← hF a f, ← hκ j (representedHomMap D U F a f), ← hκ i f,
    ← hG a (f ≫ η.app i)]
  exact congrArg
    (fun q : (U.obj i ⟶ F.obj i) →+ (U.obj j ⟶ G.obj j) => EG j (q f))
    (representedHomMap_naturality D U η a)

/-- The original coefficient maps form a transformation of the one actual
value diagram. No desired naturality equation is an input. -/
def representedHomValuesNatTrans :
    representedHomValuesFunctor D U F S mF EF hF ⟶
      representedHomValuesFunctor D U G T mG EG hG where
  app := κ
  naturality _ _ a := representedHomValues_naturality D U η S T mF mG EF EG hF hG κ hκ a

end Coefficients

end CategoryTheory.InjectiveSystem
