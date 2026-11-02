/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.SectionArrows
public import Aglib.CategoryTheory.Filtered.CoefficientSections

/-! # Original indexed test sections and their cone maps

Actual source indexing, target bases and a natural structural map determine
all section objects and square maps. The original unit/composition laws prove
the functor and the two actual cone-square pastings prove cone naturality.
No pulled-System colimit, Ext, invertibility or final naturality is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The original test projection at an Arrow uses its source coefficient
and target test base, with naturality derived from the actual Arrow square. -/
def arrowProjection {I K J : Type*} [Category* I] [Category* K] [Category* J]
    (s : K ⥤ I) (X : I ⥤ J) (Y : K ⥤ J) (τ : s ⋙ X ⟶ Y) :
    (Arrow.leftFunc ⋙ s) ⋙ X ⟶ Arrow.rightFunc ⋙ Y where
  app a := (s ⋙ X).map a.hom ≫ τ.app a.right
  naturality {a b} m := by
    change (s ⋙ X).map m.left ≫ ((s ⋙ X).map b.hom ≫ τ.app b.right) =
      ((s ⋙ X).map a.hom ≫ τ.app a.right) ≫ Y.map m.right
    calc
      (s ⋙ X).map m.left ≫ ((s ⋙ X).map b.hom ≫ τ.app b.right) =
          (s ⋙ X).map (m.left ≫ b.hom) ≫ τ.app b.right := by
        rw [Functor.map_comp, Category.assoc]
      _ = (s ⋙ X).map (a.hom ≫ m.right) ≫ τ.app b.right :=
        congrArg (fun z => (s ⋙ X).map z ≫ τ.app b.right) m.w
      _ = (s ⋙ X).map a.hom ≫ ((s ⋙ X).map m.right ≫ τ.app b.right) := by
        rw [Functor.map_comp, Category.assoc]
      _ = (s ⋙ X).map a.hom ≫ (τ.app a.right ≫ Y.map m.right) :=
        congrArg (fun z => (s ⋙ X).map a.hom ≫ z) (τ.naturality m.right)
      _ = ((s ⋙ X).map a.hom ≫ τ.app a.right) ≫ Y.map m.right :=
        (Category.assoc _ _ _).symm

/-- The actual projection/cocone square determines the original Arrow cone leg. -/
theorem arrowProjection_comp_cocone
    {I K J : Type*} [Category* I] [Category* K] [Category* J]
    (s : K ⥤ I) (X : I ⥤ J) (Y : K ⥤ J) (τ : s ⋙ X ⟶ Y)
    (c : Cocone X) (d : Cocone Y) (l : c.pt ⟶ d.pt)
    (h : ∀ k, τ.app k ≫ d.ι.app k = c.ι.app (s.obj k) ≫ l) (a : Arrow K) :
    (arrowProjection s X Y τ).app a ≫ d.ι.app a.right =
      c.ι.app (s.obj a.left) ≫ l := by
  change ((s ⋙ X).map a.hom ≫ τ.app a.right) ≫ d.ι.app a.right = _
  rw [Category.assoc, h a.right, ← Category.assoc]
  exact congrArg (fun z => z ≫ l) (c.w (s.map a.hom))

end CategoryTheory.Functor

namespace CategoryTheory.InjectiveSystem.AdjunctionData.Sections

universe uJ vJ uA vA uV vV uI vI uK vK

variable {J : Type uJ} [Category.{vJ} J]
  {A : J → Type uA} [∀ j, Category.{vA} (A j)]
  {D : InjectiveSystem.AdjunctionData A}
  {V : Type uV} [Category.{vV} V] (S : D.Sections V) (hD : D.Coherent)
  {I : Type uI} [Category.{vI} I] (X : I ⥤ J) (F : System (D.reindex X))
  {K : Type uK} [Category.{vK} K] (s : K ⥤ I) (Y : K ⥤ J) (q : s ⋙ X ⟶ Y)

/-- Original sections at the actual target base of the actual source coefficient. -/
abbrev indexedObj (i : K) : V :=
  (S.value (Y.obj i)).obj ((D.left (q.app i)).obj (F.obj (s.obj i)))

/-- The complete original square section map. -/
def indexedMap {i j : K} (a : i ⟶ j) : S.indexedObj X F s Y q i ⟶ S.indexedObj X F s Y q j :=
  S.systemSquareMap X F (s.map a) (q.app i) (q.app j) (Y.map a) (q.naturality a)

include hD in
/-- Indexed identities follow from the original system and section units. -/
theorem indexedMap_id (i : K) : S.indexedMap X F s Y q (𝟙 i) = 𝟙 _ := by
  have eq : X.map (𝟙 (s.obj i)) ≫ q.app i = q.app i ≫ Y.map (𝟙 i) := by
    simpa only [Functor.comp_map, s.map_id] using q.naturality (𝟙 i)
  have hs : S.indexedMap X F s Y q (𝟙 i) =
      S.systemSquareMap X F (𝟙 (s.obj i)) (q.app i) (q.app i) (Y.map (𝟙 i)) eq :=
    S.systemSquareMap_congr X F (s.map (𝟙 i)) (𝟙 (s.obj i)) (s.map_id i)
      (q.app i) (q.app i) (Y.map (𝟙 i)) (q.naturality (𝟙 i)) eq
  refine hs.trans ?_
  dsimp only [systemSquareMap]
  change S.squareMap (q.app i) (q.app i) (X.map (𝟙 (s.obj i))) (Y.map (𝟙 i)) eq
    (F.leftMap (D.reindex X) (𝟙 (s.obj i))) = 𝟙 _
  rw [systemTransition_id]
  exact (S.squareMap_transport (q.app i) (q.app i)
    (𝟙 (X.obj (s.obj i))) (X.map (𝟙 (s.obj i)))
    (𝟙 (Y.obj i)) (Y.map (𝟙 i)) (X.map_id (s.obj i)) (Y.map_id i)
    ((Category.id_comp (q.app i)).trans (Category.comp_id (q.app i)).symm) eq
    ((D.leftIdIso (X.obj (s.obj i))).hom.app (F.obj (s.obj i)))).trans
      (S.squareMap_id hD _ _ _)

include hD in
/-- Indexed composition is derived from the original square pasting law. -/
theorem indexedMap_comp {i j k : K} (a : i ⟶ j) (b : j ⟶ k) :
    S.indexedMap X F s Y q (a ≫ b) =
      S.indexedMap X F s Y q a ≫ S.indexedMap X F s Y q b := by
  have e := q.naturality (a ≫ b)
  change X.map (s.map (a ≫ b)) ≫ q.app k = q.app i ≫ Y.map (a ≫ b) at e
  rw [s.map_comp] at e
  exact (S.systemSquareMap_congr X F (s.map (a ≫ b)) (s.map a ≫ s.map b)
    (s.map_comp a b) (q.app i) (q.app k) (Y.map (a ≫ b)) (q.naturality (a ≫ b)) e).trans
      (S.systemSquareMap_comp hD X F (s.map a) (s.map b)
        (q.app i) (q.app j) (q.app k) (Y.map a) (Y.map b) (Y.map (a ≫ b))
        (Y.map_comp a b) (q.naturality a) (q.naturality b) e)

include hD in
/-- Construct the whole original functor, retaining the supplied actual map
values after their equality with the derived square maps is proved. -/
def indexedFunctorWithMap
    (map : ∀ {i j : K}, (i ⟶ j) → (S.indexedObj X F s Y q i ⟶ S.indexedObj X F s Y q j))
    (hmap : ∀ {i j : K} (a : i ⟶ j), map a = S.indexedMap X F s Y q a) : K ⥤ V where
  obj := S.indexedObj X F s Y q
  map := map
  map_id i := (hmap (𝟙 i)).trans (S.indexedMap_id hD X F s Y q i)
  map_comp a b := by
    simp only [hmap]
    exact S.indexedMap_comp hD X F s Y q a b

variable (c : Cocone X) (r : Y ⟶ (Functor.const K).obj c.pt)
  (h : ∀ i, q.app i ≫ r.app i = c.ι.app (s.obj i))

include h in
/-- The original relative row leg, at the fixed original cone point. -/
def indexedConeMap (i : K) : S.indexedObj X F s Y q i ⟶
    (S.value c.pt).obj ((D.left (c.ι.app (s.obj i))).obj (F.obj (s.obj i))) :=
  S.systemSquareMap X F (𝟙 (s.obj i)) (q.app i) (c.ι.app (s.obj i)) (r.app i)
    (by rw [X.map_id, Category.id_comp]; exact (h i).symm)

include hD in
/-- Two actual square pastings give the complete relative-cone naturality law. -/
theorem indexedConeMap_naturality {i j : K} (a : i ⟶ j) :
    S.indexedMap X F s Y q a ≫ S.indexedConeMap X F s Y q c r h j =
      S.indexedConeMap X F s Y q c r h i ≫ S.coneSystemMap X F c (s.map a) := by
  let u := s.map a
  have hr : Y.map a ≫ r.app j = r.app i :=
    (r.naturality a).trans (Category.comp_id _)
  let e : X.map u ≫ c.ι.app (s.obj j) = q.app i ≫ r.app i :=
    (c.w u).trans (h i).symm
  let e₁ : X.map (u ≫ 𝟙 (s.obj j)) ≫ c.ι.app (s.obj j) = q.app i ≫ r.app i := by
    simpa only [Category.comp_id] using e
  let e₂ : X.map (𝟙 (s.obj i) ≫ u) ≫ c.ι.app (s.obj j) = q.app i ≫ r.app i := by
    simpa only [Category.id_comp] using e
  have h₁ := S.systemSquareMap_comp hD X F u (𝟙 (s.obj j))
    (q.app i) (q.app j) (c.ι.app (s.obj j))
    (Y.map a) (r.app j) (r.app i) hr.symm (q.naturality a)
    (by rw [X.map_id, Category.id_comp]; exact (h j).symm) e₁
  have h₂ := S.systemSquareMap_comp hD X F (𝟙 (s.obj i)) u
    (q.app i) (c.ι.app (s.obj i)) (c.ι.app (s.obj j))
    (r.app i) (𝟙 c.pt) (r.app i) (Category.comp_id _).symm
    (by rw [X.map_id, Category.id_comp]; exact (h i).symm)
    ((c.w u).trans (Category.comp_id _).symm) e₂
  have hi := S.systemSquareMap_congr X F (u ≫ 𝟙 (s.obj j)) u (Category.comp_id _)
    (q.app i) (c.ι.app (s.obj j)) (r.app i) e₁ e
  have hj := S.systemSquareMap_congr X F (𝟙 (s.obj i) ≫ u) u (Category.id_comp _)
    (q.app i) (c.ι.app (s.obj j)) (r.app i) e₂ e
  exact h₁.symm.trans (hi.trans (hj.symm.trans h₂))

end CategoryTheory.InjectiveSystem.AdjunctionData.Sections
