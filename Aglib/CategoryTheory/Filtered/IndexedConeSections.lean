/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Filtered.SectionDiagrams

/-! # The original indexed row into its actual cone coefficient sections

The whole construction uses the supplied section data, indexed structural map,
original cone legs, and the existing cone's chosen left triangles and mates.
The source stores the original square maps; the target is the original
coefficient functor followed by sections. Both comparison equations and row
naturality are proved before specializing any base or coefficient category.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem.AdjunctionData.Sections

universe uJ vJ uA vA uV vV uI vI uK vK

variable {J : Type uJ} [Category.{vJ} J]
  {A : J → Type uA} [∀ j, Category.{vA} (A j)]
  {D : InjectiveSystem.AdjunctionData A}
  {V : Type uV} [Category.{vV} V] (S : D.Sections V)

private theorem pullback_id_inverse (j : J) (M : A j) :
    (S.pullback (𝟙 j)).app M = (S.value j).map ((D.leftIdIso j).inv.app M) := by
  let e := (S.value j).mapIso ((D.leftIdIso j).app M)
  have h : (S.pullback (𝟙 j)).app M = 𝟙 ((S.value j).obj M) ≫ e.inv :=
    e.eq_comp_inv.mpr (S.id j M)
  exact h.trans (Category.id_comp e.inv)

private theorem squareMap_top_id (hD : D.Coherent) {i j t : J}
    (f : i ⟶ j) (p : t ⟶ j) (g : i ⟶ t) (e : g ≫ p = f)
    {M : A i} {N : A t} (φ : (D.left g).obj M ⟶ N) :
    S.squareMap f p g (𝟙 j) (e.trans (Category.comp_id f).symm) φ =
      (S.value j).map (D.triangleCoefficientMap g f p e φ) := by
  dsimp only [squareMap]
  rw [pullback_id_inverse, ← Functor.map_comp]
  exact congrArg (S.value j).map (D.squareCoefficientMap_top_id hD f p g e φ)

variable (hD : D.Coherent)
  {I : Type uI} [Category.{vI} I] (X : I ⥤ J) (F : System (D.reindex X))
  {K : Type uK} [Category.{vK} K] (s : K ⥤ I) (Y : K ⥤ J) (q : s ⋙ X ⟶ Y)
  (c : Cocone X) (r : Y ⟶ (Functor.const K).obj c.pt)
  (h : ∀ k, q.app k ≫ r.app k = c.ι.app (s.obj k))
  (triangle : ∀ {i j : I} (a : i ⟶ j),
    D.left (c.ι.app i) ≅ D.left (X.map a) ⋙ D.left (c.ι.app j))
  (mate : ∀ {i j : I} (a : i ⟶ j),
    conjugateEquiv ((D.adj (X.map a)).comp (D.adj (c.ι.app j)))
      (D.adj (c.ι.app i)) (triangle a).hom =
        (Cone.coconeRightTriangle D X c a).hom)

include mate in
/-- The supplied existing mate identifies the chosen whole left triangle. -/
private theorem chosenTriangle_hom_eq {i j : I} (a : i ⟶ j) :
    (triangle a).hom =
      (D.triangleIso (c.ι.app i) (X.map a) (c.ι.app j) (c.w a)).hom := by
  apply (conjugateEquiv ((D.adj (X.map a)).comp (D.adj (c.ι.app j)))
    (D.adj (c.ι.app i))).injective
  exact (mate a).trans
    (D.conjugate_triangleIso_hom (c.ι.app i) (X.map a) (c.ι.app j) (c.w a)).symm

include hD mate in
/-- The fixed-apex square is the section image of the original chosen coefficient map. -/
private theorem coneSystemMap_eq_chosenCoefficient {i j : I} (a : i ⟶ j) :
    S.coneSystemMap X F c a =
      (S.value c.pt).map ((triangle a).hom.app (F.obj i) ≫
        (D.left (c.ι.app j)).map (F.leftMap (D.reindex X) a)) := by
  have ht := chosenTriangle_hom_eq X c triangle mate a
  exact (S.squareMap_top_id hD (c.ι.app i) (c.ι.app j) (X.map a)
    (c.w a) (F.leftMap (D.reindex X) a)).trans
      (congrArg (fun k : D.left (c.ι.app i) ⟶ D.left (X.map a) ⋙ D.left (c.ι.app j) =>
        (S.value c.pt).map (k.app (F.obj i) ≫
          (D.left (c.ι.app j)).map (F.leftMap (D.reindex X) a))) ht.symm)

variable
  (map : ∀ {i j : K}, (i ⟶ j) → (S.indexedObj X F s Y q i ⟶ S.indexedObj X F s Y q j))
  (hmap : ∀ {i j : K} (a : i ⟶ j), map a = S.indexedMap X F s Y q a)
  (app : ∀ k, S.indexedObj X F s Y q k ⟶
    (S.value c.pt).obj ((D.left (c.ι.app (s.obj k))).obj (F.obj (s.obj k))))
  (happ : ∀ k, app k = S.indexedConeMap X F s Y q c r h k)

/-- Assemble the whole original indexed row and its canonical coefficient-section
target. The cone record update is the existing construction with its supplied
left triangles; it changes neither the adjunctions nor the right comparisons. -/
def indexedConeNatTransWithMap :
    S.indexedFunctorWithMap hD X F s Y q map hmap ⟶
      s ⋙ ({ Cone.ofCocone D hD X c with
          leftTriangle := triangle
          conjugate := mate } : (D.reindex X).Cone (A c.pt)).coefficientSectionsFunctor
        F (S.value c.pt) where
  app := app
  naturality {i j} a := by
    change map a ≫ app j = app i ≫
      (S.value c.pt).map ((triangle (s.map a)).hom.app (F.obj (s.obj i)) ≫
        (D.left (c.ι.app (s.obj j))).map (F.leftMap (D.reindex X) (s.map a)))
    simp only [hmap, happ]
    exact (S.indexedConeMap_naturality hD X F s Y q c r h a).trans
      (congrArg (fun k => S.indexedConeMap X F s Y q c r h i ≫ k)
        (S.coneSystemMap_eq_chosenCoefficient hD X F c triangle mate (s.map a)))

/-- The whole construction has the literal supplied original component. -/
@[simp]
theorem indexedConeNatTransWithMap_app (k : K) :
    (S.indexedConeNatTransWithMap hD X F s Y q c r h triangle mate map hmap app happ).app k =
      app k := rfl

end CategoryTheory.InjectiveSystem.AdjunctionData.Sections
