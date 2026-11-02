/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.CoefficientSquares
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Actual section squares, Arrow diagrams and their cone maps

The supplied section pullbacks satisfy only their original unit and composition
laws. The square calculus, Arrow functor and cone naturality are derived from
those laws and the one coherent adjunction data. All maps retain their literal
pullback followed by coefficient-map value.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem.AdjunctionData

universe uJ vJ uA vA uV vV uI vI

variable {J : Type uJ} [Category.{vJ} J]
  {A : J → Type uA} [∀ j, Category.{vA} (A j)]
  (D : InjectiveSystem.AdjunctionData A)
  (V : Type uV) [Category.{vV} V]

/-- Actual section functors and their original pullbacks, with structural laws
before any coefficient square, indexing diagram or cone is chosen. -/
structure Sections where
  /-- The section functor on each stage category. -/
  value : ∀ j, A j ⥤ V
  /-- The natural map from sections at a stage to sections after the left transition. -/
  pullback : ∀ {i j : J} (a : i ⟶ j), value i ⟶ D.left a ⋙ value j
  id : ∀ (i : J) (F : A i),
    (pullback (𝟙 i)).app F ≫ (value i).map ((D.leftIdIso i).hom.app F) = 𝟙 _
  comp : ∀ {i j k : J} (a : i ⟶ j) (b : j ⟶ k) (F : A i),
    (pullback (a ≫ b)).app F ≫ (value k).map ((D.leftCompIso a b).hom.app F) =
      (pullback a).app F ≫ (pullback b).app ((D.left a).obj F)

attribute [reassoc] Sections.comp

variable {V} (S : D.Sections V) (hD : D.Coherent)

namespace Sections

variable {D}

/-- Pull sections back and apply the actual coefficient square. -/
def squareMap {i j i' j' : J}
    (f : i ⟶ j) (f' : i' ⟶ j') (g : i ⟶ i') (h : j ⟶ j')
    (e : g ≫ f' = f ≫ h) {F : A i} {G : A i'} (φ : (D.left g).obj F ⟶ G) :
    (S.value j).obj ((D.left f).obj F) ⟶ (S.value j').obj ((D.left f').obj G) :=
  (S.pullback h).app ((D.left f).obj F) ≫
    (S.value j').map (D.squareCoefficientMap f f' g h e φ)

include hD in
/-- Identity squares use the original unit, with no additional square law. -/
theorem squareMap_id {i j : J} (f : i ⟶ j)
    (e : 𝟙 i ≫ f = f ≫ 𝟙 j) (F : A i) :
    S.squareMap f f (𝟙 i) (𝟙 j) e ((D.leftIdIso i).hom.app F) = 𝟙 _ := by
  dsimp only [squareMap]
  rw [D.squareCoefficientMap_id hD, S.id]

include hD in
/-- Horizontal pasting follows from the original coefficient-square pasting. -/
theorem squareMap_comp {i₀ j₀ i₁ j₁ i₂ j₂ : J}
    (f₀ : i₀ ⟶ j₀) (f₁ : i₁ ⟶ j₁) (f₂ : i₂ ⟶ j₂)
    (g₁ : i₀ ⟶ i₁) (g₂ : i₁ ⟶ i₂) (h₁ : j₀ ⟶ j₁) (h₂ : j₁ ⟶ j₂)
    (e₁ : g₁ ≫ f₁ = f₀ ≫ h₁) (e₂ : g₂ ≫ f₂ = f₁ ≫ h₂)
    (e : (g₁ ≫ g₂) ≫ f₂ = f₀ ≫ (h₁ ≫ h₂))
    {F : A i₀} {G : A i₁} {H : A i₂}
    (φ : (D.left g₁).obj F ⟶ G) (ψ : (D.left g₂).obj G ⟶ H) :
    S.squareMap f₀ f₁ g₁ h₁ e₁ φ ≫ S.squareMap f₁ f₂ g₂ h₂ e₂ ψ =
      S.squareMap f₀ f₂ (g₁ ≫ g₂) (h₁ ≫ h₂) e
        ((D.leftCompIso g₁ g₂).hom.app F ≫ (D.left g₂).map φ ≫ ψ) := by
  dsimp only [squareMap]
  simp only [Category.assoc]
  rw [(S.pullback h₂).naturality_assoc, ← S.comp_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  rw [D.squareCoefficientMap_hComp hD f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e]

/-- Equality of base arrows transports the original section square itself. -/
theorem squareMap_transport {i j i' j' : J}
    (f : i ⟶ j) (f' : i' ⟶ j') (g g' : i ⟶ i') (h h' : j ⟶ j')
    (eg : g' = g) (eh : h' = h)
    (e : g ≫ f' = f ≫ h) (e' : g' ≫ f' = f ≫ h')
    {F : A i} {G : A i'} (φ : (D.left g).obj F ⟶ G) :
    S.squareMap f f' g' h' e'
      ((eqToIso (congrArg D.left eg)).hom.app F ≫ φ) =
        S.squareMap f f' g h e φ := by
  cases eg
  cases eh
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

end Sections

section Reindex

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ J)

/-- Reindexing retains the actual left identity comparison and its equality transport. -/
theorem leftIdIso_reindex (i : I) :
    (D.reindex X).leftIdIso i =
      eqToIso (congrArg D.left (X.map_id i)) ≪≫ D.leftIdIso (X.obj i) := by
  have hl := Adjunction.conjugateEquiv_leftAdjointIdIso_hom
    ((D.reindex X).adj (𝟙 i)) ((D.reindex X).idIso i)
  have hr :
      conjugateEquiv Adjunction.id (D.adj (X.map (𝟙 i)))
        (eqToIso (congrArg D.left (X.map_id i)) ≪≫ D.leftIdIso (X.obj i)).hom =
          ((D.reindex X).idIso i).inv := by
    dsimp only [Iso.trans_hom, eqToIso.hom]
    rw [← conjugateEquiv_comp Adjunction.id (D.adj (𝟙 (X.obj i))),
      D.conjugate_left_eqToHom (X.map_id i), AdjunctionData.leftIdIso,
      Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
    rfl
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id ((D.reindex X).adj (𝟙 i))).injective
  exact hl.trans hr.symm

/-- Reindexing retains the actual left composition comparison and its equality transport. -/
theorem leftCompIso_reindex {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    (D.reindex X).leftCompIso a b =
      eqToIso (congrArg D.left (X.map_comp a b)) ≪≫ D.leftCompIso (X.map a) (X.map b) := by
  have hl := (D.reindex X).conjugate_leftCompIso_hom a b
  have hr :
      conjugateEquiv ((D.adj (X.map a)).comp (D.adj (X.map b)))
        (D.adj (X.map (a ≫ b)))
        (eqToIso (congrArg D.left (X.map_comp a b)) ≪≫
          D.leftCompIso (X.map a) (X.map b)).hom = ((D.reindex X).compIso a b).inv := by
    dsimp only [Iso.trans_hom, eqToIso.hom]
    rw [← conjugateEquiv_comp ((D.adj (X.map a)).comp (D.adj (X.map b)))
      (D.adj (X.map a ≫ X.map b)), D.conjugate_left_eqToHom (X.map_comp a b),
      D.conjugate_leftCompIso_hom]
    rfl
  apply Iso.ext
  apply (conjugateEquiv (((D.reindex X).adj a).comp ((D.reindex X).adj b))
    ((D.reindex X).adj (a ≫ b))).injective
  exact hl.trans hr.symm

namespace Sections

variable {D}

variable (F : System (D.reindex X))

/-- The actual system transition with the original reindexing unit transport. -/
theorem systemTransition_id (i : I) :
    F.leftMap (D.reindex X) (𝟙 i) =
      (eqToIso (congrArg D.left (X.map_id i))).hom.app (F.obj i) ≫
        (D.leftIdIso (X.obj i)).hom.app (F.obj i) := by
  have h := congrArg (fun e => e.hom.app (F.obj i)) (D.leftIdIso_reindex X i)
  simp only [Iso.trans_hom, NatTrans.comp_app] at h
  exact (System.leftMap_id (D.reindex X) F i).trans h

/-- The actual system transition with the original reindexing composition transport. -/
theorem systemTransition_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    F.leftMap (D.reindex X) (a ≫ b) =
      (eqToIso (congrArg D.left (X.map_comp a b))).hom.app (F.obj i) ≫
        (D.leftCompIso (X.map a) (X.map b)).hom.app (F.obj i) ≫
          (D.left (X.map b)).map (F.leftMap (D.reindex X) a) ≫
            F.leftMap (D.reindex X) b := by
  have h := congrArg
    (fun e => e.hom.app (F.obj i) ≫
      (D.left (X.map b)).map (F.leftMap (D.reindex X) a) ≫ F.leftMap (D.reindex X) b)
    (D.leftCompIso_reindex X a b)
  simp only [Iso.trans_hom, NatTrans.comp_app] at h
  have hm := System.leftMap_comp (D.reindex X) F a b
  change F.leftMap (D.reindex X) (a ≫ b) =
    ((D.reindex X).leftCompIso a b).hom.app (F.obj i) ≫
      (D.left (X.map b)).map (F.leftMap (D.reindex X) a) ≫ F.leftMap (D.reindex X) b at hm
  have hfinal := hm.trans h
  exact hfinal.trans (Category.assoc
    ((eqToIso (congrArg D.left (X.map_comp a b))).hom.app (F.obj i))
    ((D.leftCompIso (X.map a) (X.map b)).hom.app (F.obj i))
    ((D.left (X.map b)).map (F.leftMap (D.reindex X) a) ≫ F.leftMap (D.reindex X) b))

/-- Sections of the system across a square over the actual indexing diagram. -/
def systemSquareMap {i j : I} (a : i ⟶ j) {y z : J}
    (f : X.obj i ⟶ y) (g : X.obj j ⟶ z) (h : y ⟶ z)
    (e : X.map a ≫ g = f ≫ h) :
    (S.value y).obj ((D.left f).obj (F.obj i)) ⟶
      (S.value z).obj ((D.left g).obj (F.obj j)) :=
  S.squareMap f g (X.map a) h e (F.leftMap (D.reindex X) a)

/-- Equal indexing arrows yield the same original system square. -/
theorem systemSquareMap_congr {i j : I} (a b : i ⟶ j) (hab : a = b)
    {y z : J} (f : X.obj i ⟶ y) (g : X.obj j ⟶ z) (h : y ⟶ z)
    (ea : X.map a ≫ g = f ≫ h) (eb : X.map b ≫ g = f ≫ h) :
    S.systemSquareMap X F a f g h ea = S.systemSquareMap X F b f g h eb := by
  cases hab
  rfl

include hD in
/-- System-square pasting retains both original functor-law transports. -/
theorem systemSquareMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k)
    {y₀ y₁ y₂ : J} (f₀ : X.obj i ⟶ y₀) (f₁ : X.obj j ⟶ y₁) (f₂ : X.obj k ⟶ y₂)
    (h₁ : y₀ ⟶ y₁) (h₂ : y₁ ⟶ y₂) (t : y₀ ⟶ y₂) (et : t = h₁ ≫ h₂)
    (e₁ : X.map a ≫ f₁ = f₀ ≫ h₁) (e₂ : X.map b ≫ f₂ = f₁ ≫ h₂)
    (e : X.map (a ≫ b) ≫ f₂ = f₀ ≫ t) :
    S.systemSquareMap X F (a ≫ b) f₀ f₂ t e =
      S.systemSquareMap X F a f₀ f₁ h₁ e₁ ≫ S.systemSquareMap X F b f₁ f₂ h₂ e₂ := by
  dsimp only [systemSquareMap]
  rw [systemTransition_comp]
  let e' : (X.map a ≫ X.map b) ≫ f₂ = f₀ ≫ (h₁ ≫ h₂) := by
    rw [Category.assoc, e₂, ← Category.assoc, e₁, Category.assoc]
  let φ := (D.leftCompIso (X.map a) (X.map b)).hom.app (F.obj i) ≫
    (D.left (X.map b)).map (F.leftMap (D.reindex X) a) ≫ F.leftMap (D.reindex X) b
  have ht := S.squareMap_transport f₀ f₂ (X.map a ≫ X.map b) (X.map (a ≫ b))
    (h₁ ≫ h₂) t (X.map_comp a b) et e' e φ
  have hp := S.squareMap_comp hD f₀ f₁ f₂ (X.map a) (X.map b) h₁ h₂ e₁ e₂ e'
    (F.leftMap (D.reindex X) a) (F.leftMap (D.reindex X) b)
  exact ht.trans hp.symm

/-- The actual square of a mapped Arrow morphism. -/
theorem arrowSquare {a b : Arrow I} (m : a ⟶ b) :
    X.map m.left ≫ X.map b.hom = X.map a.hom ≫ X.map m.right :=
  (X.map_comp m.left b.hom).symm.trans
    ((congrArg X.map m.w).trans (X.map_comp a.hom m.right))

/-- Sections at the target of the indexed arrow, with its source coefficient. -/
abbrev arrowObj (a : Arrow I) : V :=
  (S.value (X.obj a.right)).obj ((D.left (X.map a.hom)).obj (F.obj a.left))

/-- The original square section map of an Arrow morphism. -/
def arrowMap {a b : Arrow I} (m : a ⟶ b) : S.arrowObj X F a ⟶ S.arrowObj X F b :=
  S.systemSquareMap X F m.left (X.map a.hom) (X.map b.hom) (X.map m.right)
    (arrowSquare X m)

include hD in
/-- The Arrow identity follows from system and square units. -/
theorem arrowMap_id (a : Arrow I) : S.arrowMap X F (𝟙 a) = 𝟙 _ := by
  dsimp only [arrowMap, systemSquareMap]
  change S.squareMap (X.map a.hom) (X.map a.hom)
    (X.map (𝟙 a.left)) (X.map (𝟙 a.right)) _ (F.leftMap (D.reindex X) (𝟙 a.left)) = _
  rw [systemTransition_id]
  exact (S.squareMap_transport (X.map a.hom) (X.map a.hom)
    (𝟙 _) (X.map (𝟙 a.left)) (𝟙 _) (X.map (𝟙 a.right))
    (X.map_id a.left) (X.map_id a.right) (by simp only [Category.id_comp, Category.comp_id])
    _ ((D.leftIdIso (X.obj a.left)).hom.app (F.obj a.left))).trans
      (S.squareMap_id hD _ _ _)

include hD in
/-- The Arrow composition follows from the full system-square pasting law. -/
theorem arrowMap_comp {a b c : Arrow I} (m : a ⟶ b) (n : b ⟶ c) :
    S.arrowMap X F (m ≫ n) = S.arrowMap X F m ≫ S.arrowMap X F n := by
  exact S.systemSquareMap_comp hD X F m.left n.left
    (X.map a.hom) (X.map b.hom) (X.map c.hom)
    (X.map m.right) (X.map n.right) (X.map (m.right ≫ n.right)) (X.map_comp _ _)
    (arrowSquare X m) (arrowSquare X n) (arrowSquare X (m ≫ n))

/-- The complete Arrow section functor stores the supplied original maps,
identified with the derived square maps before applying their functor laws. -/
def arrowFunctorWithMap
    (map : ∀ {a b : Arrow I}, (a ⟶ b) → (S.arrowObj X F a ⟶ S.arrowObj X F b))
    (hmap : ∀ {a b : Arrow I} (m : a ⟶ b), map m = S.arrowMap X F m) : Arrow I ⥤ V where
  obj := S.arrowObj X F
  map := map
  map_id a := (hmap (𝟙 a)).trans (S.arrowMap_id hD X F a)
  map_comp m n := by
    simp only [hmap]
    exact S.arrowMap_comp hD X F m n

variable (c : Cocone X)

/-- The original cocone equation, before applying any section functor. -/
theorem coneSquare {i j : I} (a : i ⟶ j) : X.map a ≫ c.ι.app j = c.ι.app i := c.w a

/-- The original identity-indexed square from an arrow to the cocone point. -/
theorem coneArrowSquare (a : Arrow I) :
    X.map (𝟙 a.left) ≫ c.ι.app a.left = X.map a.hom ≫ c.ι.app a.right := by
  rw [X.map_id, Category.id_comp, c.w]

/-- Pull the arrow section to the actual cocone point. -/
def coneArrowMap (a : Arrow I) : S.arrowObj X F a ⟶
    (S.value c.pt).obj ((D.left (c.ι.app a.left)).obj (F.obj a.left)) :=
  S.systemSquareMap X F (𝟙 a.left) (X.map a.hom) (c.ι.app a.left) (c.ι.app a.right)
    (coneArrowSquare X c a)

/-- The system transition at the same actual cocone point. -/
def coneSystemMap {i j : I} (a : i ⟶ j) :
    (S.value c.pt).obj ((D.left (c.ι.app i)).obj (F.obj i)) ⟶
      (S.value c.pt).obj ((D.left (c.ι.app j)).obj (F.obj j)) :=
  S.systemSquareMap X F a (c.ι.app i) (c.ι.app j) (𝟙 _)
    ((c.w a).trans (Category.comp_id _).symm)

include hD in
/-- Two original system-square pastings prove cone naturality. -/
theorem coneArrowMap_naturality {a b : Arrow I} (m : a ⟶ b) :
    S.arrowMap X F m ≫ S.coneArrowMap X F c b =
      S.coneArrowMap X F c a ≫ S.coneSystemMap X F c m.left := by
  let e : X.map m.left ≫ c.ι.app b.left = X.map a.hom ≫ c.ι.app a.right :=
    (c.w m.left).trans (c.w a.hom).symm
  let e₁ : X.map (m.left ≫ 𝟙 b.left) ≫ c.ι.app b.left =
      X.map a.hom ≫ c.ι.app a.right := by simpa only [Category.comp_id] using e
  let e₂ : X.map (𝟙 a.left ≫ m.left) ≫ c.ι.app b.left =
      X.map a.hom ≫ c.ι.app a.right := by simpa only [Category.id_comp] using e
  have h₁ := S.systemSquareMap_comp hD X F m.left (𝟙 b.left)
    (X.map a.hom) (X.map b.hom) (c.ι.app b.left)
    (X.map m.right) (c.ι.app b.right) (c.ι.app a.right)
    (c.w m.right).symm (arrowSquare X m) (coneArrowSquare X c b) e₁
  have h₂ := S.systemSquareMap_comp hD X F (𝟙 a.left) m.left
    (X.map a.hom) (c.ι.app a.left) (c.ι.app b.left)
    (c.ι.app a.right) (𝟙 _) (c.ι.app a.right)
    (Category.comp_id _).symm (coneArrowSquare X c a)
    ((c.w m.left).trans (Category.comp_id _).symm) e₂
  have hi := S.systemSquareMap_congr X F (m.left ≫ 𝟙 b.left) m.left
    (Category.comp_id m.left) (X.map a.hom) (c.ι.app b.left) (c.ι.app a.right) e₁ e
  have hj := S.systemSquareMap_congr X F (𝟙 a.left ≫ m.left) m.left
    (Category.id_comp m.left) (X.map a.hom) (c.ι.app b.left) (c.ι.app a.right) e₂ e
  exact h₁.symm.trans (hi.trans (hj.symm.trans h₂))

end Sections
end Reindex

end CategoryTheory.InjectiveSystem.AdjunctionData
