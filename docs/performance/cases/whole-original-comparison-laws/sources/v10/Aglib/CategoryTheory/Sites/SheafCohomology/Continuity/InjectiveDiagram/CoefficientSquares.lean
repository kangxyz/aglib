/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeConstancy
public import Aglib.CategoryTheory.Adjunction.Mates.Coherence

/-! # Actual coefficient maps across coherent squares

Square comparisons use the one supplied adjunction data and its original
identity and composition comparisons. The adjunct value calculations also
apply to independently sized source, intermediate and target categories.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction.CoefficientSquares

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃

variable {A : Type u₀} [Category.{v₀} A] {B : Type u₁} [Category.{v₁} B]
  {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]
  {L_g : A ⥤ B} {L_v₀ : A ⥤ C} {L_v₁ : B ⥤ D} {L_h : C ⥤ D}

/-- Transport an actual coefficient map through the supplied whole square comparison. -/
abbrev coefficientMap (s : L_g ⋙ L_v₁ ≅ L_v₀ ⋙ L_h)
    {F : A} {G : B} (φ : L_g.obj F ⟶ G) : L_h.obj (L_v₀.obj F) ⟶ L_v₁.obj G :=
  s.inv.app F ≫ L_v₁.map φ

section TriangleEquation

universe uT₀ vT₀ uT₁ vT₁

variable {T₀ : Type uT₀} [Category.{vT₀} T₀]
  {T₁ : Type uT₁} [Category.{vT₁} T₁]
  {L : T₀ ⥤ T₁} {P₀ : A ⥤ T₀} {P₁ : B ⥤ T₀}
  {Q₀ : C ⥤ T₁} {Q₁ : D ⥤ T₁}

/-- The whole triangle-square equation, before evaluating objects or coefficient maps. -/
def WholeTriangleSquareEquation
    (t_g : P₀ ≅ L_g ⋙ P₁) (t_h : Q₀ ≅ L_h ⋙ Q₁)
    (s : L_g ⋙ L_v₁ ≅ L_v₀ ⋙ L_h)
    (s₀ : L_v₀ ⋙ Q₀ ≅ P₀ ⋙ L) (s₁ : L_v₁ ⋙ Q₁ ≅ P₁ ⋙ L) : Prop :=
  Functor.whiskerLeft L_v₀ t_h.hom ≫
      (Functor.associator L_v₀ L_h Q₁).inv ≫
      Functor.whiskerRight s.inv Q₁ ≫
      (Functor.associator L_g L_v₁ Q₁).hom ≫
      Functor.whiskerLeft L_g s₁.hom =
    s₀.hom ≫ Functor.whiskerRight t_g.hom L ≫
      (Functor.associator L_g P₁ L).hom

end TriangleEquation

end CategoryTheory.Adjunction.CoefficientSquares

namespace CategoryTheory.InjectiveSystem.AdjunctionData

universe uJ vJ uA vA

variable {J : Type uJ} [Category.{vJ} J]
  {A : J → Type uA} [∀ j, Category.{vA} (A j)]
  (D : InjectiveSystem.AdjunctionData A)

/-- The actual whole left comparison of a commuting base square. -/
def squareIso {S₀ X₀ S₁ X₁ : J}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h) :
    D.left g ⋙ D.left f₁ ≅ D.left f₀ ⋙ D.left h :=
  (D.leftCompIso g f₁).symm ≪≫ eqToIso (congrArg D.left e) ≪≫ D.leftCompIso f₀ h

/-- The actual whole right comparison of the same commuting base square. -/
def squareRightIso {S₀ X₀ S₁ X₁ : J}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h) :
    D.right h ⋙ D.right f₀ ≅ D.right f₁ ⋙ D.right g :=
  (D.compIso f₀ h).symm ≪≫ eqToIso (congrArg D.right e.symm) ≪≫ D.compIso g f₁

/-- The original coefficient map transported by the inverse whole square. -/
def squareCoefficientMap {S₀ X₀ S₁ X₁ : J}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h) {F : A S₀} {G : A S₁}
    (φ : (D.left g).obj F ⟶ G) :
    (D.left h).obj ((D.left f₀).obj F) ⟶ (D.left f₁).obj G :=
  Adjunction.CoefficientSquares.coefficientMap (L_g := D.left g) (L_v₀ := D.left f₀)
    (L_v₁ := D.left f₁) (L_h := D.left h) (D.squareIso f₀ f₁ g h e) φ

theorem squareIso_transpose {S₀ X₀ S₁ X₁ : J}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h) :
    D.squareIso g h f₀ f₁ e.symm = (D.squareIso f₀ f₁ g h e).symm := by
  simp only [squareIso, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

theorem squareRightIso_transpose {S₀ X₀ S₁ X₁ : J}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h) :
    D.squareRightIso g h f₀ f₁ e.symm = (D.squareRightIso f₀ f₁ g h e).symm := by
  simp only [squareRightIso, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

/-- Actual equality transport conjugates in the reversed right-adjoint direction. -/
theorem conjugate_left_eqToHom {i j : J} {f g : i ⟶ j} (e : f = g) :
    conjugateEquiv (D.adj g) (D.adj f) (eqToHom (congrArg D.left e)) =
      eqToHom (congrArg D.right e.symm) := by
  cases e
  simp

/-- The supplied right composition comparison is the mate of the canonical left one. -/
theorem conjugate_leftCompIso_hom {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    conjugateEquiv ((D.adj a).comp (D.adj b)) (D.adj (a ≫ b))
      (D.leftCompIso a b).hom = (D.compIso a b).inv :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

/-- The native inverse composition comparison has the original inverse mate. -/
theorem conjugate_leftCompIso_inv {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    conjugateEquiv (D.adj (a ≫ b)) ((D.adj a).comp (D.adj b))
      (D.leftCompIso a b).inv = (D.compIso a b).hom := by
  apply (cancel_epi (D.compIso a b).inv).1
  rw [← D.conjugate_leftCompIso_hom a b, conjugateEquiv_comp,
    Iso.inv_hom_id, conjugateEquiv_id, D.conjugate_leftCompIso_hom, Iso.inv_hom_id]

/-- The complete selected left square conjugates to the complete original right square. -/
theorem conjugate_squareIso_hom {S₀ X₀ S₁ X₁ : J}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h) :
    conjugateEquiv ((D.adj f₀).comp (D.adj h)) ((D.adj g).comp (D.adj f₁))
      (D.squareIso f₀ f₁ g h e).hom = (D.squareRightIso f₀ f₁ g h e).hom := by
  dsimp only [squareIso, squareRightIso, Iso.trans_hom, Iso.symm_hom]
  simp only [eqToIso.hom]
  rw [← conjugateEquiv_comp ((D.adj f₀).comp (D.adj h)) (D.adj (g ≫ f₁)),
    ← conjugateEquiv_comp ((D.adj f₀).comp (D.adj h)) (D.adj (f₀ ≫ h)),
    D.conjugate_leftCompIso_hom, D.conjugate_left_eqToHom e,
    D.conjugate_leftCompIso_inv, Category.assoc]

/-- The original inverse square has the original inverse right-square value. -/
theorem conjugate_squareIso_inv {S₀ X₀ S₁ X₁ : J}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h) :
    conjugateEquiv ((D.adj g).comp (D.adj f₁)) ((D.adj f₀).comp (D.adj h))
      (D.squareIso f₀ f₁ g h e).inv = (D.squareRightIso f₀ f₁ g h e).inv := by
  have ht := D.conjugate_squareIso_hom g h f₀ f₁ e.symm
  rw [D.squareIso_transpose f₀ f₁ g h e, D.squareRightIso_transpose f₀ f₁ g h e] at ht
  exact ht

/-- The actual triangle comparisons have their actual right-triangle mates. -/
theorem conjugate_triangleIso_hom {x y t : J}
    (p : x ⟶ t) (f : x ⟶ y) (q : y ⟶ t) (e : f ≫ q = p) :
    conjugateEquiv ((D.adj f).comp (D.adj q)) (D.adj p)
      (D.triangleIso p f q e).hom = (D.triangleRightIso p f q e).hom := by
  rw [D.triangleIso_eq_leftAdjointCompIso]
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

variable (hD : D.Coherent)

include hD in
/-- The whole right-unit comparison follows from the supplied right coherence. -/
theorem leftCompIso_comp_id_whole {i j : J} (a : i ⟶ j) :
    D.leftCompIso a (𝟙 j) ≪≫
        Functor.isoWhiskerLeft (D.left a) (D.leftIdIso j) ≪≫
        Functor.rightUnitor (D.left a) =
      eqToIso (congrArg D.left (Category.comp_id a)) := by
  let e := D.triangleRightIso a a (𝟙 j) (Category.comp_id a)
  have he : e = Functor.isoWhiskerRight (D.idIso j) (D.right a) ≪≫
      Functor.leftUnitor (D.right a) := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    have h := congrArg (fun f => (D.compIso a (𝟙 j)).inv.app K ≫ f) (hD.comp_id a K)
    have hv : (D.compIso a (𝟙 j)).inv.app K ≫
        eqToHom (congrArg (fun f => (D.right f).obj K) (Category.comp_id a)) =
          (D.right a).map ((D.idIso j).hom.app K) := by
      simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using h.symm
    simpa only [e, triangleRightIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, eqToIso.hom, eqToHom_app, Functor.id_obj] using
        hv.trans (Category.comp_id _).symm
  have hu := Adjunction.leftAdjointCompIso_comp_id (D.adj a) (D.adj (𝟙 j))
    e (D.idIso j) he
  have hm : Adjunction.leftAdjointCompIso (D.adj a) (D.adj (𝟙 j)) (D.adj a) e =
      (D.triangleIso a a (𝟙 j) (Category.comp_id a)).symm :=
    (congrArg Iso.symm (D.triangleIso_eq_leftAdjointCompIso
      a a (𝟙 j) (Category.comp_id a))).symm
  rw [hm] at hu
  change (D.triangleIso a a (𝟙 j) (Category.comp_id a)).symm =
    Functor.isoWhiskerLeft (D.left a) (D.leftIdIso j) ≪≫ Functor.rightUnitor (D.left a) at hu
  calc
    _ = D.leftCompIso a (𝟙 j) ≪≫
        (D.triangleIso a a (𝟙 j) (Category.comp_id a)).symm := by rw [hu]
    _ = _ := by
      apply Iso.ext
      simp only [triangleIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
        eqToIso.hom, eqToIso.inv, Iso.hom_inv_id_assoc]

include hD in
/-- The whole left-unit comparison follows from the supplied right coherence. -/
theorem leftCompIso_id_comp_whole {i j : J} (a : i ⟶ j) :
    D.leftCompIso (𝟙 i) a ≪≫
        Functor.isoWhiskerRight (D.leftIdIso i) (D.left a) ≪≫
        Functor.leftUnitor (D.left a) =
      eqToIso (congrArg D.left (Category.id_comp a)) := by
  let e := D.triangleRightIso a (𝟙 i) a (Category.id_comp a)
  have he : e = Functor.isoWhiskerLeft (D.right a) (D.idIso i) ≪≫
      Functor.rightUnitor (D.right a) := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    have h := congrArg (fun f => (D.compIso (𝟙 i) a).inv.app K ≫ f) (hD.id_comp a K)
    have hv : (D.compIso (𝟙 i) a).inv.app K ≫
        eqToHom (congrArg (fun f => (D.right f).obj K) (Category.id_comp a)) =
          (D.idIso i).hom.app ((D.right a).obj K) := by
      simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using h.symm
    simpa only [e, triangleRightIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, eqToIso.hom, eqToHom_app, Functor.id_obj] using
        hv.trans (Category.comp_id _).symm
  have hu := Adjunction.leftAdjointCompIso_id_comp (D.adj (𝟙 i)) (D.adj a)
    e (D.idIso i) he
  have hm : Adjunction.leftAdjointCompIso (D.adj (𝟙 i)) (D.adj a) (D.adj a) e =
      (D.triangleIso a (𝟙 i) a (Category.id_comp a)).symm :=
    (congrArg Iso.symm (D.triangleIso_eq_leftAdjointCompIso
      a (𝟙 i) a (Category.id_comp a))).symm
  rw [hm] at hu
  change (D.triangleIso a (𝟙 i) a (Category.id_comp a)).symm =
    Functor.isoWhiskerRight (D.leftIdIso i) (D.left a) ≪≫ Functor.leftUnitor (D.left a) at hu
  calc
    _ = D.leftCompIso (𝟙 i) a ≪≫
        (D.triangleIso a (𝟙 i) a (Category.id_comp a)).symm := by rw [hu]
    _ = _ := by
      apply Iso.ext
      simp only [triangleIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
        eqToIso.hom, eqToIso.inv, Iso.hom_inv_id_assoc]

include hD in
/-- Identity squares retain the whole original left-unit comparisons. -/
theorem squareIso_id {i j : J} (f : i ⟶ j) (e : 𝟙 i ≫ f = f ≫ 𝟙 j) :
    D.squareIso f f (𝟙 i) (𝟙 j) e ≪≫
        Functor.isoWhiskerLeft (D.left f) (D.leftIdIso j) ≪≫
        Functor.rightUnitor (D.left f) =
      Functor.isoWhiskerRight (D.leftIdIso i) (D.left f) ≪≫
        Functor.leftUnitor (D.left f) := by
  apply Iso.ext
  apply (cancel_epi (D.leftCompIso (𝟙 i) f).hom).1
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hA := congrArg Iso.hom (D.leftCompIso_id_comp_whole hD f)
  have hB := congrArg Iso.hom (D.leftCompIso_comp_id_whole hD f)
  simp only [Iso.trans_hom] at hA hB
  rw [hB, hA]
  simp only [eqToIso.hom, eqToHom_trans]

include hD in
/-- The actual coefficient identity square is the original stage identity map. -/
theorem squareCoefficientMap_id {i j : J} (f : i ⟶ j)
    (e : 𝟙 i ≫ f = f ≫ 𝟙 j) (F : A i) :
    D.squareCoefficientMap f f (𝟙 i) (𝟙 j) e ((D.leftIdIso i).hom.app F) =
      (D.leftIdIso j).hom.app ((D.left f).obj F) := by
  have hc := congrArg (fun z => z.hom.app F) (D.squareIso_id hD f e)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at hc
  change (D.squareIso f f (𝟙 i) (𝟙 j) e).hom.app F ≫
      (D.leftIdIso j).hom.app ((D.left f).obj F) ≫ 𝟙 _ =
    (D.left f).map ((D.leftIdIso i).hom.app F) ≫ 𝟙 _ at hc
  let m := (D.leftIdIso j).hom.app ((D.left f).obj F)
  let n := (D.left f).map ((D.leftIdIso i).hom.app F)
  have hc' : (D.squareIso f f (𝟙 i) (𝟙 j) e).hom.app F ≫ m = n :=
    (congrArg
      (fun k => (D.squareIso f f (𝟙 i) (𝟙 j) e).hom.app F ≫ k)
      (Category.comp_id m)).symm.trans (hc.trans (Category.comp_id n))
  have ht := congrArg (fun k => (D.squareIso f f (𝟙 i) (𝟙 j) e).inv.app F ≫ k) hc'
  simpa only [squareCoefficientMap, Adjunction.CoefficientSquares.coefficientMap,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp, m, n] using ht.symm

include hD in
/-- The whole base-identity square is the inverse original triangle comparison. -/
theorem squareIso_base_id {i j t : J}
    (f : i ⟶ j) (p : i ⟶ t) (h : j ⟶ t) (e : f ≫ h = p) :
    (D.squareIso f p (𝟙 i) h ((Category.id_comp p).trans e.symm)).symm ≪≫
        Functor.isoWhiskerRight (D.leftIdIso i) (D.left p) ≪≫
        Functor.leftUnitor (D.left p) = (D.triangleIso p f h e).symm := by
  have hu := D.leftCompIso_id_comp_whole hD p
  have ht := congrArg
    (fun z : D.left (𝟙 i ≫ p) ≅ D.left p =>
      (D.leftCompIso f h).symm ≪≫
        (eqToIso (congrArg D.left ((Category.id_comp p).trans e.symm))).symm ≪≫ z) hu
  apply Iso.ext
  have hth := congrArg Iso.hom ht
  simpa only [squareIso, triangleIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc, eqToIso.hom, eqToIso.inv,
    eqToHom_trans] using hth

include hD in
/-- The original coefficient identity map gives the actual inverse triangle value. -/
theorem squareCoefficientMap_base_id {i j t : J}
    (f : i ⟶ j) (p : i ⟶ t) (h : j ⟶ t) (e : f ≫ h = p) (F : A i) :
    D.squareCoefficientMap f p (𝟙 i) h ((Category.id_comp p).trans e.symm)
      ((D.leftIdIso i).hom.app F) = (D.triangleIso p f h e).inv.app F := by
  have hc := congrArg (fun z => z.hom.app F) (D.squareIso_base_id hD f p h e)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app] at hc
  let m : (D.left p).obj ((D.left (𝟙 i)).obj F) ⟶ (D.left p).obj F :=
    (D.left p).map ((D.leftIdIso i).hom.app F)
  change (D.squareIso f p (𝟙 i) h _).inv.app F ≫ m ≫ 𝟙 _ = _ at hc
  exact (congrArg
    (fun k => (D.squareIso f p (𝟙 i) h ((Category.id_comp p).trans e.symm)).inv.app F ≫ k)
    (Category.comp_id m)).symm.trans hc

include hD in
/-- The whole top-identity square is the original direct triangle comparison. -/
theorem squareIso_top_id {i j t : J}
    (f : i ⟶ j) (p : t ⟶ j) (g : i ⟶ t) (e : g ≫ p = f) :
    (Functor.rightUnitor (D.left f)).symm ≪≫
        Functor.isoWhiskerLeft (D.left f) (D.leftIdIso j).symm ≪≫
        (D.squareIso f p g (𝟙 j) (e.trans (Category.comp_id f).symm)).symm =
      D.triangleIso f g p e := by
  have hu := congrArg Iso.symm (D.leftCompIso_comp_id_whole hD f)
  have ht := congrArg
    (fun z : D.left f ≅ D.left (f ≫ 𝟙 j) => z ≪≫
      (eqToIso (congrArg D.left (e.trans (Category.comp_id f).symm))).symm ≪≫
        D.leftCompIso g p) hu
  apply Iso.ext
  have hth := congrArg Iso.hom ht
  simpa only [squareIso, triangleIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerLeft_hom, Category.assoc, eqToIso.hom, eqToIso.inv,
    eqToHom_trans_assoc] using hth

include hD in
/-- The actual top-identity coefficient square is the original triangle map. -/
theorem squareCoefficientMap_top_id {i j t : J}
    (f : i ⟶ j) (p : t ⟶ j) (g : i ⟶ t) (e : g ≫ p = f)
    {F : A i} {G : A t} (φ : (D.left g).obj F ⟶ G) :
    (D.leftIdIso j).inv.app ((D.left f).obj F) ≫
        D.squareCoefficientMap f p g (𝟙 j) (e.trans (Category.comp_id f).symm) φ =
      D.triangleCoefficientMap g f p e φ := by
  have hc := congrArg (fun z => z.hom.app F) (D.squareIso_top_id hD f p g e)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at hc
  let m : (D.left f).obj F ⟶ (D.left p).obj ((D.left g).obj F) :=
    (D.leftIdIso j).inv.app ((D.left f).obj F) ≫
      (D.squareIso f p g (𝟙 j) (e.trans (Category.comp_id f).symm)).inv.app F
  change 𝟙 _ ≫ m = _ at hc
  have hc' := (Category.id_comp m).symm.trans hc
  have ht := congrArg (fun k => k ≫ (D.left p).map φ) hc'
  simpa only [squareCoefficientMap, Adjunction.CoefficientSquares.coefficientMap,
    triangleCoefficientMap, Category.assoc, m] using ht

/-- Transport of both square arrows preserves the same actual coefficient map. -/
theorem squareCoefficientMap_transport {S₀ X₀ S₁ X₁ : J}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g g' : S₀ ⟶ S₁) (h h' : X₀ ⟶ X₁)
    (eg : g' = g) (eh : h' = h)
    (e : g ≫ f₁ = f₀ ≫ h) (e' : g' ≫ f₁ = f₀ ≫ h')
    {F : A S₀} {G : A S₁} (φ : (D.left g).obj F ⟶ G) :
    D.squareCoefficientMap f₀ f₁ g' h' e'
      (eqToHom (congrArg (fun k => (D.left k).obj F) eg) ≫ φ) =
        eqToHom (congrArg (fun k => (D.left k).obj ((D.left f₀).obj F)) eh) ≫
          D.squareCoefficientMap f₀ f₁ g h e φ := by
  cases eg
  cases eh
  simp only [eqToHom_refl, Category.id_comp]

include hD in
/-- Original left associativity as a whole natural-transformation equation. -/
theorem leftCompIso_assoc_whole {i j k t : J}
    (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ t) :
    (D.leftCompIso a (b ≫ c)).hom ≫
        Functor.whiskerLeft (D.left a) (D.leftCompIso b c).hom =
      eqToHom (congrArg D.left (Category.assoc a b c).symm) ≫
        (D.leftCompIso (a ≫ b) c).hom ≫
          Functor.whiskerRight (D.leftCompIso a b).hom (D.left c) ≫
            (Functor.associator (D.left a) (D.left b) (D.left c)).hom := by
  apply NatTrans.ext
  funext F
  have h := D.leftCompIso_assoc_hom hD a b c F
  have ht := congrArg
    (fun k => eqToHom (congrArg (fun f => (D.left f).obj F)
      (Category.assoc a b c).symm) ≫ k) h
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id, eqToHom_app, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using ht.symm

include hD in
theorem leftCompIso_assoc_start_whole {i j k t : J}
    (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ t) :
    (D.leftCompIso (a ≫ b) c).hom ≫
        (Functor.whiskerRight (D.leftCompIso a b).hom (D.left c) ≫
          (Functor.associator (D.left a) (D.left b) (D.left c)).hom) ≫
        Functor.whiskerLeft (D.left a) (D.leftCompIso b c).inv =
      (eqToIso (congrArg D.left (Category.assoc a b c).symm)).inv ≫
        (D.leftCompIso a (b ≫ c)).hom :=
  exchangeCoherence_rotate_start _ _ _ _ _ _ _
    (Iso.inv_hom_id _) (Iso.hom_inv_id (Functor.isoWhiskerLeft
      (D.left a) (D.leftCompIso b c))) (D.leftCompIso_assoc_whole hD a b c).symm

include hD in
theorem leftCompIso_assoc_finish_whole {i j k t : J}
    (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ t) :
    (D.leftCompIso (a ≫ b) c).hom ≫
        Functor.whiskerRight (D.leftCompIso a b).hom (D.left c) ≫
          (Functor.associator (D.left a) (D.left b) (D.left c)).hom =
      (eqToIso (congrArg D.left (Category.assoc a b c).symm)).inv ≫
        (D.leftCompIso a (b ≫ c)).hom ≫
          Functor.whiskerLeft (D.left a) (D.leftCompIso b c).hom :=
  exchangeCoherence_rotate_finish _ _ _ _ (Iso.inv_hom_id _)
    (D.leftCompIso_assoc_whole hD a b c).symm

theorem leftCompIso_eqToHom_right_whole {i j k : J}
    (a : i ⟶ j) {b b' : j ⟶ k} (e : b = b') :
    (D.leftCompIso a b).hom ≫
        Functor.whiskerLeft (D.left a) (eqToHom (congrArg D.left e)) =
      eqToHom (congrArg D.left (congrArg (fun f => a ≫ f) e)) ≫
        (D.leftCompIso a b').hom := by
  cases e
  simp

theorem leftCompIso_eqToHom_left_whole {i j k : J}
    {a a' : i ⟶ j} (e : a = a') (b : j ⟶ k) :
    (D.leftCompIso a b).hom ≫
        Functor.whiskerRight (eqToHom (congrArg D.left e)) (D.left b) =
      eqToHom (congrArg D.left (congrArg (fun f => f ≫ b) e)) ≫
        (D.leftCompIso a' b).hom := by
  cases e
  simp

private lemma inverse_pasting {C : Type*} [Category C]
    {U V R T W : C} (a : T ≅ W) (b : R ≅ T) (c : U ≅ V)
    (p : U ⟶ R) (l : V ⟶ W) (h : p ≫ b.hom ≫ a.hom = c.hom ≫ l) :
    l ≫ a.inv ≫ b.inv = c.inv ≫ p := by
  have ht := congrArg (fun k : U ⟶ W => c.inv ≫ k ≫ a.inv ≫ b.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Iso.inv_hom_id_assoc, Category.comp_id] using ht.symm

section Horizontal

variable {S₀ X₀ S₁ X₁ S₂ X₂ : J}
  (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (f₂ : S₂ ⟶ X₂)
  (g₁ : S₀ ⟶ S₁) (g₂ : S₁ ⟶ S₂) (h₁ : X₀ ⟶ X₁) (h₂ : X₁ ⟶ X₂)
  (e₁ : g₁ ≫ f₁ = f₀ ≫ h₁) (e₂ : g₂ ≫ f₂ = f₁ ≫ h₂)
  (e : (g₁ ≫ g₂) ≫ f₂ = f₀ ≫ (h₁ ≫ h₂))

/-- The actual comparison diagram, before proving any of its coherence equations. -/
def horizontalDiagram : ExchangeCoherenceDiagram (A S₀ ⥤ A X₂) where
  A := D.left ((g₁ ≫ g₂) ≫ f₂)
  B := D.left (g₁ ≫ g₂) ⋙ D.left f₂
  C₀ := D.left g₁ ⋙ D.left g₂ ⋙ D.left f₂
  D := D.left g₁ ⋙ D.left (g₂ ≫ f₂)
  E := D.left g₁ ⋙ D.left (f₁ ≫ h₂)
  F := D.left g₁ ⋙ D.left f₁ ⋙ D.left h₂
  G := D.left (g₁ ≫ f₁) ⋙ D.left h₂
  H := D.left (f₀ ≫ h₁) ⋙ D.left h₂
  I := D.left f₀ ⋙ D.left h₁ ⋙ D.left h₂
  J := D.left (g₁ ≫ (g₂ ≫ f₂))
  K := D.left (g₁ ≫ (f₁ ≫ h₂))
  L := D.left ((g₁ ≫ f₁) ≫ h₂)
  M := D.left ((f₀ ≫ h₁) ≫ h₂)
  N := D.left (f₀ ≫ (h₁ ≫ h₂))
  O := D.left f₀ ⋙ D.left (h₁ ≫ h₂)
  p := (D.leftCompIso (g₁ ≫ g₂) f₂).hom
  q := Functor.whiskerRight (D.leftCompIso g₁ g₂).hom (D.left f₂) ≫
    (Functor.associator (D.left g₁) (D.left g₂) (D.left f₂)).hom
  b₀ := Functor.whiskerLeft (D.left g₁) (D.leftCompIso g₂ f₂).inv
  t₂ := Functor.whiskerLeft (D.left g₁) (eqToIso (congrArg D.left e₂)).hom
  c₀ := Functor.whiskerLeft (D.left g₁) (D.leftCompIso f₁ h₂).hom
  d := Functor.isoWhiskerRight (D.leftCompIso g₁ f₁) (D.left h₂) ≪≫
    Functor.associator (D.left g₁) (D.left f₁) (D.left h₂)
  t₁ := Functor.whiskerRight (eqToIso (congrArg D.left e₁)).hom (D.left h₂)
  e₀ := Functor.whiskerRight (D.leftCompIso f₀ h₁).hom (D.left h₂) ≫
    (Functor.associator (D.left f₀) (D.left h₁) (D.left h₂)).hom
  a := (eqToIso (congrArg D.left (Category.assoc g₁ g₂ f₂).symm)).inv
  m := (D.leftCompIso g₁ (g₂ ≫ f₂)).hom
  b := (eqToIso (congrArg D.left (congrArg (fun k => g₁ ≫ k) e₂))).hom
  n := (D.leftCompIso g₁ (f₁ ≫ h₂)).hom
  c := (eqToIso (congrArg D.left (Category.assoc g₁ f₁ h₂).symm)).hom
  r := (D.leftCompIso (g₁ ≫ f₁) h₂).hom
  e := (eqToIso (congrArg D.left (congrArg (fun k => k ≫ h₂) e₁))).hom
  s := (D.leftCompIso (f₀ ≫ h₁) h₂).hom
  z := (eqToIso (congrArg D.left (Category.assoc f₀ h₁ h₂).symm)).inv
  u := (D.leftCompIso f₀ (h₁ ≫ h₂)).hom
  v := Functor.whiskerLeft (D.left f₀) (D.leftCompIso h₁ h₂).hom
  τ := (eqToIso (congrArg D.left e)).hom

include hD in
theorem horizontalDiagram_start :
    (D.horizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).StartEquation :=
  D.leftCompIso_assoc_start_whole hD g₁ g₂ f₂

theorem horizontalDiagram_firstTransport :
    (D.horizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).FirstTransportEquation :=
  D.leftCompIso_eqToHom_right_whole g₁ e₂

include hD in
theorem horizontalDiagram_middle :
    (D.horizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).MiddleEquation :=
  D.leftCompIso_assoc_whole hD g₁ f₁ h₂

theorem horizontalDiagram_secondTransport :
    (D.horizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).SecondTransportEquation :=
  D.leftCompIso_eqToHom_left_whole e₁ h₂

include hD in
theorem horizontalDiagram_finish :
    (D.horizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).FinishEquation :=
  D.leftCompIso_assoc_finish_whole hD f₀ h₁ h₂

theorem horizontalDiagram_transport :
    (D.horizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).TransportEquation :=
  exchangeCoherence_whole_transport (fun k => D.left k)
    (Category.assoc g₁ g₂ f₂).symm (congrArg (fun k => g₁ ≫ k) e₂)
    (Category.assoc g₁ f₁ h₂).symm (congrArg (fun k => k ≫ h₂) e₁)
    (Category.assoc f₀ h₁ h₂).symm e

include hD in
theorem horizontalDiagram_chain :
    (D.horizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).ChainEquation :=
  ExchangeCoherenceDiagram.chain _
    (D.horizontalDiagram_start hD f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)
    (D.horizontalDiagram_firstTransport f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)
    (D.horizontalDiagram_middle hD f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)
    (D.horizontalDiagram_secondTransport f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)
    (D.horizontalDiagram_finish hD f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)
    (D.horizontalDiagram_transport f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)

include hD in
/-- Horizontal square pasting is proved before evaluating any coefficient. -/
theorem squareIso_hComp_whole :
    WholeHorizontalSquareEquation (D.squareIso f₀ f₁ g₁ h₁ e₁).hom
      (D.squareIso f₁ f₂ g₂ h₂ e₂).hom
      (D.squareIso f₀ f₂ (g₁ ≫ g₂) (h₁ ≫ h₂) e).hom
      (D.leftCompIso g₁ g₂).hom (D.leftCompIso h₁ h₂).hom :=
  exchangeCoherence_normalize_whole
    (D.leftCompIso g₁ g₂) (D.leftCompIso h₁ h₂)
    (D.leftCompIso (g₁ ≫ g₂) f₂) (D.leftCompIso g₂ f₂)
    (eqToIso (congrArg D.left e₂)) (D.leftCompIso f₁ h₂)
    (D.leftCompIso g₁ f₁) (eqToIso (congrArg D.left e₁)) (D.leftCompIso f₀ h₁)
    (eqToIso (congrArg D.left e)) (D.leftCompIso f₀ (h₁ ≫ h₂))
    (D.squareIso f₀ f₁ g₁ h₁ e₁) (D.squareIso f₁ f₂ g₂ h₂ e₂)
    (D.squareIso f₀ f₂ (g₁ ≫ g₂) (h₁ ≫ h₂) e) rfl rfl rfl
    (D.horizontalDiagram_chain hD f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)

include hD in
/-- The whole equation for the actual supplied comparisons is derived from
coherence and their original comparison identities, before evaluating objects. -/
theorem squareIso_hComp_whole_of_eq
    (γ : D.left (g₁ ≫ g₂) ≅ D.left g₁ ⋙ D.left g₂)
    (θ : D.left (h₁ ≫ h₂) ≅ D.left h₁ ⋙ D.left h₂)
    (s₁ : D.left g₁ ⋙ D.left f₁ ≅ D.left f₀ ⋙ D.left h₁)
    (s₂ : D.left g₂ ⋙ D.left f₂ ≅ D.left f₁ ⋙ D.left h₂)
    (s : D.left (g₁ ≫ g₂) ⋙ D.left f₂ ≅ D.left f₀ ⋙ D.left (h₁ ≫ h₂))
    (hγ : γ = D.leftCompIso g₁ g₂) (hθ : θ = D.leftCompIso h₁ h₂)
    (hs₁ : s₁ = D.squareIso f₀ f₁ g₁ h₁ e₁)
    (hs₂ : s₂ = D.squareIso f₁ f₂ g₂ h₂ e₂)
    (hs : s = D.squareIso f₀ f₂ (g₁ ≫ g₂) (h₁ ≫ h₂) e) :
    WholeHorizontalSquareEquation s₁.hom s₂.hom s.hom γ.hom θ.hom := by
  cases hγ
  cases hθ
  cases hs₁
  cases hs₂
  cases hs
  exact D.squareIso_hComp_whole hD f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e

include hD in
theorem squareIso_hComp (F : A S₀) :
    HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _ (D.squareIso f₀ f₁ g₁ h₁ e₁).hom)
      (TwoSquare.mk _ _ _ _ (D.squareIso f₁ f₂ g₂ h₂ e₂).hom)
      (TwoSquare.mk _ _ _ _ (D.squareIso f₀ f₂ (g₁ ≫ g₂) (h₁ ≫ h₂) e).hom)
      (D.leftCompIso g₁ g₂).hom (D.leftCompIso h₁ h₂).hom F :=
  wholeHorizontalSquare_app _ _ _ _ _
    (D.squareIso_hComp_whole hD f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) F

include hD in
/-- Inverse pasting of the actual whole square comparisons. -/
theorem squareIso_inv_hComp (F : A S₀) :
    (D.leftCompIso h₁ h₂).hom.app ((D.left f₀).obj F) ≫
        (D.left h₂).map ((D.squareIso f₀ f₁ g₁ h₁ e₁).inv.app F) ≫
        (D.squareIso f₁ f₂ g₂ h₂ e₂).inv.app ((D.left g₁).obj F) =
      (D.squareIso f₀ f₂ (g₁ ≫ g₂) (h₁ ≫ h₂) e).inv.app F ≫
        (D.left f₂).map ((D.leftCompIso g₁ g₂).hom.app F) := by
  let a := (D.left h₂).mapIso ((D.squareIso f₀ f₁ g₁ h₁ e₁).app F)
  let b := (D.squareIso f₁ f₂ g₂ h₂ e₂).app ((D.left g₁).obj F)
  let c := (D.squareIso f₀ f₂ (g₁ ≫ g₂) (h₁ ≫ h₂) e).app F
  exact inverse_pasting a b c _ _ (D.squareIso_hComp hD f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e F)

include hD in
/-- Actual coefficient-square maps compose through the original comparisons. -/
theorem squareCoefficientMap_hComp {F : A S₀} {G : A S₁} {H : A S₂}
    (φ : (D.left g₁).obj F ⟶ G) (ψ : (D.left g₂).obj G ⟶ H) :
    (D.leftCompIso h₁ h₂).hom.app ((D.left f₀).obj F) ≫
        (D.left h₂).map (D.squareCoefficientMap f₀ f₁ g₁ h₁ e₁ φ) ≫
        D.squareCoefficientMap f₁ f₂ g₂ h₂ e₂ ψ =
      D.squareCoefficientMap f₀ f₂ (g₁ ≫ g₂) (h₁ ≫ h₂) e
        ((D.leftCompIso g₁ g₂).hom.app F ≫ (D.left g₂).map φ ≫ ψ) := by
  have hn := (D.squareIso f₁ f₂ g₂ h₂ e₂).inv.naturality φ
  simp only [Functor.comp_map] at hn
  have hp := D.squareIso_inv_hComp hD f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e F
  dsimp only [squareCoefficientMap, Adjunction.CoefficientSquares.coefficientMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((D.left h₂).map ((D.left f₁).map φ)), hn]
  have ht := congrArg
    (fun k => k ≫ (D.left f₂).map ((D.left g₂).map φ) ≫ (D.left f₂).map ψ) hp
  simpa only [Category.assoc] using ht

end Horizontal

include hD in
/-- Vertical pasting is proved as a whole natural-transformation equation. -/
theorem squareIso_vComp_whole {S X Y S' X' Y' : J}
    (f : S ⟶ X) (k : X ⟶ Y) (f' : S' ⟶ X') (k' : X' ⟶ Y')
    (g : S ⟶ S') (g' : X ⟶ X') (g'' : Y ⟶ Y')
    (ef : g ≫ f' = f ≫ g') (ek : g' ≫ k' = k ≫ g'')
    (e : g ≫ (f' ≫ k') = (f ≫ k) ≫ g'') :
    Functor.whiskerLeft (D.left g) (D.leftCompIso f' k').hom ≫
        (Functor.associator (D.left g) (D.left f') (D.left k')).inv ≫
        Functor.whiskerRight (D.squareIso f f' g g' ef).hom (D.left k') ≫
        (Functor.associator (D.left f) (D.left g') (D.left k')).hom ≫
        Functor.whiskerLeft (D.left f) (D.squareIso k k' g' g'' ek).hom ≫
        (Functor.associator (D.left f) (D.left k) (D.left g'')).inv =
      (D.squareIso (f ≫ k) (f' ≫ k') g g'' e).hom ≫
        Functor.whiskerRight (D.leftCompIso f k).hom (D.left g'') := by
  have hp := D.squareIso_hComp_whole hD g g' g'' f k f' k' ef.symm ek.symm e.symm
  dsimp only [WholeHorizontalSquareEquation] at hp
  rw [D.squareIso_transpose f f' g g' ef, D.squareIso_transpose k k' g' g'' ek,
    D.squareIso_transpose (f ≫ k) (f' ≫ k') g g'' e] at hp
  let a : (D.left f ⋙ D.left g') ⋙ D.left k' ≅
      D.left g ⋙ D.left f' ⋙ D.left k' :=
    Functor.isoWhiskerRight (D.squareIso f f' g g' ef).symm (D.left k') ≪≫
      Functor.associator (D.left g) (D.left f') (D.left k')
  let b : (D.left f ⋙ D.left k) ⋙ D.left g'' ≅
      (D.left f ⋙ D.left g') ⋙ D.left k' :=
    Functor.associator (D.left f) (D.left k) (D.left g'') ≪≫
      Functor.isoWhiskerLeft (D.left f) (D.squareIso k k' g' g'' ek).symm ≪≫
        (Functor.associator (D.left f) (D.left g') (D.left k')).symm
  let c := (D.squareIso (f ≫ k) (f' ≫ k') g g'' e).symm
  have hh : Functor.whiskerRight (D.leftCompIso f k).hom (D.left g'') ≫ b.hom ≫ a.hom =
      c.hom ≫ Functor.whiskerLeft (D.left g) (D.leftCompIso f' k').hom := by
    simpa only [a, b, c, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Category.assoc] using hp
  have hi := inverse_pasting a b c _ _ hh
  simpa only [a, b, c, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc] using hi

include hD in
/-- Evaluate only the already proved whole vertical pasting equation. -/
theorem squareIso_vComp {S X Y S' X' Y' : J}
    (f : S ⟶ X) (k : X ⟶ Y) (f' : S' ⟶ X') (k' : X' ⟶ Y')
    (g : S ⟶ S') (g' : X ⟶ X') (g'' : Y ⟶ Y')
    (ef : g ≫ f' = f ≫ g') (ek : g' ≫ k' = k ≫ g'')
    (e : g ≫ (f' ≫ k') = (f ≫ k) ≫ g'') (F : A S) :
    (D.leftCompIso f' k').hom.app ((D.left g).obj F) ≫
        (D.left k').map ((D.squareIso f f' g g' ef).hom.app F) ≫
        (D.squareIso k k' g' g'' ek).hom.app ((D.left f).obj F) =
      (D.squareIso (f ≫ k) (f' ≫ k') g g'' e).hom.app F ≫
        (D.left g'').map ((D.leftCompIso f k).hom.app F) := by
  have h := congrArg (fun η => η.app F)
    (D.squareIso_vComp_whole hD f k f' k' g g' g'' ef ek e)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using h

include hD in
/-- Coherence proves the whole original triangle-square equation before coefficients. -/
theorem triangleSquare_whole {X₀ X₁ Y₀ Y₁ Z W : J}
    (f : X₀ ⟶ X₁) (h : Y₀ ⟶ Y₁) (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁)
    (l : Z ⟶ W) (p₀ : X₀ ⟶ Z) (p₁ : X₁ ⟶ Z) (q₀ : Y₀ ⟶ W) (q₁ : Y₁ ⟶ W)
    (he : f ≫ v₁ = v₀ ≫ h) (hp : f ≫ p₁ = p₀) (hq : h ≫ q₁ = q₀)
    (hi : v₀ ≫ q₀ = p₀ ≫ l) (hj : v₁ ≫ q₁ = p₁ ≫ l) :
    Adjunction.CoefficientSquares.WholeTriangleSquareEquation
      (D.triangleIso p₀ f p₁ hp) (D.triangleIso q₀ h q₁ hq)
      (D.squareIso v₀ v₁ f h he) (D.squareIso p₀ q₀ v₀ l hi)
      (D.squareIso p₁ q₁ v₁ l hj) := by
  cases hp
  cases hq
  have hs := D.squareIso_vComp_whole hD f p₁ h q₁ v₀ v₁ l he.symm hj hi
  rw [D.squareIso_transpose v₀ v₁ f h he, Iso.symm_hom] at hs
  have ht := congrArg
    (fun z => z ≫ (Functor.associator (D.left f) (D.left p₁) (D.left l)).hom) hs
  simpa only [Adjunction.CoefficientSquares.WholeTriangleSquareEquation, triangleIso,
    Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] using ht

include hD in
/-- Actual supplied comparisons inherit that whole equation from their original identities. -/
theorem triangleSquare_whole_of_eq {X₀ X₁ Y₀ Y₁ Z W : J}
    (f : X₀ ⟶ X₁) (h : Y₀ ⟶ Y₁) (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁)
    (l : Z ⟶ W) (p₀ : X₀ ⟶ Z) (p₁ : X₁ ⟶ Z) (q₀ : Y₀ ⟶ W) (q₁ : Y₁ ⟶ W)
    (he : f ≫ v₁ = v₀ ≫ h) (hp : f ≫ p₁ = p₀) (hq : h ≫ q₁ = q₀)
    (hi : v₀ ≫ q₀ = p₀ ≫ l) (hj : v₁ ≫ q₁ = p₁ ≫ l)
    (t_f : D.left p₀ ≅ D.left f ⋙ D.left p₁)
    (t_h : D.left q₀ ≅ D.left h ⋙ D.left q₁)
    (s : D.left f ⋙ D.left v₁ ≅ D.left v₀ ⋙ D.left h)
    (s₀ : D.left v₀ ⋙ D.left q₀ ≅ D.left p₀ ⋙ D.left l)
    (s₁ : D.left v₁ ⋙ D.left q₁ ≅ D.left p₁ ⋙ D.left l)
    (ht_f : t_f = D.triangleIso p₀ f p₁ hp)
    (ht_h : t_h = D.triangleIso q₀ h q₁ hq)
    (hs : s = D.squareIso v₀ v₁ f h he)
    (hs₀ : s₀ = D.squareIso p₀ q₀ v₀ l hi)
    (hs₁ : s₁ = D.squareIso p₁ q₁ v₁ l hj) :
    Adjunction.CoefficientSquares.WholeTriangleSquareEquation t_f t_h s s₀ s₁ := by
  cases ht_f
  cases ht_h
  cases hs
  cases hs₀
  cases hs₁
  exact D.triangleSquare_whole hD f h v₀ v₁ l p₀ p₁ q₀ q₁ he hp hq hi hj

include hD in
/-- Actual coefficient squares commute with the original cone triangles. -/
theorem triangleCoefficientMap_square {X₀ X₁ Y₀ Y₁ Z W : J}
    (f : X₀ ⟶ X₁) (h : Y₀ ⟶ Y₁) (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁)
    (l : Z ⟶ W) (p₀ : X₀ ⟶ Z) (p₁ : X₁ ⟶ Z) (q₀ : Y₀ ⟶ W) (q₁ : Y₁ ⟶ W)
    (he : f ≫ v₁ = v₀ ≫ h) (hp : f ≫ p₁ = p₀) (hq : h ≫ q₁ = q₀)
    (hi : v₀ ≫ q₀ = p₀ ≫ l) (hj : v₁ ≫ q₁ = p₁ ≫ l)
    {F : A X₀} {G : A X₁} (φ : (D.left f).obj F ⟶ G) :
    D.triangleCoefficientMap h q₀ q₁ hq (D.squareCoefficientMap v₀ v₁ f h he φ) ≫
        (D.squareIso p₁ q₁ v₁ l hj).hom.app G =
      (D.squareIso p₀ q₀ v₀ l hi).hom.app F ≫
        (D.left l).map (D.triangleCoefficientMap f p₀ p₁ hp φ) := by
  cases hp
  cases hq
  have hs := D.squareIso_vComp hD f p₁ h q₁ v₀ v₁ l he.symm hj hi F
  rw [D.squareIso_transpose v₀ v₁ f h he, Iso.symm_hom] at hs
  have hn := (D.squareIso p₁ q₁ v₁ l hj).hom.naturality φ
  have ht := congrArg (fun z => z ≫ (D.left l).map ((D.left p₁).map φ)) hs
  dsimp only [triangleCoefficientMap, squareCoefficientMap,
    Adjunction.CoefficientSquares.coefficientMap, triangleIso,
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp,
    Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map] at hn
  rw [hn]
  simpa only [Category.assoc] using ht

end CategoryTheory.InjectiveSystem.AdjunctionData

namespace CategoryTheory.Adjunction.CoefficientSquares

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {A : Type u₀} [Category.{v₀} A] {B : Type u₁} [Category.{v₁} B]
  {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]
  {E : Type u₄} [Category.{v₄} E]
  {L_g : A ⥤ B} {R_g : B ⥤ A} {L_v₀ : A ⥤ C} {R_v₀ : C ⥤ A}
  {L_v₁ : B ⥤ D} {R_v₁ : D ⥤ B} {L_h : C ⥤ D} {R_h : D ⥤ C}

/-- The arbitrary-second-leg value formula, with four independent category/Hom worlds. -/
theorem homEquiv (a_g : L_g ⊣ R_g) (a_v₀ : L_v₀ ⊣ R_v₀)
    (a_v₁ : L_v₁ ⊣ R_v₁) (a_h : L_h ⊣ R_h)
    (s : L_g ⋙ L_v₁ ≅ L_v₀ ⋙ L_h) (r : R_h ⋙ R_v₀ ≅ R_v₁ ⋙ R_g)
    (hs : conjugateEquiv (a_g.comp a_v₁) (a_v₀.comp a_h) s.inv = r.inv)
    {F : A} {G : B} {K : D} (φ : L_g.obj F ⟶ G) (ψ : L_v₁.obj G ⟶ K) :
    (a_v₀.comp a_h).homEquiv _ _ (coefficientMap s φ ≫ ψ) =
      a_g.homEquiv _ _ φ ≫ R_g.map (a_v₁.homEquiv _ _ ψ) ≫ r.inv.app K := by
  simpa only [coefficientMap, Category.assoc] using
    Adjunction.RepresentedCoherence.homEquiv_comp a_g a_v₁ (a_v₀.comp a_h)
      s.inv r.inv hs F G K φ ψ

variable {L_q₀ : C ⥤ E} {R_q₀ : E ⥤ C} {L_q₁ : D ⥤ E} {R_q₁ : E ⥤ D}

/-- Paste the actual square and triangle adjunct formulas, retaining the nested native value. -/
theorem triangle_homEquiv (a_g : L_g ⊣ R_g) (a_v₀ : L_v₀ ⊣ R_v₀)
    (a_v₁ : L_v₁ ⊣ R_v₁) (a_h : L_h ⊣ R_h)
    (a_q₀ : L_q₀ ⊣ R_q₀) (a_q₁ : L_q₁ ⊣ R_q₁)
    (s : L_g ⋙ L_v₁ ≅ L_v₀ ⋙ L_h) (r : R_h ⋙ R_v₀ ≅ R_v₁ ⋙ R_g)
    (hs : conjugateEquiv (a_g.comp a_v₁) (a_v₀.comp a_h) s.inv = r.inv)
    (t : L_q₀ ≅ L_h ⋙ L_q₁) (d : R_q₁ ⋙ R_h ≅ R_q₀)
    (ht : conjugateEquiv (a_h.comp a_q₁) a_q₀ t.hom = d.hom)
    {F : A} {G : B} {K : E}
    (φ : L_g.obj F ⟶ G) (ψ : L_q₁.obj (L_v₁.obj G) ⟶ K) :
    a_v₀.homEquiv _ _ (a_q₀.homEquiv _ _
      (t.hom.app (L_v₀.obj F) ≫ L_q₁.map (coefficientMap s φ) ≫ ψ)) =
      a_g.homEquiv _ _ φ ≫
        R_g.map (a_v₁.homEquiv _ _ (a_q₁.homEquiv _ _ ψ)) ≫
          r.inv.app (R_q₁.obj K) ≫ R_v₀.map (d.hom.app K) := by
  let ζ := a_q₁.homEquiv _ _ ψ
  let σ := coefficientMap s φ
  have hc := homEquiv a_g a_v₀ a_v₁ a_h s r hs φ ζ
  rw [Adjunction.comp_homEquiv] at hc
  change a_v₀.homEquiv _ _ (a_h.homEquiv _ _ (σ ≫ ζ)) = _ at hc
  rw [Adjunction.homEquiv_naturality_right] at hc
  have hh := Adjunction.RepresentedCoherence.homEquiv_comp a_h a_q₁ a_q₀
    t.hom d.hom ht (L_v₀.obj F) (L_v₁.obj G) K σ ψ
  have hh' := hh.trans (Category.assoc _ _ _).symm
  have hv := congrArg (a_v₀.homEquiv F (R_q₀.obj K)) hh'
  have hn := a_v₀.homEquiv_naturality_right
    (a_h.homEquiv _ _ σ ≫ R_h.map ζ) (d.hom.app K)
  have he := congrArg
    (fun z : F ⟶ R_v₀.obj (R_h.obj (R_q₁.obj K)) => z ≫ R_v₀.map (d.hom.app K)) hc
  simpa only [Category.assoc] using hv.trans (hn.trans he)

section ActualHorizontal

universe uS₀ vS₀ uS₁ vS₁ uS₂ vS₂ uX₀ vX₀ uX₁ vX₁ uX₂ vX₂

variable {S₀ : Type uS₀} [Category.{vS₀} S₀] {S₁ : Type uS₁} [Category.{vS₁} S₁]
  {S₂ : Type uS₂} [Category.{vS₂} S₂] {X₀ : Type uX₀} [Category.{vX₀} X₀]
  {X₁ : Type uX₁} [Category.{vX₁} X₁] {X₂ : Type uX₂} [Category.{vX₂} X₂]
  {G₁ : S₀ ⥤ S₁} {G₂ : S₁ ⥤ S₂} {L₀ : S₀ ⥤ X₀} {L₁ : S₁ ⥤ X₁}
  {L₂ : S₂ ⥤ X₂} {H₁ : X₀ ⥤ X₁} {H₂ : X₁ ⥤ X₂} {G : S₀ ⥤ S₂} {H : X₀ ⥤ X₂}
  (γ : G ≅ G₁ ⋙ G₂) (θ : H ≅ H₁ ⋙ H₂)
  (s₁ : G₁ ⋙ L₁ ≅ L₀ ⋙ H₁) (s₂ : G₂ ⋙ L₂ ≅ L₁ ⋙ H₂) (s : G ⋙ L₂ ≅ L₀ ⋙ H)
  (h : WholeHorizontalSquareEquation s₁.hom s₂.hom s.hom γ.hom θ.hom)

include h in
/-- Invert the proved whole equation at the actual comparisons, retaining all
six independent category/Hom worlds and literal component maps. -/
theorem inverse_hComp (F : S₀) :
    θ.hom.app (L₀.obj F) ≫ H₂.map (s₁.inv.app F) ≫ s₂.inv.app (G₁.obj F) =
      s.inv.app F ≫ L₂.map (γ.hom.app F) := by
  let a := H₂.mapIso (s₁.app F)
  let b := s₂.app (G₁.obj F)
  let c := s.app F
  exact InjectiveSystem.AdjunctionData.inverse_pasting a b c _ _
    (wholeHorizontalSquare_app _ _ _ _ _ h F)

include h in
/-- Actual coefficient-map composition follows from the actual whole square,
without a post-evaluation canonical-comparison conversion. -/
theorem coefficient_hComp {F : S₀} {F' : S₁} {F'' : S₂}
    (φ : G₁.obj F ⟶ F') (ψ : G₂.obj F' ⟶ F'') :
    θ.hom.app (L₀.obj F) ≫ H₂.map (coefficientMap s₁ φ) ≫ coefficientMap s₂ ψ =
      coefficientMap s (γ.hom.app F ≫ G₂.map φ ≫ ψ) := by
  have hn := s₂.inv.naturality φ
  simp only [Functor.comp_map] at hn
  have hp := inverse_hComp γ θ s₁ s₂ s h F
  dsimp only [coefficientMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (H₂.map (L₁.map φ)), hn]
  have ht := congrArg (fun k => k ≫ L₂.map (G₂.map φ) ≫ L₂.map ψ) hp
  simpa only [Category.assoc] using ht

end ActualHorizontal

section ActualUnits

universe uT vT

variable {T : Type uT} [Category.{vT} T]

/-- Evaluate the proved base-unit equation using the actual supplied comparisons. -/
theorem coefficient_base_id {I : A ⥤ A} {F : A ⥤ B} {P : A ⥤ T} {H : B ⥤ T}
    (e : I ≅ 𝟭 A) (s : I ⋙ P ≅ F ⋙ H) (t : P ≅ F ⋙ H)
    (h : s.symm ≪≫ Functor.isoWhiskerRight e P ≪≫ Functor.leftUnitor P = t.symm)
    (X : A) : coefficientMap s (e.hom.app X) = t.inv.app X := by
  have hc := congrArg (fun z => z.hom.app X) h
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app] at hc
  let m : P.obj (I.obj X) ⟶ P.obj X := P.map (e.hom.app X)
  change s.inv.app X ≫ m ≫ 𝟙 _ = _ at hc
  exact (congrArg (fun k => s.inv.app X ≫ k) (Category.comp_id m)).symm.trans hc

/-- Evaluate the proved top-unit equation with an arbitrary actual coefficient morphism. -/
theorem coefficient_top_id {I : B ⥤ B} {F : A ⥤ B} {P : T ⥤ B} {G : A ⥤ T}
    (e : I ≅ 𝟭 B) (s : G ⋙ P ≅ F ⋙ I) (t : F ≅ G ⋙ P)
    (h : (Functor.rightUnitor F).symm ≪≫
      Functor.isoWhiskerLeft F e.symm ≪≫ s.symm = t)
    {X : A} {Y : T} (φ : G.obj X ⟶ Y) :
    e.inv.app (F.obj X) ≫ coefficientMap s φ = t.hom.app X ≫ P.map φ := by
  have hc := congrArg (fun z => z.hom.app X) h
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app] at hc
  let m : F.obj X ⟶ P.obj (G.obj X) := e.inv.app (F.obj X) ≫ s.inv.app X
  change 𝟙 _ ≫ m = _ at hc
  have hc' := (Category.id_comp m).symm.trans hc
  have ht := congrArg (fun k => k ≫ P.map φ) hc'
  simpa only [coefficientMap, Category.assoc, m] using ht

end ActualUnits

section ActualTriangleSquare

universe uT₀ vT₀ uT₁ vT₁

variable {T₀ : Type uT₀} [Category.{vT₀} T₀]
  {T₁ : Type uT₁} [Category.{vT₁} T₁]
  {L : T₀ ⥤ T₁} {P₀ : A ⥤ T₀} {P₁ : B ⥤ T₀}
  {Q₀ : C ⥤ T₁} {Q₁ : D ⥤ T₁}

/-- The actual whole triangle-square identity gives its arbitrary coefficient-map value. -/
theorem triangle_square
    (t_g : P₀ ≅ L_g ⋙ P₁) (t_h : Q₀ ≅ L_h ⋙ Q₁)
    (s : L_g ⋙ L_v₁ ≅ L_v₀ ⋙ L_h)
    (s₀ : L_v₀ ⋙ Q₀ ≅ P₀ ⋙ L) (s₁ : L_v₁ ⋙ Q₁ ≅ P₁ ⋙ L)
    (h : WholeTriangleSquareEquation t_g t_h s s₀ s₁)
    {X : A} {Y : B} (φ : L_g.obj X ⟶ Y) :
    (t_h.hom.app (L_v₀.obj X) ≫ Q₁.map (coefficientMap s φ)) ≫ s₁.hom.app Y =
      s₀.hom.app X ≫ L.map (t_g.hom.app X ≫ P₁.map φ) := by
  have hc : t_h.hom.app (L_v₀.obj X) ≫ Q₁.map (s.inv.app X) ≫
      s₁.hom.app (L_g.obj X) = s₀.hom.app X ≫ L.map (t_g.hom.app X) := by
    have ht := congrArg (fun η => η.app X) h
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp, Category.comp_id] using ht
  have hn := s₁.hom.naturality φ
  simp only [Functor.comp_map] at hn
  dsimp only [coefficientMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  have ht := congrArg (fun k => k ≫ L.map (P₁.map φ)) hc
  simpa only [Category.assoc] using ht

end ActualTriangleSquare

end CategoryTheory.Adjunction.CoefficientSquares
