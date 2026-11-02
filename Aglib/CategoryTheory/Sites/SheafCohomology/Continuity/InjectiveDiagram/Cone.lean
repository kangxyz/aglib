/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.RepresentedCoherence
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.InverseTransitions
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.InverseNaturality
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.Reindex
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.RightTail

/-! # Actual coefficient diagrams and adjunct families at a cone point

An actual cone of adjunctions transports an ordinary coefficient system to its
apex category. Its structural comparison laws imply the functor laws and the
cocone equation after transposition. The apex, stage and index universes are
independent. No colimit comparison or continuity assertion is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe u₀ v₀ u₁ v₁ u₂ v₂

/-- Naturality of coefficient transport through the supplied original triangle. -/
theorem triangleCoefficientMap_naturality
    {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂]
    {L : C₀ ⥤ C₁} {P : C₀ ⥤ C₂} {Q : C₁ ⥤ C₂} (t : P ≅ L ⋙ Q)
    {F F' : C₀} {G G' : C₁}
    (φ : L.obj F ⟶ G) (ψ : L.obj F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (h : L.map a ≫ ψ = φ ≫ b) :
    (t.hom.app F ≫ Q.map φ) ≫ Q.map b =
      P.map a ≫ (t.hom.app F' ≫ Q.map ψ) := by
  have hn := t.hom.naturality a
  change P.map a ≫ t.hom.app F' = t.hom.app F ≫ Q.map (L.map a) at hn
  rw [Category.assoc, ← Q.map_comp, ← h, Q.map_comp,
    ← Category.assoc, ← hn, Category.assoc]

end CategoryTheory.Adjunction

namespace CategoryTheory.InjectiveSystem

universe uI vI uA vA uB vB

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)]
  (D : AdjunctionData A) (B : Type uB) [Category.{vB} B]

/-- Actual apex adjunctions and their original conjugate triangle comparisons.
The two laws concern the right-adjoint comparisons themselves, before choosing
any coefficient system or any cocone of coefficient maps. -/
structure AdjunctionData.Cone where
  /-- The functors from each stage category to the apex category. -/
  left : ∀ i, A i ⥤ B
  /-- The functors from the apex category to each stage category. -/
  right : ∀ i, B ⥤ A i
  /-- The adjunction between the left and right functors at each stage. -/
  adj : ∀ i, left i ⊣ right i
  /-- The comparison of an apex left functor with transport along a stage transition. -/
  leftTriangle : ∀ {i j : I} (a : i ⟶ j), left i ≅ D.left a ⋙ left j
  /-- The comparison of an apex right functor followed by a stage right transition
  with the earlier apex right functor. -/
  rightTriangle : ∀ {i j : I} (a : i ⟶ j), right j ⋙ D.right a ≅ right i
  conjugate : ∀ {i j : I} (a : i ⟶ j),
    conjugateEquiv ((D.adj a).comp (adj j)) (adj i) (leftTriangle a).hom =
      (rightTriangle a).hom
  right_id : ∀ (i : I) (K : B),
    (rightTriangle (𝟙 i)).hom.app K = (D.idIso i).hom.app ((right i).obj K)
  right_comp : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (K : B),
    (D.right a).map ((rightTriangle b).hom.app K) ≫ (rightTriangle a).hom.app K =
      (D.compIso a b).inv.app ((right k).obj K) ≫
        (rightTriangle (a ≫ b)).hom.app K

namespace AdjunctionData.Cone

variable {D B} (P : D.Cone B) (F : System D)

/-- The original right-comparison composition, before evaluating an apex object. -/
theorem right_comp_whole {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    Functor.whiskerRight (P.rightTriangle b).hom (D.right a) ≫
        (P.rightTriangle a).hom =
      (Functor.associator (P.right k) (D.right b) (D.right a)).hom ≫
        Functor.whiskerLeft (P.right k) (D.compIso a b).inv ≫
          (P.rightTriangle (a ≫ b)).hom := by
  apply NatTrans.ext
  funext K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp] using P.right_comp a b K

/-- The original coefficient at a stage, transported by its apex left adjoint. -/
abbrev coefficientObj (i : I) : B := (P.left i).obj (F.obj i)

/-- Transport the actual left transition through the original apex triangle. -/
def coefficientMap {i j : I} (a : i ⟶ j) :
    P.coefficientObj F i ⟶ P.coefficientObj F j :=
  (P.leftTriangle a).hom.app (F.obj i) ≫ (P.left j).map (F.leftMap D a)

/-- The actual three-adjunction calculation for an arbitrary second leg. -/
theorem coefficientMap_homEquiv {i j : I} (a : i ⟶ j) {K : B}
    (ψ : P.coefficientObj F j ⟶ K) :
    (P.adj i).homEquiv _ _ (P.coefficientMap F a ≫ ψ) =
      F.map a ≫ (D.right a).map ((P.adj j).homEquiv _ _ ψ) ≫
        (P.rightTriangle a).hom.app K := by
  simpa only [coefficientMap, Category.assoc, System.homEquiv_leftMap] using
    Adjunction.RepresentedCoherence.homEquiv_comp (D.adj a) (P.adj j) (P.adj i)
      (P.leftTriangle a).hom (P.rightTriangle a).hom (P.conjugate a)
      (F.obj i) (F.obj j) K (F.leftMap D a) ψ

/-- The structural identity comparison and the system identity give identity. -/
theorem coefficientMap_id (i : I) : P.coefficientMap F (𝟙 i) = 𝟙 _ := by
  apply ((P.adj i).homEquiv _ _).injective
  have h := P.coefficientMap_homEquiv F (𝟙 i) (𝟙 (P.coefficientObj F i))
  rw [Category.comp_id, P.right_id, (D.idIso i).hom.naturality,
    ← Category.assoc, F.map_id, Category.id_comp] at h
  exact h

/-- Structural composition, rather than a coefficient cocone law, gives composition. -/
theorem coefficientMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    P.coefficientMap F (a ≫ b) = P.coefficientMap F a ≫ P.coefficientMap F b := by
  apply ((P.adj i).homEquiv _ _).injective
  let η := (P.adj k).homEquiv (F.obj k) (P.coefficientObj F k) (𝟙 _)
  have hab := P.coefficientMap_homEquiv F (a ≫ b) (𝟙 (P.coefficientObj F k))
  have hb := P.coefficientMap_homEquiv F b (𝟙 (P.coefficientObj F k))
  rw [Category.comp_id] at hab hb
  rw [hab, P.coefficientMap_homEquiv F a, hb]
  change F.map (a ≫ b) ≫ (D.right (a ≫ b)).map η ≫
      (P.rightTriangle (a ≫ b)).hom.app _ =
    F.map a ≫ (D.right a).map
      (F.map b ≫ (D.right b).map η ≫ (P.rightTriangle b).hom.app _) ≫
        (P.rightTriangle a).hom.app _
  simp only [Functor.map_comp, Category.assoc]
  rw [P.right_comp]
  rw [← Category.assoc (F.map a), ← F.map_comp, Category.assoc]
  have hn := (D.compIso a b).hom.naturality η
  rw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc]

/-- The actual system produces an ordinary coefficient functor at the cone point. -/
def coefficientFunctor : I ⥤ B where
  obj := P.coefficientObj F
  map := P.coefficientMap F
  map_id := P.coefficientMap_id F
  map_comp := P.coefficientMap_comp F

/-- A system morphism induces the literal apex left-adjoint component maps. -/
def coefficientNatTrans {F G : System D} (η : System.Hom D F G) :
    P.coefficientFunctor F ⟶ P.coefficientFunctor G where
  app i := (P.left i).map (η.app i)
  naturality i j a := Adjunction.triangleCoefficientMap_naturality
    (P.leftTriangle a) (F.leftMap D a) (G.leftMap D a)
    (η.app i) (η.app j) (System.Hom.leftMap_naturality D η a)

/-- The actual map between the colimits of the original coefficient functors. -/
def coefficientColimitMap {F G : System D} (η : System.Hom D F G)
    [HasColimitsOfShape I B] :
    colimit (P.coefficientFunctor F) ⟶ colimit (P.coefficientFunctor G) :=
  colim.map (P.coefficientNatTrans η)

@[reassoc]
theorem coefficientColimitMap_ι {F G : System D} (η : System.Hom D F G)
    [HasColimitsOfShape I B] (i : I) :
    colimit.ι (P.coefficientFunctor F) i ≫ P.coefficientColimitMap η =
      (P.left i).map (η.app i) ≫ colimit.ι (P.coefficientFunctor G) i :=
  colimit.ι_map (P.coefficientNatTrans η) i

/-- Original right-adjoint legs satisfying their actual transition equations. -/
def AdjointFamily (K : B) :=
  {ξ : ∀ i, F.obj i ⟶ (P.right i).obj K //
    ∀ {i j} (a : i ⟶ j), ξ i = F.map a ≫
      (D.right a).map (ξ j) ≫ (P.rightTriangle a).hom.app K}

/-- Native adjuncts re-express actual coefficient cocones in both directions. -/
def coconeAdjointEquiv (K : B) :
    (P.coefficientFunctor F ⟶ (Functor.const I).obj K) ≃ P.AdjointFamily F K where
  toFun α := ⟨fun i => (P.adj i).homEquiv _ _ (α.app i), fun {i j} a => by
    have hn : (P.coefficientFunctor F).map a ≫ α.app j = α.app i :=
      (α.naturality a).trans (Category.comp_id (α.app i))
    exact (congrArg ((P.adj i).homEquiv _ _) hn).symm.trans
      (P.coefficientMap_homEquiv F a (α.app j))⟩
  invFun ξ :=
    { app := fun i => ((P.adj i).homEquiv _ _).symm (ξ.val i)
      naturality := fun {i j} a => by
        change P.coefficientMap F a ≫ ((P.adj j).homEquiv (F.obj j) K).symm (ξ.val j) =
          ((P.adj i).homEquiv (F.obj i) K).symm (ξ.val i) ≫ 𝟙 K
        rw [Category.comp_id]
        apply ((P.adj i).homEquiv (F.obj i) K).injective
        have ht := P.coefficientMap_homEquiv F a
          (((P.adj j).homEquiv (F.obj j) K).symm (ξ.val j))
        have he := congrArg
          (fun z : F.obj j ⟶ (P.right j).obj K =>
            F.map a ≫ (D.right a).map z ≫ (P.rightTriangle a).hom.app K)
          (((P.adj j).homEquiv (F.obj j) K).apply_symm_apply (ξ.val j))
        exact ht.trans (he.trans ((ξ.property a).symm.trans
          (((P.adj i).homEquiv (F.obj i) K).apply_symm_apply (ξ.val i)).symm)) }
  left_inv α := by
    apply NatTrans.ext
    funext i
    exact Equiv.symm_apply_apply _ _
  right_inv ξ := by
    apply Subtype.ext
    funext i
    exact Equiv.apply_symm_apply _ _

variable [HasColimit (P.coefficientFunctor F)]

/-- Transpose the literal injection of the original coefficient colimit. -/
def adjointLeg (i : I) : F.obj i ⟶ (P.right i).obj (colimit (P.coefficientFunctor F)) :=
  (P.adj i).homEquiv _ _ (colimit.ι (P.coefficientFunctor F) i)

/-- The literal colimit injections satisfy the right-adjoint cocone equation. -/
theorem adjointLeg_naturality {i j : I} (a : i ⟶ j) :
    P.adjointLeg F i = F.map a ≫ (D.right a).map (P.adjointLeg F j) ≫
      (P.rightTriangle a).hom.app (colimit (P.coefficientFunctor F)) := by
  have h := congrArg ((P.adj i).homEquiv _ _)
    (colimit.w (P.coefficientFunctor F) a)
  exact h.symm.trans (P.coefficientMap_homEquiv F a
    (colimit.ι (P.coefficientFunctor F) j))

section FromCocone

universe uJ vJ

variable {J : Type uJ} [Category.{vJ} J]
  {E : J → Type uA} [∀ j, Category.{vA} (E j)]
  (S : AdjunctionData E) (hS : S.Coherent) (X : I ⥤ J) (c : Cocone X)

/-- The original right-adjoint composition comparison with its cone equality transport. -/
def coconeRightTriangle {i j : I} (a : i ⟶ j) :
    S.right (c.ι.app j) ⋙ S.right (X.map a) ≅ S.right (c.ι.app i) :=
  (S.compIso (X.map a) (c.ι.app j)).symm ≪≫
    eqToIso (congrArg S.right (c.w a))

include hS in
private theorem rightTriangle_id_transport {i t : J} (e : i ⟶ i) (p : i ⟶ t)
    (he : e = 𝟙 i) (hp : e ≫ p = p) (K : E t) :
    (S.compIso e p).inv.app K ≫
        eqToHom (congrArg (fun a => (S.right a).obj K) hp) =
      eqToHom (congrArg (fun a => (S.right a).obj ((S.right p).obj K)) he) ≫
        (S.idIso i).hom.app ((S.right p).obj K) := by
  cases he
  have h := congrArg (fun f => (S.compIso (𝟙 i) p).inv.app K ≫ f)
    (hS.id_comp p K)
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp,
    eqToHom_refl] using h.symm

include hS in
private theorem rightTriangle_comp_transport {i j k t : J}
    (a : i ⟶ j) (b : j ⟶ k) (d : i ⟶ k) (p : i ⟶ t) (q : j ⟶ t) (r : k ⟶ t)
    (hd : d = a ≫ b) (hp : a ≫ q = p) (hq : b ≫ r = q) (hr : d ≫ r = p)
    (K : E t) :
    (S.right a).map ((S.compIso b r).inv.app K ≫
        eqToHom (congrArg (fun f => (S.right f).obj K) hq)) ≫
      (S.compIso a q).inv.app K ≫
        eqToHom (congrArg (fun f => (S.right f).obj K) hp) =
      (S.compIso a b).inv.app ((S.right r).obj K) ≫
        eqToHom (congrArg (fun f => (S.right f).obj ((S.right r).obj K)) hd.symm) ≫
          (S.compIso d r).inv.app K ≫
            eqToHom (congrArg (fun f => (S.right f).obj K) hr) := by
  cases hd
  cases hq
  cases hp
  change (S.right a).map ((S.compIso b r).inv.app K ≫ 𝟙 _) ≫
      (S.compIso a (b ≫ r)).inv.app K ≫ 𝟙 _ =
    (S.compIso a b).inv.app ((S.right r).obj K) ≫
      𝟙 _ ≫ (S.compIso (a ≫ b) r).inv.app K ≫
        eqToHom (congrArg (fun f => (S.right f).obj K) (Category.assoc a b r))
  simp only [Category.comp_id, Category.id_comp]
  have h := congrArg
    (fun f => f ≫ eqToHom (congrArg (fun g => (S.right g).obj K)
      (Category.assoc a b r)))
    (AdjunctionData.Coherent.inv_assoc S hS a b r K)
  simpa only [eqToHom_refl, Category.comp_id, Functor.map_comp, Functor.map_id,
    Category.assoc, eqToHom_trans] using h.symm

include hS in
/-- The existing right-triangle transport calculation as a whole transformation. -/
theorem rightTriangle_comp_transport_whole {i j k t : J}
    (a : i ⟶ j) (b : j ⟶ k) (d : i ⟶ k) (p : i ⟶ t) (q : j ⟶ t) (r : k ⟶ t)
    (hd : d = a ≫ b) (hp : a ≫ q = p) (hq : b ≫ r = q) (hr : d ≫ r = p) :
    Functor.whiskerRight
        (((S.compIso b r).symm ≪≫ eqToIso (congrArg S.right hq)).hom) (S.right a) ≫
      (((S.compIso a q).symm ≪≫ eqToIso (congrArg S.right hp)).hom) =
      (Functor.associator (S.right r) (S.right b) (S.right a)).hom ≫
        Functor.whiskerLeft (S.right r)
          ((S.compIso a b).inv ≫ eqToHom (congrArg S.right hd.symm)) ≫
            (((S.compIso d r).symm ≪≫ eqToIso (congrArg S.right hr)).hom) := by
  apply NatTrans.ext
  funext K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    eqToHom_app, Category.id_comp, Category.assoc] using
      rightTriangle_comp_transport S hS a b d p q r hd hp hq hr K

include hS in
/-- Restrict one existing coherent adjunction system to a diagram and its actual
apex. Neither the coefficient system nor the image functors are replaced. -/
def ofCocone : (S.reindex X).Cone (E c.pt) where
  left i := S.left (c.ι.app i)
  right i := S.right (c.ι.app i)
  adj i := S.adj (c.ι.app i)
  leftTriangle a := (Adjunction.leftAdjointCompIso (S.adj (X.map a))
    (S.adj (c.ι.app _)) (S.adj (c.ι.app _)) (coconeRightTriangle S X c a)).symm
  rightTriangle := coconeRightTriangle S X c
  conjugate a := Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  right_id i K := by
    simpa only [coconeRightTriangle, AdjunctionData.reindex, Iso.trans_hom,
      NatTrans.comp_app, Iso.symm_hom, eqToIso.hom, eqToHom_app] using
      rightTriangle_id_transport S hS (X.map (𝟙 i)) (c.ι.app i) (X.map_id i) (c.w (𝟙 i)) K
  right_comp a b K := by
    simpa only [coconeRightTriangle, AdjunctionData.reindex, Iso.trans_hom,
      Iso.trans_inv, NatTrans.comp_app, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      eqToHom_app, Category.assoc] using
      rightTriangle_comp_transport S hS (X.map a) (X.map b) (X.map (a ≫ b))
        (c.ι.app _) (c.ι.app _) (c.ι.app _) (X.map_comp a b)
        (c.w a) (c.w b) (c.w (a ≫ b)) K

end FromCocone

end AdjunctionData.Cone

end CategoryTheory.InjectiveSystem
