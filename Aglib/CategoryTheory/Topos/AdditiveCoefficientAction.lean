/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Topos.SheafMorphism
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate
public import Aglib.CategoryTheory.Sites.Continuous.Limits
public import Aglib.CategoryTheory.Sites.Pullback.Coefficients
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Native additive coefficients over a sheaf geometric morphism

The Set and additive adjunctions are the actual supplied native adjunctions.
The observation comparison preserves the original group operations. The
left comparison is its native mate, with its original unit equation.
No torsor, cohomology, ring or module comparison law is stored here.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Topos

universe uC vC uD vD w

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace AdditiveCoefficientAction

/-- The original underlying Set sheaf of an additive sheaf. -/
abbrev observation (J : GrothendieckTopology C) :
    Sheaf J AddCommGrpCat.{w} ⥤ Sheaf J (Type w) :=
  sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})

/-- The actual zero as a morphism from the selected terminal sheaf. -/
def zeroMap (A : Sheaf J AddCommGrpCat.{w}) :
    terminalSheaf J ⟶ (observation J).obj A where
  hom.app U := TypeCat.ofHom fun _ => (0 : A.obj.obj U)
  hom.naturality {U V} f := by
    ext x
    exact (A.obj.map f).hom.map_zero.symm

/-- The original pointwise additive inverse. -/
def negMap (A : Sheaf J AddCommGrpCat.{w}) :
    (observation J).obj A ⟶ (observation J).obj A where
  hom.app U := TypeCat.ofHom fun x => -(show A.obj.obj U from x)
  hom.naturality {U V} f := by
    ext x
    exact ((A.obj.map f).hom.map_neg (show A.obj.obj U from x)).symm

/-- Addition on the same native product of underlying Set sheaves. -/
def addMap (A : Sheaf J AddCommGrpCat.{w}) :
    (observation J).obj A ⨯ (observation J).obj A ⟶ (observation J).obj A where
  hom.app U := TypeCat.ofHom fun x =>
    (show A.obj.obj U from
      (prod.fst : (observation J).obj A ⨯ (observation J).obj A ⟶ _).hom.app U x) +
    (show A.obj.obj U from
      (prod.snd : (observation J).obj A ⨯ (observation J).obj A ⟶ _).hom.app U x)
  hom.naturality {U V} f := by
    ext x
    have hf := ConcreteCategory.congr_hom
      ((prod.fst : (observation J).obj A ⨯ (observation J).obj A ⟶
        (observation J).obj A).hom.naturality f) x
    have hs := ConcreteCategory.congr_hom
      ((prod.snd : (observation J).obj A ⨯ (observation J).obj A ⟶
        (observation J).obj A).hom.naturality f) x
    simp only [ConcreteCategory.comp_apply] at hf hs
    change
      (show A.obj.obj V from (prod.fst : (observation J).obj A ⨯
        (observation J).obj A ⟶ _).hom.app V
          (((observation J).obj A ⨯ (observation J).obj A).obj.map f x)) +
      (show A.obj.obj V from (prod.snd : (observation J).obj A ⨯
        (observation J).obj A ⟶ _).hom.app V
          (((observation J).obj A ⨯ (observation J).obj A).obj.map f x)) =
        A.obj.map f (_ + _)
    rw [hf, hs]
    exact ((A.obj.map f).hom.map_add _ _).symm

/-- The native right-adjoint product comparison, with its original product objects. -/
def directProductIso
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (A B : Sheaf K (Type w)) :
    f.right.obj (A ⨯ B) ≅ f.right.obj A ⨯ f.right.obj B := by
  let : f.right.IsRightAdjoint := f.adj.isRightAdjoint
  exact asIso (prodComparison f.right A B)

/-- The original transpose of the unique terminal arrow. -/
def directTerminalMap
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))) :
    terminalSheaf J ⟶ f.right.obj (terminalSheaf K) :=
  (f.adj.homEquiv _ _) ((terminalSheafIsTerminal K).from _)

end AdditiveCoefficientAction

open AdditiveCoefficientAction in
/-- The additive fragment of an actual coefficient action over a Set geometric morphism.
The actual additive adjunction is an index, so its functors and units are not reselected. -/
structure AdditiveCoefficientAction
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (a : LeftExactAdjunction (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})) where
  /-- The original additive direct image observes the same Set direct image. -/
  abSetComparison : a.right ⋙ observation J ≅ observation K ⋙ f.right
  /-- Actual zero is preserved through the native terminal comparison. -/
  abZeroCompatible : ∀ A,
    zeroMap (a.right.obj A) ≫ abSetComparison.hom.app A =
      directTerminalMap f ≫ f.right.map (zeroMap A)
  /-- Actual additive inverse is preserved. -/
  abNegCompatible : ∀ A,
    negMap (a.right.obj A) ≫ abSetComparison.hom.app A =
      abSetComparison.hom.app A ≫ f.right.map (negMap A)
  /-- Actual addition is preserved through the native product comparison. -/
  abAddCompatible : ∀ A,
    addMap (a.right.obj A) ≫ abSetComparison.hom.app A =
      prod.map (abSetComparison.hom.app A) (abSetComparison.hom.app A) ≫
        (directProductIso f ((observation K).obj A) ((observation K).obj A)).inv ≫
          f.right.map (addMap A)

namespace AdditiveCoefficientAction

variable {f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))}
  {a : LeftExactAdjunction (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})}

/-- The original native mate of the additive right observation comparison. -/
def leftComparison (s : AdditiveCoefficientAction f a) :
    observation J ⋙ f.left.obj ⟶ a.left.obj ⋙ observation K :=
  ((CategoryTheory.mateEquiv a.adj f.adj).symm
    (TwoSquare.mk _ _ _ _ s.abSetComparison.hom)).natTrans

/-- The comparison has the literal unit equation of that same native mate. -/
@[reassoc]
theorem leftComparison_unit (s : AdditiveCoefficientAction f a)
    (A : Sheaf J AddCommGrpCat.{w}) :
    (observation J).map (a.adj.unit.app A) ≫
        s.abSetComparison.hom.app (a.left.obj.obj A) =
      f.adj.unit.app ((observation J).obj A) ≫ f.right.map (s.leftComparison.app A) :=
  unit_mateEquiv_symm a.adj f.adj (TwoSquare.mk _ _ _ _ s.abSetComparison.hom) A

section NativeSite

variable (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K]
  [(F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [PreservesFiniteLimits (F.sheafPullback (Type w) J K)]

/-- Native reindexing retains the original addition and product comparison. -/
private theorem addMap_reindex (A : Sheaf K AddCommGrpCat.{w}) :
    (directProductIso (SheafMorphism.ofSiteFunctor F J K)
        ((observation K).obj A) ((observation K).obj A)).inv ≫
      (F.sheafPushforwardContinuous (Type w) J K).map (addMap A) =
        addMap ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj A) := by
  let R := F.sheafPushforwardContinuous (Type w) J K
  let X := (observation K).obj A
  let d := directProductIso (SheafMorphism.ofSiteFunctor F J K) X X
  have hf : d.inv ≫ R.map (prod.fst : X ⨯ X ⟶ X) = prod.fst := by
    rw [← prodComparison_fst R X X]
    exact d.inv_hom_id_assoc _
  have hs : d.inv ≫ R.map (prod.snd : X ⨯ X ⟶ X) = prod.snd := by
    rw [← prodComparison_snd R X X]
    exact d.inv_hom_id_assoc _
  ext U x
  have hfst := congrArg
    (fun q : R.obj X ⨯ R.obj X ⟶ R.obj X => q.hom.app U x) hf
  have hsnd := congrArg
    (fun q : R.obj X ⨯ R.obj X ⟶ R.obj X => q.hom.app U x) hs
  change (prod.fst : X ⨯ X ⟶ X).hom.app (F.op.obj U) (d.inv.hom.app U x) =
    (prod.fst : R.obj X ⨯ R.obj X ⟶ R.obj X).hom.app U x at hfst
  change (prod.snd : X ⨯ X ⟶ X).hom.app (F.op.obj U) (d.inv.hom.app U x) =
    (prod.snd : R.obj X ⨯ R.obj X ⟶ R.obj X).hom.app U x at hsnd
  change
    (show A.obj.obj (F.op.obj U) from
      (prod.fst : X ⨯ X ⟶ X).hom.app (F.op.obj U) (d.inv.hom.app U x)) +
    (show A.obj.obj (F.op.obj U) from
      (prod.snd : X ⨯ X ⟶ X).hom.app (F.op.obj U) (d.inv.hom.app U x)) =
    (show A.obj.obj (F.op.obj U) from
      (prod.fst : R.obj X ⨯ R.obj X ⟶ R.obj X).hom.app U x) +
    (show A.obj.obj (F.op.obj U) from
      (prod.snd : R.obj X ⨯ R.obj X ⟶ R.obj X).hom.app U x)
  rw [hfst, hsnd]

variable [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{w} J K)]

/-- The original coefficient adjunction with its genuine finite-limit capability. -/
def coefficientAdjunctionOfSiteFunctor :
    LeftExactAdjunction (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w}) :=
  LeftExactAdjunction.ofAdjunction (F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K)

/-- The native continuous-site additive action, using the original functors and units. -/
def ofSiteFunctor :
    AdditiveCoefficientAction (SheafMorphism.ofSiteFunctor F J K)
      (coefficientAdjunctionOfSiteFunctor F J K) where
  abSetComparison := Iso.refl _
  abZeroCompatible := by
    intro A
    ext U x
    change (0 : A.obj.obj (F.op.obj U)) = 0
    rfl
  abNegCompatible := by
    intro A
    ext U x
    change -(show A.obj.obj (F.op.obj U) from x) =
      -(show A.obj.obj (F.op.obj U) from x)
    rfl
  abAddCompatible := by
    intro A
    change addMap ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj A) ≫ 𝟙 _ =
      prod.map (𝟙 _) (𝟙 _) ≫
        (directProductIso (SheafMorphism.ofSiteFunctor F J K)
          ((observation K).obj A) ((observation K).obj A)).inv ≫
        (F.sheafPushforwardContinuous (Type w) J K).map (addMap A)
    rw [Category.comp_id, prod.map_id_id, Category.id_comp]
    exact (addMap_reindex F J K A).symm

@[simp]
theorem ofSiteFunctor_abSetComparison :
    (ofSiteFunctor F J K).abSetComparison = Iso.refl _ := rfl

section UnderlyingComparison

variable [HasWeakSheafify K AddCommGrpCat.{w}] [HasWeakSheafify K (Type w)]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasLeftKanExtension P]
  [∀ P : Cᵒᵖ ⥤ Type w, F.op.HasLeftKanExtension P]
  [(CategoryTheory.forget AddCommGrpCat.{w}).PreservesLeftKanExtensions F.op]
  [K.PreservesSheafification (CategoryTheory.forget AddCommGrpCat.{w})]

/-- The native coefficient Iso is exactly the mate fixed by the original unit equation. -/
theorem ofSiteFunctor_leftComparison :
    (ofSiteFunctor F J K).leftComparison =
      (Functor.sheafPullbackCoefficientIso F J K
        (CategoryTheory.forget AddCommGrpCat.{w})).hom := by
  apply NatTrans.ext
  funext A
  apply ((F.sheafAdjunctionContinuous (Type w) J K).homEquiv _ _).injective
  change (F.sheafAdjunctionContinuous (Type w) J K).unit.app
      ((observation J).obj A) ≫
        (F.sheafPushforwardContinuous (Type w) J K).map
          ((ofSiteFunctor F J K).leftComparison.app A) = _
  have h := leftComparison_unit (ofSiteFunctor F J K) A
  change (observation J).map
      ((F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app A) ≫ 𝟙 _ =
    (F.sheafAdjunctionContinuous (Type w) J K).unit.app ((observation J).obj A) ≫
      (F.sheafPushforwardContinuous (Type w) J K).map
        ((ofSiteFunctor F J K).leftComparison.app A) at h
  exact (h.symm.trans (Category.comp_id _)).trans
    (Functor.sheafPullbackCoefficientIso_unit F J K
      (CategoryTheory.forget AddCommGrpCat.{w}) A).symm

/-- The genuine native Kan/sheafification capabilities make this actual mate invertible. -/
instance ofSiteFunctor_leftComparison_isIso : IsIso (ofSiteFunctor F J K).leftComparison := by
  rw [ofSiteFunctor_leftComparison]
  exact Iso.isIso_hom (Functor.sheafPullbackCoefficientIso F J K
    (CategoryTheory.forget AddCommGrpCat.{w}))

end UnderlyingComparison
end NativeSite
end AdditiveCoefficientAction
end CategoryTheory.Topos
