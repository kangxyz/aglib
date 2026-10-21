/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericFiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TorsorAction

/-!
# Unique extension of generic torsors on supplied finite-etale covers

The actual generic torsor action extends uniquely on a SUPPLIED finite-etale model cover over a
normal integral base. Native finite-etale generic full faithfulness provides the extension
mechanism.

Source: `R5Lab.Aglib.AlgebraicGeometry.Normalization.GenericTorsorExtension`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`32bd0196aab955c918c262668a78df900634162ff4a338c563c12d19357ce775`. Selected lines: [[47, 315]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
open _root_.AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open _root_.CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericTorsorExtension

universe u

attribute [local instance] Over.cartesianMonoidalCategory GroupDescent.coverCartesian

variable (X : Scheme.{u}) [IsIntegral X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

/-- Actual pullback along the canonical function-field inclusion. -/
abbrev genericFunctor := Over.pullback (X.fromSpecStalk (genericPoint X))

variable (A : Grp (Over X)) [IsFinite A.X.hom] [Etale A.X.hom] (Y : Scheme.FiniteEtale X)

/-- The supplied actual coefficient group, viewed as a finite-etale cover. -/
abbrev coefficientCover : Scheme.FiniteEtale X := ⟨A.X, ⟨inferInstance, inferInstance⟩⟩
/-- The actual coefficient group pulled back to the generic point. -/
abbrev genericGroup : Grp (Over (Spec X.functionField)) := (genericFunctor X).mapGrp.obj A

variable (τ : TorsorAction (genericGroup X A) (toUnit ((genericFunctor X).obj Y.obj)))

/-- The original generic action on the literal generic pullback of the
actual coefficient/source product, via the canonical product comparison. -/
def genericActionCoverMap :
    (baseChange (X.fromSpecStalk (genericPoint X))).obj (coefficientCover X A ⊗ Y) ⟶
      (baseChange (X.fromSpecStalk (genericPoint X))).obj Y :=
  ObjectProperty.homMk
    ((Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).inv ≫ τ.actionMap)

/-- Actual extension of the original generic coefficient-group action map. -/
def extendedActionMap : A.X ⊗ Y.obj ⟶ Y.obj :=
  (extendGenericFiberMap X (coefficientCover X A ⊗ Y) Y (genericActionCoverMap X A Y τ)).hom

theorem extendedActionMap_generic :
    (genericFunctor X).map (extendedActionMap X A Y τ) =
      (Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).inv ≫ τ.actionMap := by
  exact congrArg (fun f => f.hom)
    (baseChange_extendGenericFiberMap X (coefficientCover X A ⊗ Y) Y
      (genericActionCoverMap X A Y τ))

/-- Faithfulness for finite-etale actual Over morphisms, derived from the
constructed generic-restriction functor. -/
theorem finiteOver_map_ext (Z W : Scheme.FiniteEtale X) {f g : Z.obj ⟶ W.obj}
    (h : (genericFunctor X).map f = (genericFunctor X).map g) : f = g := by
  have hc : (baseChange (X.fromSpecStalk (genericPoint X))).map (ObjectProperty.homMk f) =
      (baseChange (X.fromSpecStalk (genericPoint X))).map (ObjectProperty.homMk g) := by
    apply ObjectProperty.hom_ext
    exact h
  exact congrArg (fun f => f.hom) (genericFiber_hom_ext X Z W hc)

/-- Evaluation of the actual extended action has exactly the original
generic action; this holds for every actual test object over X. -/
theorem extendedActionMap_evaluation {T : Over X} (a : T ⟶ A.X) (x : T ⟶ Y.obj) :
    (genericFunctor X).map (lift a x ≫ extendedActionMap X A Y τ) =
      τ.act ((genericFunctor X).map a) ((genericFunctor X).map x) := by
  rw [Functor.map_comp, extendedActionMap_generic]
  have hl : (genericFunctor X).map (lift a x) ≫
      (Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).inv =
        lift ((genericFunctor X).map a) ((genericFunctor X).map x) := by
    apply (cancel_mono (Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (Functor.Monoidal.lift_μ (genericFunctor X) a x).symm
  rw [← Category.assoc, hl]
  exact τ.comp_actionMap _ _

/-- The unit identity is derived as an equality of actual scheme maps. -/
theorem extendedActionMap_one :
    lift (1 : Y.obj ⟶ A.X) (𝟙 Y.obj) ≫ extendedActionMap X A Y τ = 𝟙 Y.obj := by
  apply finiteOver_map_ext X Y Y
  rw [extendedActionMap_evaluation, Functor.map_one]
  exact τ.one_act _

/-- The multiplication identity on an actual finite-etale test cover. -/
theorem extendedActionMap_mul_on_cover (T : Scheme.FiniteEtale X) (a b : T.obj ⟶ A.X)
    (x : T.obj ⟶ Y.obj) :
    lift (a * b) x ≫ extendedActionMap X A Y τ =
      lift a (lift b x ≫ extendedActionMap X A Y τ) ≫ extendedActionMap X A Y τ := by
  apply finiteOver_map_ext X T Y
  rw [extendedActionMap_evaluation, extendedActionMap_evaluation,
    extendedActionMap_evaluation, Functor.map_mul, τ.mul_act]

/-- The multiplication diagram on the actual coefficient/source triple
product is a conclusion, rather than supplied global action data. -/
theorem extendedActionMap_mul :
    let a := fst (A.X ⊗ A.X) Y.obj ≫ fst A.X A.X
    let b := fst (A.X ⊗ A.X) Y.obj ≫ snd A.X A.X
    let x := snd (A.X ⊗ A.X) Y.obj
    lift (a * b) x ≫ extendedActionMap X A Y τ =
      lift a (lift b x ≫ extendedActionMap X A Y τ) ≫ extendedActionMap X A Y τ :=
  extendedActionMap_mul_on_cover X A Y τ ((coefficientCover X A ⊗ coefficientCover X A) ⊗ Y)
    _ _ _

private def genericTransporterIso :
    (genericGroup X A).X ⊗ ((genericFunctor X).obj Y.obj) ≅
      ((genericFunctor X).obj Y.obj) ⊗ ((genericFunctor X).obj Y.obj) :=
  τ.action_isPullback.isoIsPullback _ _
    (IsPullback.of_is_product
      (tensorProductIsBinaryProduct ((genericFunctor X).obj Y.obj) ((genericFunctor X).obj Y.obj))
      isTerminalTensorUnit)

omit [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] [IsFinite A.X.hom] [Etale A.X.hom] in
private theorem genericTransporterIso_hom :
    (genericTransporterIso X A Y τ).hom =
      lift τ.actionMap (snd (genericGroup X A).X ((genericFunctor X).obj Y.obj)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [genericTransporterIso]
  · simp [genericTransporterIso]

/-- The actual extended torsor comparison (a,x) ↦ (a.x,x). -/
def extendedTransporter : A.X ⊗ Y.obj ⟶ Y.obj ⊗ Y.obj :=
  lift (extendedActionMap X A Y τ) (snd A.X Y.obj)

private theorem extendedTransporter_generic :
    (Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).hom ≫
      (genericFunctor X).map (extendedTransporter X A Y τ) ≫
        (Functor.Monoidal.μIso (genericFunctor X) Y.obj Y.obj).inv =
          (genericTransporterIso X A Y τ).hom := by
  simp only [extendedTransporter, Functor.Monoidal.μIso_inv]
  rw [Functor.OplaxMonoidal.lift_δ]
  rw [comp_lift, extendedActionMap_generic]
  simp only [Iso.hom_inv_id_assoc]
  rw [Functor.Monoidal.μIso_hom, Functor.Monoidal.μ_snd]
  exact (genericTransporterIso_hom X A Y τ).symm

/-- The torsor square is an actual isomorphism on the supplied finite-etale
models. The generic isomorphism and the constructed full-faithful functor
prove this; it is not a global square premise. -/
instance extendedTransporterIsIso : IsIso (extendedTransporter X A Y τ) := by
  have : IsIso ((genericFunctor X).map (extendedTransporter X A Y τ)) := by
    have he := congrArg
      (fun h => (Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).inv ≫ h ≫
        (Functor.Monoidal.μIso (genericFunctor X) Y.obj Y.obj).hom)
      (extendedTransporter_generic X A Y τ)
    have he' : (genericFunctor X).map (extendedTransporter X A Y τ) =
        (Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).inv ≫
          (genericTransporterIso X A Y τ).hom ≫
            (Functor.Monoidal.μIso (genericFunctor X) Y.obj Y.obj).hom := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id] using he
    rw [he']
    infer_instance
  let h : coefficientCover X A ⊗ Y ⟶ Y ⊗ Y := ObjectProperty.homMk (extendedTransporter X A Y τ)
  have : IsIso ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget (Spec X.functionField)).map
      ((baseChange (X.fromSpecStalk (genericPoint X))).map h)) := by
    change IsIso ((genericFunctor X).map (extendedTransporter X A Y τ))
    infer_instance
  have : IsIso ((baseChange (X.fromSpecStalk (genericPoint X))).map h) :=
    isIso_of_reflects_iso _ (_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget
      (Spec X.functionField))
  have : IsIso h := isIso_of_reflects_iso _ (baseChange (X.fromSpecStalk (genericPoint X)))
  exact inferInstanceAs (IsIso ((_root_.AlgebraicGeometry.Scheme.FiniteEtale.forget X).map h))

/-- The actual extended transporter as an Over-scheme isomorphism. -/
def extendedTransporterIso : A.X ⊗ Y.obj ≅ Y.obj ⊗ Y.obj :=
  asIso (extendedTransporter X A Y τ)

/-- The inverse extended transporter gives unique transport for every
scheme test object, including nonreduced test schemes. -/
theorem extendedTransport_unique {T : Over X} (x y : T ⟶ Y.obj) :
    ∃! a : T ⟶ A.X, lift a x ≫ extendedActionMap X A Y τ = y := by
  let z : T ⟶ A.X ⊗ Y.obj := lift y x ≫ (extendedTransporterIso X A Y τ).inv
  have hz : z ≫ extendedTransporter X A Y τ = lift y x := by
    simp [z, extendedTransporterIso]
  have hy : z ≫ extendedActionMap X A Y τ = y := by
    have h := congrArg (fun f => f ≫ fst Y.obj Y.obj) hz
    simpa only [extendedTransporter, Category.assoc, lift_fst] using h
  have hx : z ≫ snd A.X Y.obj = x := by
    have h := congrArg (fun f => f ≫ snd Y.obj Y.obj) hz
    simpa only [extendedTransporter, Category.assoc, lift_snd] using h
  refine ⟨z ≫ fst A.X Y.obj, ?_, ?_⟩
  · change lift (z ≫ fst A.X Y.obj) x ≫ extendedActionMap X A Y τ = y
    rw [← hx, lift_comp_fst_snd]
    exact hy
  · intro a ha
    have hh : lift a x ≫ extendedTransporter X A Y τ = lift y x := by
      apply CartesianMonoidalCategory.hom_ext
      · simpa only [extendedTransporter, Category.assoc, lift_fst] using ha
      · simp only [extendedTransporter, Category.assoc, lift_snd]
    have he : lift a x = z := (cancel_mono (extendedTransporter X A Y τ)).mp
      (hh.trans hz.symm)
    simpa only [lift_fst] using congrArg (fun f => f ≫ fst A.X Y.obj) he

/-- Source K2-018#prop:k2018-arithmetic-characters, module revision: the
actual generic torsor action extends to the SAME supplied finite-etale cover
and SAME coefficient group scheme over X. All action laws and the torsor
comparison are conclusions. Local nonemptiness is a separate geometric input. -/
def extendedTorsor : TorsorAction A (toUnit Y.obj) where
  act a x := lift a x ≫ extendedActionMap X A Y τ
  naturality f a x := by simp only [comp_lift_assoc]
  one_act x := by
    have h := congrArg (fun f => x ≫ f) (extendedActionMap_one X A Y τ)
    simpa only [comp_lift_assoc, MonObj.comp_one, Category.comp_id] using h
  mul_act a b x := by
    have h := congrArg (fun f => lift (lift a b) x ≫ f) (extendedActionMap_mul X A Y τ)
    simpa only [comp_lift_assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd,
      lift_fst] using h
  over a x := toUnit_unique _ _
  transport x y _ := extendedTransport_unique X A Y τ x y

theorem extendedTorsor_actionMap :
    (extendedTorsor X A Y τ).actionMap = extendedActionMap X A Y τ := by
  change lift (fst A.X Y.obj) (snd A.X Y.obj) ≫ extendedActionMap X A Y τ = _
  rw [lift_fst_snd, Category.id_comp]

/-- The extended torsor retains the original generic action with the
canonical product comparison; no marking or coefficient group is replaced. -/
theorem extendedTorsor_generic :
    (genericFunctor X).map (extendedTorsor X A Y τ).actionMap =
      (Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).inv ≫ τ.actionMap := by
  rw [extendedTorsor_actionMap]
  exact extendedActionMap_generic X A Y τ

/-- The action extension is unique once its ORIGINAL generic action is fixed. -/
theorem extendedTorsor_unique (σ : TorsorAction A (toUnit Y.obj))
    (hσ : (genericFunctor X).map σ.actionMap =
      (Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).inv ≫ τ.actionMap) :
    σ = extendedTorsor X A Y τ := by
  have he : σ.actionMap = extendedActionMap X A Y τ :=
    finiteOver_map_ext X (coefficientCover X A ⊗ Y) Y
      (hσ.trans (extendedActionMap_generic X A Y τ).symm)
  apply _root_.CategoryTheory.TorsorAction.ext
  intro T a x
  rw [← σ.comp_actionMap, he]
  rfl

/-- Exactly one actual global action/torsor-square package extends the
original generic torsor on these same supplied objects. -/
theorem existsUnique_torsor_extension :
    ∃! σ : TorsorAction A (toUnit Y.obj),
      (genericFunctor X).map σ.actionMap =
        (Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).inv ≫ τ.actionMap := by
  refine ⟨extendedTorsor X A Y τ, extendedTorsor_generic X A Y τ, ?_⟩
  exact fun σ hσ => extendedTorsor_unique X A Y τ σ hσ

section TorsorMaps

variable (Z : Scheme.FiniteEtale X)
  (υ : TorsorAction (genericGroup X A) (toUnit ((genericFunctor X).obj Z.obj)))

/-- An actual map between the original generic torsors extends uniquely as
a cover map, and its equivariance is a derived equality of global scheme maps. -/
theorem extendCoverMap_equivariant
    (h : (baseChange (X.fromSpecStalk (genericPoint X))).obj Y ⟶
      (baseChange (X.fromSpecStalk (genericPoint X))).obj Z)
    (hh : τ.actionMap ≫ h.hom =
      lift (fst (genericGroup X A).X ((genericFunctor X).obj Y.obj))
        (snd (genericGroup X A).X ((genericFunctor X).obj Y.obj) ≫ h.hom) ≫ υ.actionMap) :
    extendedActionMap X A Y τ ≫ (extendGenericFiberMap X Y Z h).hom =
      lift (fst A.X Y.obj) (snd A.X Y.obj ≫ (extendGenericFiberMap X Y Z h).hom) ≫
        extendedActionMap X A Z υ := by
  have hf : (genericFunctor X).map (extendGenericFiberMap X Y Z h).hom = h.hom :=
    congrArg (fun f => f.hom) (baseChange_extendGenericFiberMap X Y Z h)
  apply finiteOver_map_ext X (coefficientCover X A ⊗ Y) Z
  apply (cancel_epi (Functor.Monoidal.μIso (genericFunctor X) A.X Y.obj).hom).mp
  rw [extendedActionMap_evaluation]
  simp only [CategoryTheory.Functor.map_comp, extendedActionMap_generic,
    Category.assoc, Iso.hom_inv_id_assoc, hf]
  rw [υ.naturality]
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μ_fst,
    Functor.Monoidal.μ_snd_assoc]
  exact hh.trans (υ.comp_actionMap _ _)

end TorsorMaps

omit [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] [IsFinite A.X.hom] [Etale A.X.hom] in
/-- A nonempty ORIGINAL generic fibre of a finite cover makes the supplied
cover surjective over the integral base. Thus the geometric nonemptiness
needed for a torsor is inherited from the original generic torsor. -/
theorem cover_surjective_of_generic_nonempty
    [Nonempty ↥(pullback (C := Scheme) Y.obj.hom (X.fromSpecStalk (genericPoint X)))] :
    Surjective Y.obj.hom := by
  obtain ⟨p⟩ := ‹Nonempty ↥(pullback (C := Scheme) Y.obj.hom (X.fromSpecStalk (genericPoint X)))›
  have hp : Y.obj.hom (pullback.fst Y.obj.hom (X.fromSpecStalk (genericPoint X)) p) =
      genericPoint X := by
    have h := congrArg (fun f : pullback Y.obj.hom (X.fromSpecStalk (genericPoint X)) ⟶ X => f p)
      (pullback.condition (f := Y.obj.hom) (g := (X.fromSpecStalk (genericPoint X))))
    simpa only [Scheme.Hom.comp_apply, fromSpecStalk_genericPoint_apply] using h
  have hg : genericPoint X ∈ Set.range Y.obj.hom := ⟨_, hp⟩
  have hclosed := Y.obj.hom.isClosedMap.isClosed_range
  constructor
  intro x
  exact ((genericPoint_spec X).specializes (Set.mem_univ x)).mem_closed hclosed hg

end AlgebraicGeometry.Scheme.FiniteEtale.GenericTorsorExtension
