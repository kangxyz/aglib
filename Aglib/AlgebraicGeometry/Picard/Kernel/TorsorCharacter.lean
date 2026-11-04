/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.PowerBaseChange
public import Aglib.AlgebraicGeometry.Picard.FrameTensor
public import Aglib.AlgebraicGeometry.Picard.UnitDescent
public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.LineBundle.Single

/-!
# The original trivialized line-bundle cocycle

Restrict the same frame along two maps into the original cover which agree
below. The ratio of these two frames is an actual structure-module
isomorphism. Its global unit obeys the original cocycle, pullback and tensor
laws. This ratio is precisely the canonical descent transition transported
through the given frame, with direction from the first map to the second.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Pseudofunctor Opposite

universe u v v' u' u''

namespace AlgebraicGeometry.Scheme.Modules.TrivializedDescent

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
open Invertible.TrivializedPower (unitOfIso)
open Invertible.TrivializedPowerTorsor Invertible.PowerBaseChange
open Invertible.ScalarAutomorphisms (scalarIso unitAutoEquiv)

variable {X Y V W : Scheme.{u}} (q : X ⟶ Y) (L : LineBundle Y)
  (a : (pullback q).obj L.val ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))

/-- The transported original transition is the ratio of the two actual
restrictions of the supplied frame. The direction is from `v` to `w`. -/
def transition (s : V ⟶ Y) (v w : V ⟶ X) (hv : v ≫ q = s) (hw : w ≫ q = s) :
    (SheafOfModules.unit V.ringCatSheaf : V.Modules) ≅
      SheafOfModules.unit V.ringCatSheaf :=
  (nativePullFrame L q s v hv a).symm ≪≫ nativePullFrame L q s w hw a

/-- The actual global unit of the transported original transition. -/
def unit (s : V ⟶ Y) (v w : V ⟶ X) (hv : v ≫ q = s) (hw : w ≫ q = s) :
    Γ(V, ⊤)ˣ := unitOfIso V (transition q L a s v w hv hw)

/-- A repeated overlap map has exactly the identity transition. -/
theorem transition_self (s : V ⟶ Y) (v : V ⟶ X) (hv : v ≫ q = s) :
    transition q L a s v v hv hv = Iso.refl _ := by
  apply Iso.ext
  simp only [transition, Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id, Iso.refl_hom]

/-- The transported original transitions obey the original cocycle law. -/
theorem transition_comp (s : V ⟶ Y) (v w z : V ⟶ X)
    (hv : v ≫ q = s) (hw : w ≫ q = s) (hz : z ≫ q = s) :
    transition q L a s v w hv hw ≪≫ transition q L a s w z hw hz =
      transition q L a s v z hv hz := by
  apply Iso.ext
  simp only [transition, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

/-- The transition units satisfy the multiplicative cocycle law. -/
theorem unit_comp (s : V ⟶ Y) (v w z : V ⟶ X)
    (hv : v ≫ q = s) (hw : w ≫ q = s) (hz : z ≫ q = s) :
    unit q L a s v w hv hw * unit q L a s w z hw hz = unit q L a s v z hv hz := by
  rw [unit, unit, ← unitOfIso_trans, transition_comp]
  rfl

/-- The actual frame scalar of the identity automorphism is one. -/
@[simp]
theorem unitOfIso_refl (V : Scheme.{u}) :
    unitOfIso V (Iso.refl (SheafOfModules.unit V.ringCatSheaf)) = 1 := by
  apply Units.ext
  rfl

/-- The identity transition function is the actual unit function. -/
@[simp]
theorem unit_self (s : V ⟶ Y) (v : V ⟶ X) (hv : v ≫ q = s) :
    unit q L a s v v hv hv = 1 := by
  rw [unit, transition_self, unitOfIso_refl]

/-- The original transition commutes with arbitrary restriction. The
common composition isomorphism of the two restricted frames cancels. -/
theorem transition_pullback (r : W ⟶ V) (s : V ⟶ Y) (v w : V ⟶ X)
    (hv : v ≫ q = s) (hw : w ≫ q = s) :
    (pullbackUnitIso r).symm ≪≫
        (pullback r).mapIso (transition q L a s v w hv hw) ≪≫ pullbackUnitIso r =
      transition q L a (r ≫ s) (r ≫ v) (r ≫ w)
        (by rw [Category.assoc, hv]) (by rw [Category.assoc, hw]) := by
  let ev := nativePullFrame L q s v hv a
  let ew := nativePullFrame L q s w hw a
  have h₁ := nativePullFrame_comp L q s (r ≫ s) v r hv rfl a
  have h₂ := nativePullFrame_comp L q s (r ≫ s) w r hw rfl a
  unfold transition
  rw [← h₁, ← h₂]
  let c : (pullback (r ≫ s)).obj L.val ≅ (pullback r).obj ((pullback s).obj L.val) :=
    ((pullbackCongr (rfl : r ≫ s = r ≫ s)).app L.val).symm ≪≫
      ((pullbackComp r s).app L.val).symm
  change _ = (c ≪≫ (pullback r).mapIso ev ≪≫ pullbackUnitIso r).symm ≪≫
    (c ≪≫ (pullback r).mapIso ew ≪≫ pullbackUnitIso r)
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, ev, ew]

/-- Pullback of the actual transition unit is the unit on the pulled-back
original overlap, without a reducedness restriction. -/
theorem unit_pullback (r : W ⟶ V) (s : V ⟶ Y) (v w : V ⟶ X)
    (hv : v ≫ q = s) (hw : w ≫ q = s) :
    Units.map r.appTop.hom.toMonoidHom (unit q L a s v w hv hw) =
      unit q L a (r ≫ s) (r ≫ v) (r ≫ w)
        (by rw [Category.assoc, hv]) (by rw [Category.assoc, hw]) := by
  rw [unit, ← unitOfIso_pullback, transition_pullback]
  rfl

/-- Multiplying the first restricted frame by the original transition
unit gives the second restricted frame. -/
theorem nativePullFrame_eq_scalar (s : V ⟶ Y) (v w : V ⟶ X)
    (hv : v ≫ q = s) (hw : w ≫ q = s) :
    nativePullFrame L q s w hw a = nativePullFrame L q s v hv a ≪≫
      scalarIso V _ (unit q L a s v w hv hw) := by
  have hu := (unitAutoEquiv V).left_inv (transition q L a s v w hv hw)
  change scalarIso V _ (unit q L a s v w hv hw) = _ at hu
  rw [hu]
  apply Iso.ext
  simp only [transition, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- Tensoring the actual line bundles with their actual tensor frame
multiplies the original transition units. -/
theorem unit_tensor (N : LineBundle Y)
    (b : (pullback q).obj N.val ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (s : V ⟶ Y) (v w : V ⟶ X) (hv : v ≫ q = s) (hw : w ≫ q = s) :
    unit q (tensorLineBundle Y L N) (FrameTensor.tensorFrame q L N a b) s v w hv hw =
      unit q L a s v w hv hw * unit q N b s v w hv hw := by
  have h₁ := FrameTensor.tensorFrame_pullback L N q s v hv a b
  have h₂ := FrameTensor.tensorFrame_pullback L N q s w hw a b
  change nativePullFrame (tensorLineBundle Y L N) q s v hv (FrameTensor.tensorFrame q L N a b) =
    FrameTensor.tensorFrame s L N (nativePullFrame L q s v hv a)
      (nativePullFrame N q s v hv b) at h₁
  change nativePullFrame (tensorLineBundle Y L N) q s w hw (FrameTensor.tensorFrame q L N a b) =
    FrameTensor.tensorFrame s L N (nativePullFrame L q s w hw a)
      (nativePullFrame N q s w hw b) at h₂
  rw [nativePullFrame_eq_scalar q L a s v w hv hw,
    nativePullFrame_eq_scalar q N b s v w hv hw, FrameTensor.tensorFrame_scalar] at h₂
  have ht : transition q (tensorLineBundle Y L N) (FrameTensor.tensorFrame q L N a b)
      s v w hv hw = scalarIso V _
        (unit q L a s v w hv hw * unit q N b s v w hv hw) := by
    unfold transition
    rw [h₁, h₂]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
  rw [unit, ht]
  exact (unitAutoEquiv V).right_inv _

/-- An isomorphism downstairs may be precomposed with the given frame
before or after restriction to an original overlap map. -/
theorem nativePullFrame_precompIso (N : LineBundle Y) (e : L.val ≅ N.val)
    (b : (pullback q).obj N.val ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (s : V ⟶ Y) (v : V ⟶ X) (hv : v ≫ q = s) :
    nativePullFrame L q s v hv ((pullback q).mapIso e ≪≫ b) =
      (pullback s).mapIso e ≪≫ nativePullFrame N q s v hv b := by
  subst s
  apply Iso.ext
  change 𝟙 _ ≫ (pullbackComp v q).inv.app L.val ≫
      (pullback v).map (((pullback q).mapIso e).hom ≫ b.hom) ≫
      (pullbackUnitIso v).hom =
    (pullback (v ≫ q)).map e.hom ≫ 𝟙 _ ≫ (pullbackComp v q).inv.app N.val ≫
      (pullback v).map b.hom ≫ (pullbackUnitIso v).hom
  simp only [Functor.mapIso_hom, Functor.map_comp, Category.assoc, Category.id_comp]
  rw [reassoc_of% (pullbackComp v q).inv.naturality e.hom]

/-- The same isomorphism downstairs cancels in the original transition
ratio. This is a statement about the actual frames and their pullbacks. -/
theorem unit_precompIso (N : LineBundle Y) (e : L.val ≅ N.val)
    (b : (pullback q).obj N.val ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (s : V ⟶ Y) (v w : V ⟶ X) (hv : v ≫ q = s) (hw : w ≫ q = s) :
    unit q L ((pullback q).mapIso e ≪≫ b) s v w hv hw = unit q N b s v w hv hw := by
  unfold unit transition
  rw [nativePullFrame_precompIso q L N e b s v hv,
    nativePullFrame_precompIso q L N e b s w hw]
  congr 1
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- A change of the upstairs frame by a unit with equal restrictions on
the two overlap maps does not change the original transition unit. -/
theorem unit_postcompose_scalar (c : Γ(X, ⊤)ˣ)
    (s : V ⟶ Y) (v w : V ⟶ X) (hv : v ≫ q = s) (hw : w ≫ q = s)
    (hc : Units.map v.appTop.hom.toMonoidHom c = Units.map w.appTop.hom.toMonoidHom c) :
    unit q L (a ≪≫ scalarIso X _ c) s v w hv hw = unit q L a s v w hv hw := by
  let e := scalarIso V (SheafOfModules.unit V.ringCatSheaf)
    (Units.map w.appTop.hom.toMonoidHom c)
  have ht : transition q L (a ≪≫ scalarIso X _ c) s v w hv hw =
      e.symm ≪≫ transition q L a s v w hv hw ≪≫ e := by
    unfold transition
    rw [nativePullFrame_scalar, nativePullFrame_scalar, hc]
    apply Iso.ext
    simp only [e, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]
  rw [unit, ht, unitOfIso_trans, unitOfIso_trans]
  have he : e.symm ≪≫ e = Iso.refl _ := Iso.ext e.inv_hom_id
  rw [mul_left_comm, ← unitOfIso_trans, he, unitOfIso_refl, mul_one]
  rfl

/-- The actual transition units are unchanged by pulling the same framed
bundle through a specified commuting base-change square. -/
theorem unit_pullbackFrame {Y' X' : Scheme.{u}} (f : Y' ⟶ Y) (q' : X' ⟶ Y')
    (g : X' ⟶ X) (h : g ≫ q = q' ≫ f)
    (s : V ⟶ Y') (v w : V ⟶ X') (hv : v ≫ q' = s) (hw : w ≫ q' = s) :
    unit q' (pullbackLineBundle f L) (pullbackFrame f L q q' g h a) s v w hv hw =
      unit q L a (s ≫ f) (v ≫ g) (w ≫ g)
        (by rw [Category.assoc, h, ← Category.assoc, hv])
        (by rw [Category.assoc, h, ← Category.assoc, hw]) := by
  unfold unit transition
  rw [pullbackFrame_restriction, pullbackFrame_restriction]
  congr 1
  apply Iso.ext
  simp only [pullbackFrame, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- The canonical trivial frame restricts to the canonical unit comparison
of the composite map. -/
theorem nativePullFrame_unit (s : V ⟶ Y) (v : V ⟶ X) (hv : v ≫ q = s) :
    nativePullFrame (FrameTorsor.unitBundle Y) q s v hv (pullbackUnitIso q) =
      pullbackUnitIso s := by
  subst s
  apply Iso.ext
  change 𝟙 _ ≫ (pullbackComp v q).inv.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      (pullback v).map (pullbackUnitIso q).hom ≫ (pullbackUnitIso v).hom =
    (pullbackUnitIso (v ≫ q)).hom
  rw [Category.id_comp, ← pullbackUnitIso_comp v q, Iso.inv_hom_id_app_assoc]

/-- The original trivial line bundle with its canonical frame has the
identity transition on every overlap. -/
@[simp]
theorem unit_trivial (s : V ⟶ Y) (v w : V ⟶ X) (hv : v ≫ q = s) (hw : w ≫ q = s) :
    unit q (FrameTorsor.unitBundle Y) (pullbackUnitIso q) s v w hv hw = 1 := by
  unfold unit transition
  have he : (pullbackUnitIso s).symm ≪≫ pullbackUnitIso s = Iso.refl _ :=
    Iso.ext (pullbackUnitIso s).inv_hom_id
  rw [nativePullFrame_unit q s v hv, nativePullFrame_unit q s w hw, he, unitOfIso_refl]

/-- The original transition unit is unchanged by equality of its
three underlying test maps. -/
theorem unit_congr {s s' : V ⟶ Y} {v w v' w' : V ⟶ X}
    (hv : v ≫ q = s) (hw : w ≫ q = s) (hv' : v' ≫ q = s') (hw' : w' ≫ q = s')
    (hs : s = s') (h₁ : v = v') (h₂ : w = w') :
    unit q L a s v w hv hw = unit q L a s' v' w' hv' hw' := by
  cases hs
  cases h₁
  cases h₂
  rfl

/-- A unit transition equal to one identifies the actual two restricted
frames, including their nilpotent information. -/
theorem nativePullFrame_eq_of_unit_eq_one (s : V ⟶ Y) (v w : V ⟶ X)
    (hv : v ≫ q = s) (hw : w ≫ q = s) (h : unit q L a s v w hv hw = 1) :
    nativePullFrame L q s v hv a = nativePullFrame L q s w hw a := by
  have ht : transition q L a s v w hv hw = Iso.refl _ :=
    (unitAutoEquiv V).injective (h.trans (unitOfIso_refl V).symm)
  apply Iso.ext
  have he := congrArg (fun e => (nativePullFrame L q s v hv a).hom ≫ e.hom) ht
  simpa only [transition, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id] using he.symm

open Invertible.EtaleDescent (ofLineBundle)
open Invertible.UnitDescent (unitObject)
open Pseudofunctor.LocallyDiscreteOpToCat

/-- Equal restrictions of a given morphism are the compatibility equation
of the same canonical singleton descent data. -/
theorem singletonDescentComm_of_pullHomEq
    {C : Type u'} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u''})
    {X Y : C} (f : X ⟶ Y) {M N : F.obj (.mk (op Y))}
    (b : (F.map f.op.toLoc).toFunctor.obj M ⟶ (F.map f.op.toLoc).toFunctor.obj N)
    (h : ∀ {W : C} (s : W ⟶ Y) (v w : W ⟶ X) (hv : v ≫ f = s) (hw : w ≫ f = s),
      pullHom b v s s hv hv = pullHom b w s s hw hw)
    {W : C} (s : W ⟶ Y) {i j : PUnit.{1}} (v w : W ⟶ X)
    (hv : v ≫ f = s) (hw : w ≫ f = s) :
    (F.map v.op.toLoc).toFunctor.map b ≫
        ((F.toDescentData (X := fun _ : PUnit.{1} => X) (fun _ : PUnit.{1} => f)).obj N).hom
          s (i₁ := i) (i₂ := j) v w hv hw =
      ((F.toDescentData (X := fun _ : PUnit.{1} => X) (fun _ : PUnit.{1} => f)).obj M).hom
          s (i₁ := i) (i₂ := j) v w hv hw ≫ (F.map w.op.toLoc).toFunctor.map b := by
  have hb : Presieve.Arrows.Compatible (F.presheafHom M N)
      (X := fun _ : PUnit.{1} => Over.mk f) (B := Over.mk (𝟙 Y))
      (fun _ => Over.homMk f) (fun _ => b) := by
    intro _ _ Z v w _
    exact h Z.hom v.left w.left (Over.w v) (Over.w w)
  let c := DescentData.subtypeCompatibleHomEquiv F
    (X := fun _ : PUnit.{1} => X) (fun _ : PUnit.{1} => f)
    (M := M) (N := N) ⟨fun _ => b, hb⟩
  exact c.comm s (i₁ := i) (i₂ := j) v w hv hw

/-- A frame with identity original transition on every overlap gives an
isomorphism of the two original native descent data. The native Hom
restriction is exactly restriction of the original frame. -/
def descentIsoOfUnitEqOne
    (h : ∀ {V : Scheme.{u}} (s : V ⟶ Y) (v w : V ⟶ X)
      (hv : v ≫ q = s) (hw : w ≫ q = s), unit q L a s v w hv hw = 1) :
    (lineBundlePseudofunctor.toDescentData (X := fun _ : PUnit.{1} => X)
      (fun _ : PUnit.{1} => q)).obj (ofLineBundle Y L) ≅
    (lineBundlePseudofunctor.toDescentData (X := fun _ : PUnit.{1} => X)
      (fun _ : PUnit.{1} => q)).obj (unitObject Y) := by
  let e : (lineBundlePseudofunctor.map q.op.toLoc).toFunctor.obj (ofLineBundle Y L) ≅
      (lineBundlePseudofunctor.map q.op.toLoc).toFunctor.obj (unitObject Y) :=
    ObjectProperty.isoMk _ (a ≪≫ (pullbackUnitIso q).symm)
  have h' : ∀ {W : Scheme.{u}} (s : W ⟶ Y) (v w : W ⟶ X)
      (hv : v ≫ q = s) (hw : w ≫ q = s),
      pullHom (rawOfFrame L q a) v s s hv hv = pullHom (rawOfFrame L q a) w s s hw hw := by
    intro W s v w hv hw
    exact (rawOfFrame_nativePullFrame L q s v hv a).symm.trans
      ((congrArg (rawOfFrame L s)
        (nativePullFrame_eq_of_unit_eq_one q L a s v w hv hw (h s v w hv hw))).trans
          (rawOfFrame_nativePullFrame L q s w hw a))
  refine DescentData.isoMk (fun _ : PUnit.{1} => e) ?_
  intro V s i j v w hv hw
  exact singletonDescentComm_of_pullHomEq lineBundlePseudofunctor q
    (rawOfFrame L q a) h' s (i := i) (j := j) v w hv hw

/-- Full faithfulness for the actual fppf singleton cover descends this
one frame as an isomorphism between the given original line bundle and
the original structure module. -/
def descendFrameIso
    (hf : Sieve.ofArrows (fun _ : PUnit.{1} => X) (fun _ : PUnit.{1} => q) ∈
      Scheme.fppfTopology Y)
    (h : ∀ {V : Scheme.{u}} (s : V ⟶ Y) (v w : V ⟶ X)
      (hv : v ≫ q = s) (hw : w ≫ q = s), unit q L a s v w hv hw = 1) :
    (L.val : Y.Modules) ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (CategoryTheory.ObjectProperty.ι _).mapIso
    (FppfSingle.liftIso q hf (descentIsoOfUnitEqOne q L a h))

end AlgebraicGeometry.Scheme.Modules.TrivializedDescent
