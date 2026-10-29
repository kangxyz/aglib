/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Actual local sections trivialize the same torsor on a slice

Restriction uses the native `Sheaf.over` carrier and the original action.
A section at the slice base gives a genuine global point of this restricted
torsor, so the existing global-point trivialization applies. Whiskering along
the actual test arrows gives the chart isomorphism. Its components are exactly
the original `sectionEquiv` at the restricted original section.

The constant-chart constructor retains the supplied inverse-image/restriction
comparisons and the native constant/forgetful comparison. Finiteness is separate.
Site object, morphism and sheaf-value universes are independent. No global
nonemptiness or sheafification premise is used for the slice trivialization.
The actual small-etale finite-torsor charts are the current consumer.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.Torsor

universe uC vC uD vD w

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  {L : Sheaf J AddCommGrpCat.{w}} (P : Torsor L)

/-- Restrict the same carrier and action to the native over-site. -/
def over (U : C) : Torsor (L.over U) where
  carrier := P.carrier.over U
  action V := P.action ((Over.forget U).op.obj V)
  zero_action V := P.zero_action ((Over.forget U).op.obj V)
  add_action V := P.add_action ((Over.forget U).op.obj V)
  naturality f := P.naturality ((Over.forget U).op.map f)
  unique_transport V := P.unique_transport ((Over.forget U).op.obj V)
  locally_nonempty V := by
    change (Sieve.overEquiv V).symm (nonemptySieve P.carrier V.left) ∈ (J.over U) V
    exact J.overEquiv_symm_mem_over V _ (P.locally_nonempty V.left)

/-- The slice carrier is literally the original native sheaf restriction. -/
theorem over_carrier (U : C) : (P.over U).carrier = P.carrier.over U := rfl

/-- The slice action is the original sectionwise action on the same values. -/
theorem over_action (U : C) (V : (Over U)ᵒᵖ) (a : (L.over U).obj.obj V)
    (t : (P.over U).carrier.obj.obj V) :
    (P.over U).action V a t = P.action ((Over.forget U).op.obj V) a t := rfl

/-- Restrict the given actual section along the original arrow of a slice test object. -/
def restrictOverSection (U : C) (s : P.carrier.obj.obj (op U)) (V : (Over U)ᵒᵖ) :
    (P.over U).carrier.obj.obj V :=
  P.carrier.obj.map V.unop.hom.op s

/-- Original section restriction is natural on the slice. -/
theorem restrictOverSection_naturality (U : C) (s : P.carrier.obj.obj (op U))
    {V W : (Over U)ᵒᵖ} (f : V ⟶ W) :
    (P.over U).carrier.obj.map f (P.restrictOverSection U s V) =
      P.restrictOverSection U s W := by
  change P.carrier.obj.map ((Over.forget U).op.map f)
    (P.carrier.obj.map V.unop.hom.op s) = P.carrier.obj.map W.unop.hom.op s
  calc
    _ = P.carrier.obj.map (V.unop.hom.op ≫ (Over.forget U).op.map f) s :=
      (P.carrier.obj.map_comp_apply _ _ s).symm
    _ = _ := congrArg (fun a => P.carrier.obj.map a s)
      (congrArg Quiver.Hom.op (Over.w f.unop))

/-- A local section gives a genuine global point only after restriction to its slice. -/
def overSectionPoint (U : C) (s : P.carrier.obj.obj (op U)) :
    Topos.GlobalPoint (P.over U).carrier where
  hom.app V := ↾fun _ => P.restrictOverSection U s V
  hom.naturality {V W} f := by
    ext t
    exact (P.restrictOverSection_naturality U s f).symm

/-- The slice point is exactly the original restricted section at every test object. -/
@[simp]
theorem overSectionPoint_app (U : C) (s : P.carrier.obj.obj (op U)) (V : (Over U)ᵒᵖ) :
    (P.overSectionPoint U s).hom.app V PUnit.unit = P.restrictOverSection U s V := rfl

/-- Apply the existing global-point trivialization to the same restricted torsor. -/
def overTrivialization (U : C) (s : P.carrier.obj.obj (op U)) :
    Iso (trivialTorsor (L.over U)) (P.over U) :=
  (P.over U).trivializationOfGlobalPoint (P.overSectionPoint U s)

/-- The complete slice trivialization retains the original action component. -/
@[simp]
theorem overTrivialization_hom_app (U : C) (s : P.carrier.obj.obj (op U))
    (V : (Over U)ᵒᵖ) (a : L.obj.obj ((Over.forget U).op.obj V)) :
    (P.overTrivialization U s).carrierIso.hom.hom.app V a =
      P.action ((Over.forget U).op.obj V) a (P.restrictOverSection U s V) :=
  (P.over U).trivializationOfGlobalPoint_hom_app (P.overSectionPoint U s) V a

/-- Its inverse is the same unique section transport, without another inverse choice. -/
@[simp]
theorem overTrivialization_inv_app (U : C) (s : P.carrier.obj.obj (op U))
    (V : (Over U)ᵒᵖ) (t : (P.over U).carrier.obj.obj V) :
    (show L.obj.obj ((Over.forget U).op.obj V) from
      (P.overTrivialization U s).carrierIso.inv.hom.app V t) =
      (P.sectionEquiv ((Over.forget U).op.obj V) (P.restrictOverSection U s V)).symm t :=
  (P.over U).trivializationOfGlobalPoint_inv_app (P.overSectionPoint U s) V t

section Chart

variable {D : Type uD} [Category.{vD} D] {K : GrothendieckTopology D}
  (F : D ⥤ C) [F.IsContinuous K J] (U : C)
  (k : ∀ V : D, F.obj V ⟶ U)
  (hk : ∀ {V W : D} (f : V ⟶ W), F.map f ≫ k W = k V)
  (s : P.carrier.obj.obj (op U))

/-- Restrict the actual section along the supplied original chart test arrow. -/
def restrictChartSection (V : Dᵒᵖ) : P.carrier.obj.obj (F.op.obj V) :=
  P.carrier.obj.map (k V.unop).op s

/-- Whisker the existing slice trivialization along the actual chart test functor. -/
def chartTrivialization :
    underlyingSetSheaf ((F.sheafPushforwardContinuous AddCommGrpCat.{w} K J).obj L) ≅
      (F.sheafPushforwardContinuous (Type w) K J).obj P.carrier :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerLeft (F.toOver U k hk).op
    ((sheafToPresheaf (J.over U) (Type w)).mapIso
      (P.overTrivialization U s).carrierIso))

/-- Every chart component is the original action at the restricted original section. -/
@[simp]
theorem chartTrivialization_hom_app (V : Dᵒᵖ) (a : L.obj.obj (F.op.obj V)) :
    (P.chartTrivialization (K := K) F U k hk s).hom.hom.app V a =
      P.action (F.op.obj V) a (P.restrictChartSection F U k s V) :=
  P.overTrivialization_hom_app U s ((F.toOver U k hk).op.obj V) a

/-- The entire component is exactly the original section equivalence. -/
theorem chartTrivialization_app (V : Dᵒᵖ) :
    ((sheafToPresheaf K (Type w)).mapIso
      (P.chartTrivialization (K := K) F U k hk s)).app V =
        (P.sectionEquiv (F.op.obj V) (P.restrictChartSection F U k s V)).toIso := by
  apply CategoryTheory.Iso.ext
  ext a
  exact P.chartTrivialization_hom_app (K := K) F U k hk s V a

variable [HasWeakSheafify K AddCommGrpCat.{w}] [HasWeakSheafify K (Type w)]
  [K.PreservesSheafification (forget AddCommGrpCat.{w})]

/-- The full constant chart uses the same values and the actual supplied restriction
comparisons. It requires no finiteness or global-section assumption. -/
def constantChartIso (A : AddCommGrpCat.{w})
    {Q : Sheaf K (Type w)}
    (rP : Q ≅ (F.sheafPushforwardContinuous (Type w) K J).obj P.carrier)
    {M : Sheaf K AddCommGrpCat.{w}}
    (rL : M ≅ (F.sheafPushforwardContinuous AddCommGrpCat.{w} K J).obj L)
    (e : M ≅ (constantSheaf K AddCommGrpCat.{w}).obj A) :
    Q ≅ (constantSheaf K (Type w)).obj A :=
  rP ≪≫ (P.chartTrivialization (K := K) F U k hk s).symm ≪≫
    (sheafCompose K (forget AddCommGrpCat.{w})).mapIso (rL.symm ≪≫ e) ≪≫
    (constantCommuteCompose K (forget AddCommGrpCat.{w})).app A

end Chart

end CategoryTheory.Sheaf.Torsor
