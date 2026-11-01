/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.EtaleTraceNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DirectImageEvaluationComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DirectImageEvaluationGerm
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SplitMapFiber

/-!
# Original canonical finite trace on geometric stalks

The original coefficient-natural germ maps transport the already normalized
local graph SUM to the original geometric stalk. Splitting neighborhoods are
cofinal by the actual point's covering-sieve axiom. All constructions keep the
existing represented trace and actual point and section functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MorphismProperty.Over

universe u uC vC uD vD

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge Fintype.ofFinite

section Interchange

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

private theorem germ_interchange (T : C ⥤ C) (S H : C ⥤ D)
    (γ : S ⟶ H) (τ : T ⟶ 𝟭 C) :
    Functor.whiskerLeft T γ ≫ Functor.whiskerRight τ H ≫ (Functor.leftUnitor H).hom =
      (Functor.whiskerRight τ S ≫ (Functor.leftUnitor S).hom) ≫ γ := by
  apply NatTrans.ext
  funext F
  dsimp
  simp only [Category.comp_id]
  exact (γ.naturality (τ.app F)).symm

end Interchange

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (η : Spec (.of Ω) ⟶ X)

/-- Original geometric germs, bundled naturally in the unchanged coefficient sheaf. -/
def geometricGermNatTrans (V : X.Etale) (v : (pointSmallEtale η).fiber.obj V) :
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V) ⟶
      (pointSmallEtale η).sheafFiber :=
  Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    ((pointSmallEtale η).toPresheafFiberNatTrans V v)

/-- The natural family retains the literal original germ, without a new stalk carrier. -/
@[simp] theorem geometricGermNatTrans_app (V : X.Etale)
    (v : (pointSmallEtale η).fiber.obj V) (F : AbelianSheaf.{u, u + 1} X) :
    (geometricGermNatTrans η V v).app F = (pointSmallEtale η).toPresheafFiber V v F.obj := rfl

variable (Y : Scheme.FiniteEtale X)

-- Use the original over-category presentation of the native Etale category.
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual splitting neighborhoods refine every pointed etale neighborhood.
The original point's covering-sieve axiom supplies the lift. -/
theorem exists_refining_finiteEtale_trace_chart (V : X.Etale)
    (v : (pointSmallEtale η).fiber.obj V) :
    ∃ (W : X.Etale) (g : W ⟶ V) (w : (pointSmallEtale η).fiber.obj W)
      (A : FintypeCat.{u})
      (_e : (Scheme.FiniteEtale.trivialCoverFunctor W.left).obj A ≅
        (Scheme.FiniteEtale.baseChange W.hom).obj Y),
      (pointSmallEtale η).fiber.map g w = v := by
  classical
  choose C A e c hc using Scheme.FiniteEtale.exists_labelled_chart Y
  let T : X.Etale := etaleTerminal X
  let hT : IsTerminal T := etaleTerminalIsTerminal X
  let p (x : X) : C x ⟶ T := hT.from (C x)
  have hp : Sieve.ofArrows C p ∈ X.smallEtaleTopology T := by
    apply Scheme.FiniteEtale.SheafDescent.etaleFamily_covering C p
    intro x
    refine ⟨x, c x, ?_⟩
    have hw := MorphismProperty.Over.w (p x)
    change (p x).left ≫ 𝟙 X = (C x).hom at hw
    have hw' : (p x).left = (C x).hom := (Category.comp_id (p x).left).symm.trans hw
    exact (congrArg (fun a : (C x).left ⟶ X => a (c x)) hw').trans (hc x)
  have hp' := X.smallEtaleTopology.pullback_stable (hT.from V) hp
  obtain ⟨W, g, hg, w, hw⟩ :=
    (pointSmallEtale η).jointly_surjective _ hp' v
  change Sieve.ofArrows C p (g ≫ hT.from V) at hg
  obtain ⟨i, a, _⟩ := Sieve.ofArrows.exists hg
  exact ⟨W, g, w, A i, Scheme.FiniteEtale.restrictChartSplitting Y a (e i), hw⟩

set_option backward.isDefEq.respectTransparency.types false in
private def traceChartFiberEquiv (V : X.Etale)
    (v : (pointSmallEtale η).fiber.obj V) (A : FintypeCat.{u})
    (e : (Scheme.FiniteEtale.trivialCoverFunctor V.left).obj A ≅
      (Scheme.FiniteEtale.baseChange V.hom).obj Y) :
    A ≃ Scheme.FiniteEtale.Fiber η Y :=
  (Scheme.FiniteEtale.trivialCoverFiberEquiv A v.left).trans
    (((Scheme.FiniteEtale.fiber v.left).mapIso e).toEquiv.trans
      ((Scheme.FiniteEtale.fiberBaseChangeEquiv V.hom v.left Y).symm.trans
        (Scheme.FiniteEtale.fiberPointCongrEquiv (Over.w v) Y)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem traceChartFiberEquiv_left (V : X.Etale)
    (v : (pointSmallEtale η).fiber.obj V) (A : FintypeCat.{u})
    (e : (Scheme.FiniteEtale.trivialCoverFunctor V.left).obj A ≅
      (Scheme.FiniteEtale.baseChange V.hom).obj Y) (a : A) :
    (traceChartFiberEquiv η Y V v A e a).left =
      v.left ≫ (Scheme.FiniteEtale.chartSiteSection Y e a).left := by
  unfold traceChartFiberEquiv
  erw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply,
    Scheme.FiniteEtale.fiberPointCongrEquiv_left,
    Scheme.FiniteEtale.fiberBaseChangeEquiv_symm_left]
  change ((v.left ≫ (Scheme.FiniteEtale.trivialCoverι V.left A a).hom.left) ≫
      e.hom.hom.left) ≫ pullback.fst Y.obj.hom V.hom =
    v.left ≫ (Scheme.FiniteEtale.trivialCoverι V.left A a).hom.left ≫
      e.hom.hom.left ≫ pullback.fst Y.obj.hom V.hom
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

variable (d : ℕ) (hd : ∀ x : X, Y.obj.hom.finrank x = d)

-- Form the original product graphs through the native Etale category alias.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The WHOLE canonical trace followed by original germs is the original
local graph SUM followed by those same germs, naturally in every coefficient. -/
theorem finiteEtaleSheafTrace_germ_local (V : X.Etale)
    (v : (pointSmallEtale η).fiber.obj V) (A : FintypeCat.{u})
    (e : (Scheme.FiniteEtale.trivialCoverFunctor V.left).obj A ≅
      (Scheme.FiniteEtale.baseChange V.hom).obj Y) :
    Functor.whiskerLeft (inverseImage Y.obj.hom ⋙ directImage Y.obj.hom)
        (geometricGermNatTrans η V v) ≫
      Functor.whiskerRight (finiteEtaleSheafTrace Y d hd)
        ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
      (Functor.leftUnitor ((pointSmallEtale η).sheafFiber
        (A := AddCommGrpCat.{u + 1}))).hom =
      (Functor.whiskerRight
          (Functor.whiskerRight (inverseImageEtaleIso Y.obj.hom).hom (directImage Y.obj.hom))
          ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V)) ≫
        ∑ a : A, (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (productGraph (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})
            (Scheme.FiniteEtale.chartSiteSection Y e a)).op) ≫ geometricGermNatTrans η V v := by
  have hsum := congrArg (fun a => a ≫ geometricGermNatTrans η V v)
    (finiteEtaleSheafTrace_local Y d hd V A e)
  exact (germ_interchange (inverseImage Y.obj.hom ⋙ directImage Y.obj.hom)
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V))
    ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}))
    (geometricGermNatTrans η V v) (finiteEtaleSheafTrace Y d hd)).trans hsum

section EtaleUnitGerms

open CoefficientStalkBaseChange

variable {S : Scheme.{u}} (f : S ⟶ X) [Etale f] (s : Spec (.of Ω) ⟶ S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original site unit carries the actual point of an etale test to the
original pulled-back point of its postcomposition. -/
theorem siteEtalePostcompose_pointed_unit (T : S.Etale)
    (t : (pointSmallEtale s).fiber.obj T) :
    (pointSmallEtale s).fiber.map ((siteEtalePostcomposeAdj f).unit.app T) t =
      pointedPulledBackPoint f s (s ≫ f) rfl ((siteEtalePostcompose f).obj T)
        ((CategoryTheory.Over.map f).map t) := by
  apply Over.OverMorphism.ext
  change t.left ≫ ((siteEtalePostcomposeAdj f).unit.app T).left = _
  rw [pointedPulledBackPoint_left]
  change t.left ≫
      pullback.lift (f := ((siteEtalePostcompose f).obj T).hom) (g := f)
        (𝟙 T.left) T.hom _ =
    pullback.lift (f := ((siteEtalePostcompose f).obj T).hom) (g := f) t.left s _
  apply pullback.hom_ext (f := ((siteEtalePostcompose f).obj T).hom) (g := f)
  · simp only [Category.assoc, pullback.lift_fst]
    exact Category.comp_id t.left
  · simp only [Category.assoc, pullback.lift_snd]
    simpa only [Scheme.Etale.forget_obj_hom, Over.mk_hom] using Over.w t

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The WHOLE original pointed inverse-image unit followed by the original
etale restriction comparison is normalized on postcomposed geometric germs. -/
theorem geometricGermNatTrans_etaleUnit (T : S.Etale)
    (t : (pointSmallEtale s).fiber.obj T) :
    geometricGermNatTrans (s ≫ f) ((siteEtalePostcompose f).obj T)
        ((CategoryTheory.Over.map f).map t) ≫
      (pointedStalkUnitNatIso f s (s ≫ f) rfl).hom ≫
      Functor.whiskerRight (inverseImageEtaleIso f).hom
        ((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})) =
      Functor.whiskerLeft (etaleRestriction f) (geometricGermNatTrans s T t) := by
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, geometricGermNatTrans_app,
    pointedStalkUnitNatIso_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  let U := (siteEtalePostcompose f).obj T
  let p := (CategoryTheory.Over.map f).map t
  let W := (siteBaseChange f).obj U
  let q := pointedPulledBackPoint f s (s ≫ f) rfl U p
  let M := (inverseImage f).obj F
  let N := (etaleRestriction f).obj F
  let i := (inverseImageEtaleIso f).hom.app F
  let a := ((inverseImageAdjunction f).unit.app F).hom.app (op U)
  let b := i.hom.app (op W)
  let u := pointedStalkUnit f s F (s ≫ f) rfl
  let c := (pointSmallEtale s).sheafFiber.map i
  let g₀ := (pointSmallEtale (s ≫ f)).toPresheafFiber U p F.obj
  let g₁ := (pointSmallEtale s).toPresheafFiber W q M.obj
  let g₂ := (pointSmallEtale s).toPresheafFiber W q N.obj
  let g₃ := (pointSmallEtale s).toPresheafFiber T t N.obj
  let j := (siteEtalePostcomposeAdj f).unit.app T
  let a₀ := F.obj.map ((siteEtalePostcomposeAdj f).counit.app U).op
  let b₀ := N.obj.map j.op
  have h₁ : g₀ ≫ u = a ≫ g₁ := germ_pointedStalkUnit f s F (s ≫ f) rfl U p
  have h₂ : g₁ ≫ c = b ≫ g₂ :=
    (pointSmallEtale s).toPresheafFiber_naturality i.hom W q
  have h₃ : a ≫ b = a₀ := inverseImageEtaleIso_unit_app f F U
  have h₄ : b₀ ≫ g₃ = g₂ := by
    have h := (pointSmallEtale s).toPresheafFiber_w j t N.obj
    have hq := siteEtalePostcompose_pointed_unit f s T t
    change (pointSmallEtale s).fiber.map j t = q at hq
    rw [hq] at h
    exact h
  have h₅ : a₀ ≫ b₀ = 𝟙 _ := by
    change F.obj.map ((siteEtalePostcomposeAdj f).counit.app U).op ≫
      F.obj.map ((siteEtalePostcompose f).map j).op = 𝟙 _
    rw [← F.obj.map_comp, ← op_comp,
      (siteEtalePostcomposeAdj f).left_triangle_components T]
    change F.obj.map (𝟙 (op U)) = 𝟙 _
    exact F.obj.map_id (op U)
  change g₀ ≫ u ≫ c = g₃
  calc
    g₀ ≫ u ≫ c = (a ≫ g₁) ≫ c := by rw [← Category.assoc, h₁]
    _ = (a ≫ b) ≫ g₂ := by rw [Category.assoc, h₂, ← Category.assoc]
    _ = a₀ ≫ (b₀ ≫ g₃) := by rw [h₃, ← h₄]
    _ = g₃ := by rw [← Category.assoc, h₅, Category.id_comp]

end EtaleUnitGerms

/-- The original whole germ family respects every original pointed refinement. -/
theorem geometricGermNatTrans_refine {V W : X.Etale} (a : V ⟶ W)
    (v : (pointSmallEtale η).fiber.obj V) :
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).map a.op ≫
        geometricGermNatTrans η V v =
      geometricGermNatTrans η W ((pointSmallEtale η).fiber.map a v) := by
  apply NatTrans.ext
  funext F
  exact (pointSmallEtale η).toPresheafFiber_w a v F.obj

section EvaluationGerms

variable {S : Scheme.{u}} (f : S ⟶ X) (s : Spec (.of Ω) ⟶ S)

/-- The whole original direct-image evaluation is the original germ at the
actual pulled-back point. No etaleness or finiteness is required. -/
theorem geometricGermNatTrans_directImageEvaluation (V : X.Etale)
    (v : (pointSmallEtale (s ≫ f)).fiber.obj V) :
    Functor.whiskerLeft (directImage f) (geometricGermNatTrans (s ≫ f) V v) ≫
        pointedDirectImageEvaluationNatTrans f s (s ≫ f) rfl =
      geometricGermNatTrans s ((siteBaseChange f).obj V)
        (CoefficientStalkBaseChange.pointedPulledBackPoint f s (s ≫ f) rfl V v) := by
  apply NatTrans.ext
  funext F
  exact Finite.germ_pointedDirectImageEvaluation f s (s ≫ f) rfl F V v

end EvaluationGerms

section GraphPoints

open CoefficientStalkBaseChange

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem productGraph_pointedPoint (U V : X.Etale)
    (s : Spec (.of Ω) ⟶ U.left)
    (v : (pointSmallEtale (s ≫ U.hom)).fiber.obj V)
    (a : V ⟶ U) (ha : v.left ≫ a.left = s) :
    (pointSmallEtale (s ≫ U.hom)).fiber.map
        (productGraph (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) a) v =
      (CategoryTheory.Over.map U.hom).map
        (pointedPulledBackPoint U.hom s (s ≫ U.hom) rfl V v) := by
  let P : MorphismProperty Scheme.{u} := @AlgebraicGeometry.Etale
  have h₁ := congrArg (fun k : V ⟶ V => k.left) (productGraph_fst P a)
  have h₂ := congrArg (fun k : V ⟶ U => k.left) (productGraph_snd P a)
  change (productGraph P a).left ≫ pullback.fst V.hom U.hom = 𝟙 V.left at h₁
  change (productGraph P a).left ≫ pullback.snd V.hom U.hom = a.left at h₂
  apply Over.OverMorphism.ext
  change v.left ≫ (productGraph P a).left =
    (pointedPulledBackPoint U.hom s (s ≫ U.hom) rfl V v).left
  rw [pointedPulledBackPoint_left]
  apply pullback.hom_ext (f := V.hom) (g := U.hom)
  · erw [Category.assoc, h₁, pullback.lift_fst]
    exact Category.comp_id v.left
  · erw [Category.assoc, h₂, pullback.lift_snd]
    exact ha

end GraphPoints

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original product-graph coordinate is the original pointed
direct-image evaluation followed by the inverse of the same pointed unit.
The equality is on the whole coefficient family. -/
theorem etaleProductGraph_evaluation (U V : X.Etale)
    (s : Spec (.of Ω) ⟶ U.left) (x : Spec (.of Ω) ⟶ X) (hs : s ≫ U.hom = x)
    (v : (pointSmallEtale x).fiber.obj V) (a : V ⟶ U) (ha : v.left ≫ a.left = s) :
    Functor.whiskerLeft (inverseImage (X := X) (S := U.left) U.hom ⋙
        directImage (X := X) (S := U.left) U.hom)
        (geometricGermNatTrans x V v) ≫
      (Functor.associator (inverseImage (X := X) (S := U.left) U.hom)
        (directImage (X := X) (S := U.left) U.hom)
        ((pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1}))).hom ≫
      Functor.whiskerLeft (inverseImage (X := X) (S := U.left) U.hom)
        (pointedDirectImageEvaluationNatTrans (X := X) (Y := U.left) U.hom s x hs) ≫
      (pointedStalkUnitNatIso (X := X) (Y := U.left) U.hom s x hs).inv =
      Functor.whiskerRight
          (Functor.whiskerRight (inverseImageEtaleIso (X := X) (S := U.left) U.hom).hom
            (directImage (X := X) (S := U.left) U.hom))
          ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V)) ≫
        (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (productGraph (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) a).op ≫
        geometricGermNatTrans x V v := by
  subst x
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp]
  let P : MorphismProperty Scheme.{u} := @AlgebraicGeometry.Etale
  let T := (siteBaseChange (X := X) (S := U.left) U.hom).obj V
  let q := CoefficientStalkBaseChange.pointedPulledBackPoint (X := X) (S := U.left)
    U.hom s (s ≫ U.hom) rfl V v
  let H := (pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  let e := (pointedStalkUnitNatIso (X := X) (Y := U.left) U.hom s (s ≫ U.hom) rfl).app F
  let j := (inverseImageEtaleIso (X := X) (S := U.left) U.hom).app F
  let b := j.hom.hom.app (op T)
  let h := F.obj.map (productGraph P a).op
  let k := (geometricGermNatTrans (X := X) (s ≫ U.hom) V v).app F
  let g₀ := (geometricGermNatTrans (X := X) (s ≫ U.hom) V v).app
    ((directImage (X := X) (S := U.left) U.hom).obj
      ((inverseImage (X := X) (S := U.left) U.hom).obj F))
  let g₁ := (geometricGermNatTrans s T q).app ((inverseImage (X := X) (S := U.left) U.hom).obj F)
  let g₂ := (geometricGermNatTrans s T q).app ((etaleRestriction U.hom).obj F)
  let ev := pointedDirectImageEvaluation (X := U.left) (S := X) U.hom s (s ≫ U.hom) rfl
    ((inverseImage (X := X) (S := U.left) U.hom).obj F)
  have hE : g₀ ≫ ev = g₁ := NatTrans.congr_app
    (geometricGermNatTrans_directImageEvaluation (X := X) (S := U.left) U.hom s V v)
    ((inverseImage (X := X) (S := U.left) U.hom).obj F)
  have hn : b ≫ g₂ = g₁ ≫ H.map j.hom :=
    (geometricGermNatTrans s T q).naturality j.hom
  have hp := productGraph_pointedPoint (X := X) U V s v a ha
  have hg := NatTrans.congr_app
    (geometricGermNatTrans_refine (X := X) (s ≫ U.hom) (productGraph P a) v) F
  erw [hp] at hg
  have hu := NatTrans.congr_app
    (geometricGermNatTrans_etaleUnit (X := X) (S := U.left) U.hom s T q) F
  change (geometricGermNatTrans (X := X) (s ≫ U.hom)
    ((siteEtalePostcompose (X := X) (S := U.left) U.hom).obj T)
    ((CategoryTheory.Over.map U.hom).map q)).app F ≫ e.hom ≫ H.map j.hom = g₂ at hu
  have hlocal : h ≫ k ≫ e.hom ≫ H.map j.hom = g₂ := by
    have hmap := congrArg (fun z => z ≫ e.hom ≫ H.map j.hom) hg
    simp only [NatTrans.comp_app, Category.assoc] at hmap
    change h ≫ k ≫ e.hom ≫ H.map j.hom = _ at hmap
    exact hmap.trans hu
  change g₀ ≫ ev ≫ e.inv = b ≫ h ≫ k
  apply (cancel_mono (e.hom ≫ H.map j.hom)).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [← Category.assoc g₀ ev, hE, hlocal]
  exact hn.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The WHOLE original canonical finite-etale trace on a geometric stalk is
the sum of the original pointed evaluations and inverse pointed units. The
actual cover fibre is the index set, including the empty fibre. -/
theorem finiteEtaleSheafTrace_stalk :
    Functor.whiskerRight (finiteEtaleSheafTrace Y d hd)
        ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
      (Functor.leftUnitor ((pointSmallEtale η).sheafFiber
        (A := AddCommGrpCat.{u + 1}))).hom =
      ∑ s : Scheme.FiniteEtale.Fiber η Y,
        (Functor.associator (inverseImage Y.obj.hom) (directImage Y.obj.hom)
          ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}))).hom ≫
        Functor.whiskerLeft (inverseImage Y.obj.hom)
          (pointedDirectImageEvaluationNatTrans Y.obj.hom s.left η (Over.w s)) ≫
        (pointedStalkUnitNatIso Y.obj.hom s.left η (Over.w s)).inv := by
  classical
  let T := inverseImage Y.obj.hom ⋙ directImage Y.obj.hom
  let H := (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let τ : T ⋙ H ⟶ H := Functor.whiskerRight (finiteEtaleSheafTrace Y d hd) H ≫
    (Functor.leftUnitor H).hom
  let b (s : Scheme.FiniteEtale.Fiber η Y) : T ⋙ H ⟶ H :=
    (Functor.associator (inverseImage Y.obj.hom) (directImage Y.obj.hom) H).hom ≫
      Functor.whiskerLeft (inverseImage Y.obj.hom)
        (pointedDirectImageEvaluationNatTrans Y.obj.hom s.left η (Over.w s)) ≫
      (pointedStalkUnitNatIso Y.obj.hom s.left η (Over.w s)).inv
  have hlocal (V : X.Etale) (v : (pointSmallEtale η).fiber.obj V) (A : FintypeCat.{u})
      (e : (Scheme.FiniteEtale.trivialCoverFunctor V.left).obj A ≅
        (Scheme.FiniteEtale.baseChange V.hom).obj Y) :
      Functor.whiskerLeft T (geometricGermNatTrans η V v) ≫ τ =
        Functor.whiskerLeft T (geometricGermNatTrans η V v) ≫ ∑ s, b s := by
    let E := traceChartFiberEquiv η Y V v A e
    let p := Functor.whiskerRight
      (Functor.whiskerRight (inverseImageEtaleIso Y.obj.hom).hom (directImage Y.obj.hom))
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op V))
    let g (a : A) := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (productGraph (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})
        (Scheme.FiniteEtale.chartSiteSection Y e a)).op
    calc
      _ = (p ≫ ∑ a, g a) ≫ geometricGermNatTrans η V v :=
        finiteEtaleSheafTrace_germ_local η Y d hd V v A e
      _ = ∑ a, p ≫ g a ≫ geometricGermNatTrans η V v := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = ∑ a : A, Functor.whiskerLeft T (geometricGermNatTrans η V v) ≫ b (E a) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (etaleProductGraph_evaluation ((Scheme.FiniteEtale.toEtale X).obj Y) V
          (E a).left η (Over.w (E a)) v (Scheme.FiniteEtale.chartSiteSection Y e a)
          (traceChartFiberEquiv_left η Y V v A e a).symm).symm
      _ = ∑ s, Functor.whiskerLeft T (geometricGermNatTrans η V v) ≫ b s :=
        E.sum_comp (fun s => Functor.whiskerLeft T (geometricGermNatTrans η V v) ≫ b s)
      _ = _ := by rw [Preadditive.comp_sum]
  change τ = ∑ s, b s
  apply NatTrans.ext
  funext F
  apply (pointSmallEtale η).presheafFiber_hom_ext
  intro V v
  obtain ⟨W, g, w, A, e, hw⟩ := exists_refining_finiteEtale_trace_chart η Y V v
  have hg := (pointSmallEtale η).toPresheafFiber_w g w (T.obj F).obj
  rw [hw] at hg
  have hl := NatTrans.congr_app (hlocal W w A e) F
  change (pointSmallEtale η).toPresheafFiber W w (T.obj F).obj ≫ τ.app F =
    (pointSmallEtale η).toPresheafFiber W w (T.obj F).obj ≫ (∑ s, b s).app F at hl
  exact (congrArg (fun a => a ≫ τ.app F) hg.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => (T.obj F).obj.map g.op ≫ a) hl).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun a => a ≫ (∑ s, b s).app F) hg))))

end AlgebraicGeometry.Scheme.EtaleCohomology
