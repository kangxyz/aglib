/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# The original inverse-image unit on geometric stalks

The native point colimit descends the actual sheaf adjunction unit on germs.
The point, map, and identity/composition transports are the original ones.
No coefficient representation is needed for these constructions or their coherence.

These proofs are split from `H1.CoefficientStalkBaseChange`; their public names
and actual maps are retained, with the native sheaf fibre written directly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.CoefficientStalkBaseChange

universe u
attribute [local instance] hasSheafifyLarge
variable {X S : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
variable (f : S ⟶ X) (s : Spec (CommRingCat.of K) ⟶ S)

/-- The actual pulled-back point of a small-etale test object. -/
def pulledBackPoint (U : X.Etale) (p : Over.mk (s ≫ f) ⟶ (Scheme.Etale.forget X).obj U) :
    Over.mk s ⟶ (Scheme.Etale.forget S).obj ((siteBaseChange f).obj U) :=
  (Over.mapPullbackAdj f).homEquiv (Over.mk s) ((Scheme.Etale.forget X).obj U) p

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- Its naturality is the actual Over pullback adjunction's right naturality. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem pulledBackPoint_naturality {U V : X.Etale} (g : U ⟶ V)
    (p : Over.mk (s ≫ f) ⟶ (Scheme.Etale.forget X).obj U) :
    pulledBackPoint f s V (p ≫ (Scheme.Etale.forget X).map g) =
      pulledBackPoint f s U p ≫ (Scheme.Etale.forget S).map ((siteBaseChange f).map g) := by
  change (Over.mapPullbackAdj f).homEquiv (Over.mk s) ((Scheme.Etale.forget X).obj V)
      (p ≫ (Scheme.Etale.forget X).map g) =
    (Over.mapPullbackAdj f).homEquiv (Over.mk s) ((Scheme.Etale.forget X).obj U) p ≫
      (Over.pullback f).map ((Scheme.Etale.forget X).map g)
  exact (Over.mapPullbackAdj f).homEquiv_naturality_right (X := Over.mk s) p
    ((Scheme.Etale.forget X).map g)

variable (L : AbelianSheaf.{u, u + 1} X)

/-- The canonical original-stalk to inverse-image-stalk map, defined on germs
using the genuine sheaf adjunction unit and the pulled-back test point. -/
def stalkUnit :
    ((Scheme.pointSmallEtale (s ≫ f)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj L ⟶
      ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((inverseImage f).obj L) :=
  (Scheme.pointSmallEtale (s ≫ f)).presheafFiberDesc
    (fun U p => ((inverseImageAdjunction f).unit.app L).hom.app (op U) ≫
      (Scheme.pointSmallEtale s).toPresheafFiber ((siteBaseChange f).obj U)
        (pulledBackPoint f s U p) ((inverseImage f).obj L).obj)
    (by
      intro U V g p
      change L.obj.map g.op ≫ (((inverseImageAdjunction f).unit.app L).hom.app (op U) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber ((siteBaseChange f).obj U)
          (pulledBackPoint f s U p) ((inverseImage f).obj L).obj) = _
      rw [← Category.assoc]
      erw [((inverseImageAdjunction f).unit.app L).hom.naturality g.op]
      rw [Category.assoc]
      erw [(Scheme.pointSmallEtale s).toPresheafFiber_w]
      congr 1
      exact congrArg (fun p => (Scheme.pointSmallEtale s).toPresheafFiber
        ((siteBaseChange f).obj V) p ((inverseImage f).obj L).obj)
        (pulledBackPoint_naturality f s g p).symm)

/-- The germ formula for the actual canonical stalk map. -/
@[reassoc] theorem germ_stalkUnit (U : X.Etale)
    (p : Over.mk (s ≫ f) ⟶ (Scheme.Etale.forget X).obj U) :
    (Scheme.pointSmallEtale (s ≫ f)).toPresheafFiber U p L.obj ≫ stalkUnit f s L =
      ((inverseImageAdjunction f).unit.app L).hom.app (op U) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber ((siteBaseChange f).obj U)
          (pulledBackPoint f s U p) ((inverseImage f).obj L).obj :=
  (Scheme.pointSmallEtale (s ≫ f)).toPresheafFiber_presheafFiberDesc _ _ U p

/-- Naturality of the canonical stalk map for every actual additive coefficient map. -/
@[reassoc] theorem stalkUnit_naturality {N : AbelianSheaf.{u, u + 1} X} (q : L ⟶ N) :
    ((Scheme.pointSmallEtale (s ≫ f)).sheafFiber (A := AddCommGrpCat.{u + 1})).map q ≫
        stalkUnit f s N =
      stalkUnit f s L ≫ ((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map ((inverseImage f).map q) := by
  apply (Scheme.pointSmallEtale (s ≫ f)).presheafFiber_hom_ext
  intro U p
  rw [← Category.assoc]
  erw [(Scheme.pointSmallEtale (s ≫ f)).toPresheafFiber_naturality q.hom]
  rw [Category.assoc]
  erw [germ_stalkUnit, germ_stalkUnit_assoc]
  erw [(Scheme.pointSmallEtale s).toPresheafFiber_naturality]
  have h := congrArg (fun r => r.hom.app (op U)) ((inverseImageAdjunction f).unit.naturality q)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun r => r ≫ (Scheme.pointSmallEtale s).toPresheafFiber
      ((siteBaseChange f).obj U) (pulledBackPoint f s U p) ((inverseImage f).obj N).obj) h).trans
        (Category.assoc _ _ _))

section Pointed
variable (x : Spec (CommRingCat.of K) ⟶ X) (hx : s ≫ f = x)

/-- Point-preserving pullback retains the actual basepoint equality. -/
def pointedPulledBackPoint (U : X.Etale)
    (p : Over.mk x ⟶ (Scheme.Etale.forget X).obj U) :
    Over.mk s ⟶ (Scheme.Etale.forget S).obj ((siteBaseChange f).obj U) := by
  subst x
  exact pulledBackPoint f s U p

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- On schemes the pointed comparison is the actual pullback lift. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem pointedPulledBackPoint_left (U : X.Etale)
    (p : Over.mk x ⟶ (Scheme.Etale.forget X).obj U) :
    (pointedPulledBackPoint f s x hx U p).left =
      pullback.lift p.left s ((Over.w p).trans hx.symm) := by
  subst x
  simp only [pointedPulledBackPoint, pulledBackPoint,
    Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The canonical lifted point projects to the original section-point map. -/
@[reassoc] theorem pointedPulledBackPoint_fst (U : X.Etale)
    (p : Over.mk x ⟶ (Scheme.Etale.forget X).obj U) :
    (pointedPulledBackPoint f s x hx U p).left ≫ pullback.fst U.hom f = p.left := by
  rw [pointedPulledBackPoint_left]
  exact pullback.lift_fst _ _ _

/-- The actual germ-unit stalk map for a pointed scheme morphism. -/
def pointedStalkUnit :
    ((Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).obj L ⟶
      ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((inverseImage f).obj L) := by
  subst x
  exact stalkUnit f s L

/-- The pointed germ formula retains the actual unit and test point. -/
@[reassoc] theorem germ_pointedStalkUnit (U : X.Etale)
    (p : Over.mk x ⟶ (Scheme.Etale.forget X).obj U) :
    (Scheme.pointSmallEtale x).toPresheafFiber U p L.obj ≫ pointedStalkUnit f s L x hx =
      ((inverseImageAdjunction f).unit.app L).hom.app (op U) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber ((siteBaseChange f).obj U)
          (pointedPulledBackPoint f s x hx U p) ((inverseImage f).obj L).obj := by
  subst x
  exact germ_stalkUnit f s L U p

end Pointed

section UnitCoherence

/-- The fixed inverse-image identity isomorphism has the unit of the actual
right-adjoint identity identification; this fixes its action on all sections. -/
theorem inverseImageId_unit (X : Scheme.{u}) (L : AbelianSheaf.{u, u + 1} X) (U : X.Etale) :
    ((inverseImageAdjunction (𝟙 X)).unit.app L).hom.app (op U) ≫
        ((inverseImageId X).hom.app L).hom.app (op ((siteBaseChange (𝟙 X)).obj U)) =
      L.obj.map ((siteBaseChangeId X).hom.app U).op := by
  let adj := inverseImageAdjunction (𝟙 X)
  let e := Functor.sheafPushforwardContinuousId' (siteBaseChangeId X)
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj.ofNatIsoRight e) (Adjunction.id (C := AbelianSheaf.{u, u + 1} X)) L
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have hh : adj.homEquiv _ _ ((inverseImageId X).hom.app L) = e.inv.app L := by
    apply (cancel_mono (e.hom.app L)).mp
    exact h.trans (e.inv_hom_id_app L).symm
  exact congrArg (fun q => q.hom.app (op U)) hh

/-- The fixed inverse-image composition is the actual mate of test-scheme
pullback composition, expressed on every section through the real units. -/
theorem inverseImageComp_unit {T : Scheme.{u}} (g : T ⟶ S) (U : X.Etale) :
    ((inverseImageAdjunction (g ≫ f)).unit.app L).hom.app (op U) ≫
        ((inverseImageComp f g).hom.app L).hom.app (op ((siteBaseChange (g ≫ f)).obj U)) =
      ((inverseImageAdjunction f).unit.app L).hom.app (op U) ≫
        ((inverseImageAdjunction g).unit.app ((inverseImage f).obj L)).hom.app
          (op ((siteBaseChange f).obj U)) ≫
        ((inverseImage g).obj ((inverseImage f).obj L)).obj.map
          ((siteBaseChangeComp f g).hom.app U).op := by
  have h := unit_conjugateEquiv
    ((inverseImageAdjunction f).comp (inverseImageAdjunction g))
    (inverseImageAdjunction (g ≫ f)) (inverseImageComp f g).hom L
  have hc : conjugateEquiv ((inverseImageAdjunction f).comp (inverseImageAdjunction g))
      (inverseImageAdjunction (g ≫ f)) (inverseImageComp f g).hom =
        (directImageCompIso f g).hom :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv
      (inverseImageAdjunction f) (inverseImageAdjunction g)
      (inverseImageAdjunction (g ≫ f)) (directImageCompIso f g)
  rw [hc, Adjunction.comp_unit_app] at h
  exact (congrArg (fun q => q.hom.app (op U)) h).symm

end UnitCoherence

section PointedCoherence

/-- The identity test-object comparison carries the canonical lifted point back
exactly to the original point. -/
theorem pointedPulledBackPoint_id {X : Scheme.{u}}
    (s : Spec (CommRingCat.of K) ⟶ X) (U : X.Etale)
    (p : Over.mk s ⟶ (Scheme.Etale.forget X).obj U) :
    pointedPulledBackPoint (𝟙 X) s s (Category.comp_id s) U p ≫
        (Scheme.Etale.forget X).map ((siteBaseChangeId X).hom.app U) = p := by
  apply Over.OverMorphism.ext
  exact pointedPulledBackPoint_fst (𝟙 X) s s (Category.comp_id s) U p

/-- Canonical identity coherence on actual stalks, proved on real germs. -/
theorem pointedStalkUnit_id {X : Scheme.{u}}
    (s : Spec (CommRingCat.of K) ⟶ X) (L : AbelianSheaf.{u, u + 1} X) :
    pointedStalkUnit (𝟙 X) s L s (Category.comp_id s) ≫
        ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          ((inverseImageId X).hom.app L) = 𝟙 (((Scheme.pointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj L) := by
  apply (Scheme.pointSmallEtale s).presheafFiber_hom_ext
  intro U p
  erw [germ_pointedStalkUnit_assoc]
  erw [(Scheme.pointSmallEtale s).toPresheafFiber_naturality]
  rw [← Category.assoc]
  erw [inverseImageId_unit]
  erw [(Scheme.pointSmallEtale s).toPresheafFiber_w]
  erw [Category.comp_id]
  change (Scheme.pointSmallEtale s).toPresheafFiber U
    (pointedPulledBackPoint (𝟙 X) s s (Category.comp_id s) U p ≫
      (Scheme.Etale.forget X).map ((siteBaseChangeId X).hom.app U)) L.obj = _
  rw [pointedPulledBackPoint_id]
  rfl

/-- Equality of scheme arrows acts by the exact corresponding coefficient
identification on the canonical pointed germ-unit maps. -/
theorem pointedStalkUnit_congr {g : S ⟶ X} (h : f = g)
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : s ≫ f = x) (hy : s ≫ g = x) :
    pointedStalkUnit f s L x hx ≫
        ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          (eqToHom (congrArg (fun k : S ⟶ X => (inverseImage k).obj L) h)) =
      pointedStalkUnit g s L x hy := by
  subst g
  have hi := ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map_id
    ((inverseImage f).obj L)
  change pointedStalkUnit f s L x hx ≫
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map (𝟙 _) = _
  rw [hi, Category.comp_id]

/-- Iterated pullback and direct composite pullback give the same actual test
point under the fixed site composition isomorphism. -/
theorem pointedPulledBackPoint_comp {T : Scheme.{u}} (g : T ⟶ S)
    (t : Spec (CommRingCat.of K) ⟶ T) (x : Spec (CommRingCat.of K) ⟶ X)
    (hy : t ≫ g = s) (hx : s ≫ f = x) (U : X.Etale)
    (p : Over.mk x ⟶ (Scheme.Etale.forget X).obj U) :
    pointedPulledBackPoint (g ≫ f) t x (by rw [← Category.assoc, hy, hx]) U p ≫
        (Scheme.Etale.forget T).map ((siteBaseChangeComp f g).hom.app U) =
      pointedPulledBackPoint g t s hy ((siteBaseChange f).obj U)
        (pointedPulledBackPoint f s x hx U p) := by
  apply Over.OverMorphism.ext
  change (pointedPulledBackPoint (g ≫ f) t x (by rw [← Category.assoc, hy, hx]) U p).left ≫
    ((siteBaseChangeComp f g).hom.app U).left = _
  simp only [pointedPulledBackPoint_left, siteBaseChangeComp,
    MorphismProperty.Over.pullbackComp_hom_app_left]
  simp only [Over.mk_left, Functor.comp_obj, MorphismProperty.Over.pullback_obj_left,
    MorphismProperty.Over.pullback_obj_hom, Etale.forget_obj_left, Etale.forget_obj_hom,
    pullback.map_id, Category.id_comp]
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [Category.assoc, hy]
  · simp [Category.assoc]

/-- The canonical pointed stalk map composes with the fixed inverse-image
composition isomorphism, as proved from adjunction units and actual test points. -/
theorem pointedStalkUnit_comp {T : Scheme.{u}} (g : T ⟶ S)
    (t : Spec (CommRingCat.of K) ⟶ T) (x : Spec (CommRingCat.of K) ⟶ X)
    (hy : t ≫ g = s) (hx : s ≫ f = x) :
    pointedStalkUnit (g ≫ f) t L x (by rw [← Category.assoc, hy, hx]) ≫
        ((Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          ((inverseImageComp f g).hom.app L) =
      pointedStalkUnit f s L x hx ≫ pointedStalkUnit g t ((inverseImage f).obj L) s hy := by
  apply (Scheme.pointSmallEtale x).presheafFiber_hom_ext
  intro U p
  erw [germ_pointedStalkUnit_assoc (g ≫ f) t L x (by rw [← Category.assoc, hy, hx]) U p,
    germ_pointedStalkUnit_assoc f s L x hx U p]
  erw [(Scheme.pointSmallEtale t).toPresheafFiber_naturality]
  rw [← Category.assoc]
  erw [inverseImageComp_unit f L g U]
  rw [Category.assoc, Category.assoc]
  erw [(Scheme.pointSmallEtale t).toPresheafFiber_w, germ_pointedStalkUnit]
  congr 2
  exact congrArg (fun p => (Scheme.pointSmallEtale t).toPresheafFiber
    ((siteBaseChange g).obj ((siteBaseChange f).obj U)) p
      ((inverseImage g).obj ((inverseImage f).obj L)).obj)
    (pointedPulledBackPoint_comp f s g t x hy hx U p)

end PointedCoherence

section SectionIdentity
variable {B X : Scheme.{u}} (b : Spec (CommRingCat.of K) ⟶ B)
variable (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
variable (L : AbelianSheaf.{u, u + 1} B)

/-- The canonical section coefficient identification is the identity on germs
after the two actual unit maps. This fixes its stalk marking without any H¹ premise. -/
theorem section_stalkUnit :
    pointedStalkUnit p (b ≫ o) L b (by simp [Category.assoc, h]) ≫
      pointedStalkUnit o b ((inverseImage p).obj L) (b ≫ o) rfl ≫
      ((Scheme.pointSmallEtale b).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((inverseImageComp p o).inv.app L ≫
          eqToHom (congrArg (fun k : B ⟶ B => (inverseImage k).obj L) h) ≫
          (inverseImageId B).hom.app L) = 𝟙 (((Scheme.pointSmallEtale b).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj L) := by
  let F := (Scheme.pointSmallEtale b).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hx : (b ≫ o) ≫ p = b := by simp [Category.assoc, h]
  have hz : b ≫ (o ≫ p) = b := by simp [h]
  have hc := pointedStalkUnit_comp p (b ≫ o) L o b b rfl hx
  change pointedStalkUnit (o ≫ p) b L b hz ≫ F.map ((inverseImageComp p o).hom.app L) =
    pointedStalkUnit p (b ≫ o) L b hx ≫
      pointedStalkUnit o b ((inverseImage p).obj L) (b ≫ o) rfl at hc
  rw [← Category.assoc, ← hc, Category.assoc, ← F.map_comp]
  rw [(inverseImageComp p o).hom_inv_id_app_assoc]
  rw [F.map_comp, ← Category.assoc,
    pointedStalkUnit_congr (o ≫ p) b L h b hz (Category.comp_id b)]
  exact pointedStalkUnit_id b L

end SectionIdentity

end AlgebraicGeometry.Scheme.EtaleCohomology.CoefficientStalkBaseChange
