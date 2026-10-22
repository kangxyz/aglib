/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoverSystemModules
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.RestrictionTransitions

/-!
# Actual restrictions of a global cover are its original coherent completion

Both the objectwise comparison and its naturality are fixed by the original
quotient units. The resulting isomorphism uses the original cover transitions.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

/-- Original epimorphic units turn a family of whole comparison packets into
one natural-isomorphism packet, without changing any diagram map. -/
def natIsoOfOriginalUnitData {I D : Type*} [Category I] [Category D]
    {F G : I ⥤ D} {M : D} (u : (Functor.const I).obj M ⟶ F)
    (v : (Functor.const I).obj M ⟶ G) [∀ i, Epi (u.app i)]
    (d : ∀ i, {e : F.obj i ≅ G.obj i // u.app i ≫ e.hom = v.app i}) :
    {e : F ≅ G // ∀ i, u.app i ≫ e.hom.app i = v.app i} := by
  let e : F ≅ G := NatIso.ofComponents (fun i => (d i).val) (fun {i j} g => by
    have hu : u.app i ≫ F.map g = u.app j :=
      (u.naturality g).symm.trans (Category.id_comp _)
    have hv : v.app i ≫ G.map g = v.app j :=
      (v.naturality g).symm.trans (Category.id_comp _)
    apply (cancel_epi (u.app i)).mp
    rw [← Category.assoc, hu, (d j).property, ← Category.assoc, (d i).property, hv])
  exact ⟨e, fun i => (d i).property⟩

/-- Preserve the literal augmentation components under a contravariant functor,
rather than identifying the image of a constant diagram by definitional equality. -/
def contravariantAugmentation {I C D : Type*} [Category I] [Category C] [Category D]
    {P : I ⥤ C} {Q : C} (a : P ⟶ (Functor.const I).obj Q) (F : Cᵒᵖ ⥤ D) :
    (Functor.const Iᵒᵖ).obj (F.obj (op Q)) ⟶ P.op ⋙ F where
  app i := F.map (a.app i.unop).op
  naturality i j g := by
    have ha : P.map g.unop ≫ a.app i.unop = a.app j.unop :=
      (a.naturality g.unop).trans (Category.comp_id _)
    change 𝟙 _ ≫ F.map (a.app j.unop).op =
      F.map (a.app i.unop).op ≫ F.map (P.map g.unop).op
    calc
      𝟙 _ ≫ F.map (a.app j.unop).op = F.map (a.app j.unop).op := Category.id_comp _
      _ = F.map (P.map g.unop ≫ a.app i.unop).op :=
        congrArg (fun k : P.obj j.unop ⟶ Q => F.map k.op) ha.symm
      _ = F.map (a.app i.unop).op ≫ F.map (P.map g.unop).op := F.map_comp _ _

open Modules Modules.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (K : X.IdealSheafData) (C : FiniteEtale X)

/-- The actual finite direct-image module of the given global cover. -/
def globalStructureCoherent : X.CoherentSheaf :=
  ⟨pushforwardStructureSheaf C.obj.hom,
    Modules.Algebra.affineLocallyFiniteType_pushforwardStructureSheaf C.obj.hom⟩

/-- The original structure maps from a global cover to its actual restriction
modules, with all-order naturality inherited from the original cover projections. -/
def restrictionModuleUnit :
    (Functor.const ℕᵒᵖ).obj (pushforwardStructureSheaf C.obj.hom) ⟶
      (restrictionCoverSystem K C).moduleDiagram :=
  contravariantAugmentation (restrictionProjectionNatTrans K C)
    (Modules.Algebra.structureSheafFunctor X)

omit [IsLocallyNoetherian X] in
@[simp]
theorem restrictionModuleUnit_app (n : ℕ) :
    (restrictionModuleUnit K C).app (op n) =
      Modules.Algebra.structurePullbackMap (Limits.pullback.fst C.obj.hom (K ^ n).subschemeι)
        pullback.condition := rfl

/-- Original quotient comparison at every actual restriction stage, together
with the original quotient-unit equation. -/
def restrictionStageComparisonData (n : ℕ) :
    {e : (idealSheafQuotientTower X K (globalStructureCoherent C).obj).obj (op n) ≅
      (restrictionCoverSystem K C).moduleDiagram.obj (op n) //
      (idealSheafQuotientUnit X (K ^ n)).app (globalStructureCoherent C).obj ≫ e.hom =
        (restrictionModuleUnit K C).app (op n)} :=
  cartesianStructureComparisonData C.obj.hom (K ^ n).subschemeι
    (Limits.pullback.fst C.obj.hom (K ^ n).subschemeι)
    (Limits.pullback.snd C.obj.hom (K ^ n).subschemeι) (IsPullback.of_hasPullback _ _)

/-- The original whole completion diagram is naturally isomorphic to the actual
restriction module diagram of the given global finite-etale cover. -/
def restrictionCompletionData :
    {e : idealSheafQuotientTower X K (globalStructureCoherent C).obj ≅
      (restrictionCoverSystem K C).moduleDiagram //
      ∀ n, (idealSheafQuotientUnit X (K ^ n)).app (globalStructureCoherent C).obj ≫
        e.hom.app (op n) = (restrictionModuleUnit K C).app (op n)} := by
  let : ∀ n : ℕᵒᵖ,
      Epi ((idealSheafQuotientTowerUnit X K (globalStructureCoherent C).obj).app n) :=
    fun n => by
      change Epi ((idealSheafQuotientUnit X (K ^ n.unop)).app (globalStructureCoherent C).obj)
      infer_instance
  let d := natIsoOfOriginalUnitData
    (idealSheafQuotientTowerUnit X K (globalStructureCoherent C).obj)
    (restrictionModuleUnit K C) (fun n => restrictionStageComparisonData K C n.unop)
  exact ⟨d.val, fun n => d.property (op n)⟩

/-- The comparison in the native coherent adic-system category. -/
def restrictionCompletionIso :
    (completionFunctor X K).obj (globalStructureCoherent C) ≅
      (restrictionCoverSystem K C).adicSystem :=
  ObjectProperty.isoMk _ (restrictionCompletionData K C).val

/-- The comparison is characterized by the original quotient unit at every stage. -/
@[reassoc (attr := simp)]
theorem unit_restrictionCompletionIso_hom (n : ℕ) :
    (idealSheafQuotientUnit X (K ^ n)).app (globalStructureCoherent C).obj ≫
      (restrictionCompletionIso K C).hom.hom.app (op n) =
        (restrictionModuleUnit K C).app (op n) :=
  (restrictionCompletionData K C).property n

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
