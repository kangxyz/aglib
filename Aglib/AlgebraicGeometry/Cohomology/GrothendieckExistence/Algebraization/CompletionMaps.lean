/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.JointDetection
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompatiblePresentation

/-! # Original-unit lifting and joint detection

The full-faithfulness calculation is made for abstract native functors and
retains its whole original-unit equation. The sheaf specialization uses the
existing quotient descent, whose naturality cancels the actual quotient units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] {J : Type u₃} [Category.{v₃} J]
  {V : D ⥤ C} {E : D ⥤ (J ⥤ C)}
  (unit : V ⋙ Functor.const J ⟶ E)
  {M : D} {F : J ⥤ C} (beta : E.obj M ≅ F)

/-- The specified unit followed by the specified formal isomorphism. -/
def originalUnitMaps : (Functor.const J).obj (V.obj M) ⟶ F :=
  unit.app M ≫ beta.hom

/-- Fullness lifts a descended arrow, with its whole original-unit equation. -/
def originalUnitLiftData (hE : E.FullyFaithful) (P : D)
    (p : (Functor.const J).obj (V.obj P) ⟶ F) (d : E.obj P ⟶ F)
    (hd : unit.app P ≫ d = p) :
    { f : P ⟶ M //
      (Functor.const J).map (V.map f) ≫ originalUnitMaps unit beta = p } := by
  let f := hE.preimage (d ≫ beta.inv)
  refine ⟨f, ?_⟩
  change (V ⋙ Functor.const J).map f ≫ (unit.app M ≫ beta.hom) = p
  rw [← Category.assoc, unit.naturality, Category.assoc]
  simpa only [f, hE.map_preimage, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using hd

/-- Faithfulness and epimorphic original units detect all coherent-source
maps after every specified component of the formal comparison. -/
theorem originalUnitMaps_jointlyDetects (hV : V.FullyFaithful)
    (hE : E.FullyFaithful) (P : D)
    (hEpi : ∀ j, Epi ((unit.app P).app j)) :
    JointlyDetects (fun j => (originalUnitMaps unit beta).app j) (V.obj P) := by
  intro a b hab
  have h : E.map (hV.preimage a) = E.map (hV.preimage b) := by
    apply NatTrans.ext
    funext j
    let := hEpi j
    apply (cancel_epi ((unit.app P).app j)).mp
    apply (cancel_mono (beta.hom.app j)).mp
    have ha := NatTrans.congr_app (unit.naturality (hV.preimage a)) j
    have hb := NatTrans.congr_app (unit.naturality (hV.preimage b)) j
    simp only [Functor.comp_map, NatTrans.comp_app, Functor.const_map_app,
      hV.map_preimage] at ha hb
    rw [← ha, ← hb]
    simpa only [originalUnitMaps, NatTrans.comp_app, Category.assoc] using hab j
  simpa only [hV.map_preimage] using congrArg V.map (hE.map_injective h)

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X] (K : X.IdealSheafData)

/-- Original quotient units, simultaneously natural in coherent coefficients. -/
def coherentCompletionUnit :
    QuasiCoherent.finiteTypeSheavesToModules X ⋙ Functor.const ℕᵒᵖ ⟶
      completionFunctor X K ⋙ adicSystemToDiagram X K where
  app M := idealSheafQuotientTowerUnit X K M.obj
  naturality {M N} f := by
    apply NatTrans.ext
    funext n
    exact (idealSheafQuotientUnit X (K ^ n.unop)).naturality f.hom

/-- Original completion maps on the entire diagram, not chosen stagewise. -/
abbrev originalCompletionMaps {M : X.CoherentSheaf} {F : AdicSystem X K}
    (beta : (completionFunctor X K).obj M ≅ F) :
    (Functor.const ℕᵒᵖ).obj M.obj ⟶ F.obj :=
  originalUnitMaps (coherentCompletionUnit K) ((adicSystemToDiagram X K).mapIso beta)

/-- Lift any compatible original maps into an adic system and preserve the
whole given family of equations, using the original quotient descent. -/
def originalCompletionLiftData
    (h : (completionFunctor X K).FullyFaithful)
    {M : X.CoherentSheaf} {F : AdicSystem X K}
    (beta : (completionFunctor X K).obj M ≅ F)
    (P : X.CoherentSheaf) (p : (Functor.const ℕᵒᵖ).obj P.obj ⟶ F.obj) :
    { f : P ⟶ M //
      (Functor.const ℕᵒᵖ).map f.hom ≫ originalCompletionMaps K beta = p } :=
  originalUnitLiftData (coherentCompletionUnit K)
    ((adicSystemToDiagram X K).mapIso beta)
    (h.comp (ObjectProperty.fullyFaithfulι (IsAdicSystem X K))) P p
    (compatibleQuotientDesc K F.property.annihilated p)
    (idealSheafQuotientTowerUnit_compatibleQuotientDesc K F.property.annihilated p)

/-- Every coherent source is detected by the original completion maps. -/
theorem originalCompletionMaps_jointlyDetects
    (h : (completionFunctor X K).FullyFaithful)
    {M : X.CoherentSheaf} {F : AdicSystem X K}
    (beta : (completionFunctor X K).obj M ≅ F) (P : X.CoherentSheaf) :
    JointlyDetects (fun n => (originalCompletionMaps K beta).app n) P.obj :=
  originalUnitMaps_jointlyDetects (coherentCompletionUnit K)
    ((adicSystemToDiagram X K).mapIso beta)
    (QuasiCoherent.affineLocallyFiniteType X).fullyFaithfulι
    (h.comp (ObjectProperty.fullyFaithfulι (IsAdicSystem X K))) P (by
      intro n
      change Epi ((idealSheafQuotientUnit X (K ^ n.unop)).app P.obj)
      infer_instance)

end AlgebraicGeometry.Scheme.Modules.Coherent
