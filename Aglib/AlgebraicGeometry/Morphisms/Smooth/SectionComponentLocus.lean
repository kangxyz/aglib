/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentCartesian

/-! # The original fibrewise section-component locus

The locus is the union of the images of the actual scheme-theoretic fibre
components containing the original section. Its pointwise description uses
the original `asFiber` point. Base change uses Mathlib's original residue-field
cartesian square and the single field-component construction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme
universe u

/-- The actual fibrewise component locus, with no chosen chart or model. -/
def sectionComponentLocus {X S : Scheme.{u}} (f : X ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) : Set X :=
  {x | ∃ (s : S) (y : f.fiber s),
    y ∈ connectedComponent (sectionOnFiber f σ hσ s
      (IsLocalRing.closedPoint (S.residueField s))) ∧
      f.fiberι s y = x}

private lemma fiberι_base_point {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (y : f.fiber s) : f (f.fiberι s y) = s := by
  have h := congrArg (fun a : f.fiber s ⟶ S => a y) (f.fiber_fac s)
  change f (f.fiberι s y) = S.fromSpecResidueField s (f.fiberToSpecResidueField s y) at h
  exact h.trans (S.fromSpecResidueField_apply s (f.fiberToSpecResidueField s y))

/-- Membership may be computed using any original point in the specified
scheme-theoretic fibre; the fibre inclusion is the actual embedding. -/
lemma mem_sectionComponentLocus_fiberι_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) (s : S) (y : f.fiber s) :
    f.fiberι s y ∈ sectionComponentLocus f σ hσ ↔
      y ∈ connectedComponent (sectionOnFiber f σ hσ s
        (IsLocalRing.closedPoint (S.residueField s))) := by
  constructor
  · rintro ⟨t, z, hz, he⟩
    have ht : t = s := by
      have h := congrArg f he
      simpa only [fiberι_base_point] using h
    subst t
    have hzy : z = y := (f.fiberι s).isEmbedding.injective he
    exact hzy ▸ hz
  · intro hy
    exact ⟨s, y, hy, rfl⟩

/-- The union definition equals the intrinsic original `asFiber` condition. -/
lemma mem_sectionComponentLocus_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) (x : X) :
    x ∈ sectionComponentLocus f σ hσ ↔
      f.asFiber x ∈ connectedComponent (sectionOnFiber f σ hσ (f x)
        (IsLocalRing.closedPoint (S.residueField (f x)))) := by
  simpa only [Hom.fiberι_asFiber] using
    mem_sectionComponentLocus_fiberι_iff f σ hσ (f x) (f.asFiber x)

section Cartesian
variable {X S P T : Scheme.{u}} (f : X ⟶ S) (a : P ⟶ X) (p : P ⟶ T) (b : T ⟶ S)
  (H : IsPullback a p f b)

/-- The original residue-field fibre map already used by Mathlib's cartesian
fibre square. Its original arrows and equations are unchanged. -/
def sectionComponentFiberMap (t : T) : p.fiber t ⟶ f.fiber (b t) :=
  pullback.map p (T.fromSpecResidueField t) f (S.fromSpecResidueField (b t))
    a (Spec.map (b.residueFieldMap t)) b H.w.symm (by simp)

@[reassoc]
lemma sectionComponentFiberMap_fst (t : T) :
    sectionComponentFiberMap f a p b H t ≫ f.fiberι (b t) = p.fiberι t ≫ a := by
  exact pullback.lift_fst _ _ _

@[reassoc]
lemma sectionComponentFiberMap_snd (t : T) :
    sectionComponentFiberMap f a p b H t ≫ f.fiberToSpecResidueField (b t) =
      p.fiberToSpecResidueField t ≫ Spec.map (b.residueFieldMap t) := by
  exact pullback.lift_snd _ _ _

/-- The same original fibre map carries the original compatible sections. -/
lemma sectionComponentFiberMap_section
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) (τ : T ⟶ P) (hτ : τ ≫ p = 𝟙 _)
    (hτa : τ ≫ a = b ≫ σ) (t : T) :
    sectionOnFiber p τ hτ t ≫ sectionComponentFiberMap f a p b H t =
      Spec.map (b.residueFieldMap t) ≫ sectionOnFiber f σ hσ (b t) := by
  apply pullback.hom_ext
  · change (sectionOnFiber p τ hτ t ≫ sectionComponentFiberMap f a p b H t) ≫
      f.fiberι (b t) = (Spec.map (b.residueFieldMap t) ≫
        sectionOnFiber f σ hσ (b t)) ≫ f.fiberι (b t)
    rw [Category.assoc, sectionComponentFiberMap_fst, ← Category.assoc,
      sectionOnFiber_fiberι, Category.assoc, hτa]
    rw [Category.assoc, sectionOnFiber_fiberι]
    simpa only [Category.assoc] using (congrArg (fun c => c ≫ σ)
      (b.SpecMap_residueFieldMap_fromSpecResidueField t)).symm
  · change (sectionOnFiber p τ hτ t ≫ sectionComponentFiberMap f a p b H t) ≫
      f.fiberToSpecResidueField (b t) = (Spec.map (b.residueFieldMap t) ≫
        sectionOnFiber f σ hσ (b t)) ≫ f.fiberToSpecResidueField (b t)
    rw [Category.assoc, sectionComponentFiberMap_snd, ← Category.assoc,
      sectionOnFiber_structural, Category.id_comp, Category.assoc,
      sectionOnFiber_structural, Category.comp_id]

/-- The original residue-field fibre square has exact section-component
preimage, supplied by the single field-extension construction. -/
lemma sectionComponentFiberMap_preimage [Smooth f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) (τ : T ⟶ P) (hτ : τ ≫ p = 𝟙 _)
    (hτa : τ ≫ a = b ≫ σ) (t : T) :
    sectionComponentFiberMap f a p b H t ⁻¹'
        connectedComponent (sectionOnFiber f σ hσ (b t)
          (IsLocalRing.closedPoint (S.residueField (b t)))) =
      connectedComponent (sectionOnFiber p τ hτ t
        (IsLocalRing.closedPoint (T.residueField t))) := by
  let : Algebra (S.residueField (b t)) (T.residueField t) :=
    (b.residueFieldMap t).hom.toAlgebra
  let : Smooth (f.fiberToSpecResidueField (b t)) := by
    change Smooth (pullback.snd f (S.fromSpecResidueField (b t)))
    infer_instance
  have HF : IsPullback (sectionComponentFiberMap f a p b H t)
      (p.fiberToSpecResidueField t) (f.fiberToSpecResidueField (b t))
      (Spec.algebraMap (S.residueField (b t)) (T.residueField t)) :=
    isPullback_fiberToSpecResidueField_of_isPullback H t
  have h := SmoothSectionComponent.componentOpen_preimage_of_isPullback
    (S.residueField (b t)) (T.residueField t) (f.fiberToSpecResidueField (b t))
    (sectionComponentFiberMap f a p b H t) (p.fiberToSpecResidueField t) HF
    (sectionOnFiber f σ hσ (b t)) (sectionOnFiber_structural f σ hσ (b t))
    (sectionOnFiber p τ hτ t) (sectionOnFiber_structural p τ hτ t)
    (sectionComponentFiberMap_section f a p b H σ hσ τ hτ hτa t)
  simpa only [SmoothSectionComponent.componentOpen_eq_connectedComponent] using h

include H

/-- The actual locus commutes with the original cartesian base change and
original compatible sections, as a literal preimage equality. -/
theorem sectionComponentLocus_preimage_of_isPullback [Smooth f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) (τ : T ⟶ P) (hτ : τ ≫ p = 𝟙 _)
    (hτa : τ ≫ a = b ≫ σ) :
    a ⁻¹' sectionComponentLocus f σ hσ = sectionComponentLocus p τ hτ := by
  ext z
  let t := p z
  let y := p.asFiber z
  let F := sectionComponentFiberMap f a p b H t
  have hz : f.fiberι (b t) (F y) = a z := by
    have h := congrArg (fun c : p.fiber t ⟶ X => c y)
      (sectionComponentFiberMap_fst f a p b H t)
    change f.fiberι (b t) (F y) = a (p.fiberι t y) at h
    change f.fiberι (b t) (F y) = a (p.fiberι (p z) (p.asFiber z)) at h
    exact h.trans (congrArg a (p.fiberι_asFiber z))
  have hl := mem_sectionComponentLocus_fiberι_iff f σ hσ (b t) (F y)
  rw [hz] at hl
  have hr := mem_sectionComponentLocus_iff p τ hτ z
  have hc := congrArg (fun U : Set (p.fiber t) => y ∈ U)
    (sectionComponentFiberMap_preimage f a p b H σ hσ τ hτ hτa t)
  exact hl.trans ((Iff.of_eq hc).trans hr.symm)

end Cartesian
end AlgebraicGeometry.Scheme
