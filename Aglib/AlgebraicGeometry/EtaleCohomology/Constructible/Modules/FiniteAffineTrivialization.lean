/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteRefinement

/-! # Finite affine refinements of actual module trivializations

Quasi-compactness selects finitely many affine étale charts inside the original
trivializing family. The actual inverse-image composition and constant-sheaf
comparison transport the original values and isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

variable {R : Type r} [Ring R]

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge

/-- Every actual finite-type module trivialization on a quasi-compact scheme
has a finite affine refinement, with the same original coefficient ring. -/
theorem FiniteTypeLocalTrivialization.exists_finite_affine
    {X : Scheme.{u}} [CompactSpace X] {F : ModuleSheaf R X}
    (t : FiniteTypeLocalTrivialization F) :
    ∃ s : FiniteTypeLocalTrivialization F,
      Finite s.index ∧ ∀ i, IsAffine (s.chart i).left := by
  let : Scheme.JointlySurjective
      (Scheme.precoverage (@Etale : MorphismProperty Scheme.{u})) :=
    Scheme.instJointlySurjectivePrecoverage
  let 𝒰 : X.Cover (Scheme.precoverage (@Etale : MorphismProperty Scheme.{u})) :=
    { I₀ := t.index
      X i := (t.chart i).left
      f i := (t.chart i).hom
      mem₀ := by
        apply (presieve₀_mem_precoverage_iff (P := @Etale) _).mpr
        refine ⟨?_, fun i => (t.chart i).prop⟩
        intro x
        obtain ⟨i, y, hy⟩ := t.covers x
        exact ⟨i, y, hy⟩ }
  obtain ⟨𝒱, q, hfin, hopen⟩ := EtaleAffineBasis.exists_finite_affine_refinement 𝒰
  let (i : 𝒱.I₀) : Etale (𝒱.f i) := 𝒱.map_prop i
  let s : FiniteTypeLocalTrivialization F :=
    { index := 𝒱.I₀
      chart i := Scheme.Etale.mk (𝒱.f i)
      covers x := by
        obtain ⟨y, hy⟩ := 𝒱.cover.covers x
        exact ⟨𝒱.cover.idx x, y, hy⟩
      value i := t.value (q.s₀ i)
      finite_value i := t.finite_value (q.s₀ i)
      trivialization i := by
        let g := q.h₀ i
        let f := (t.chart (q.s₀ i)).hom
        have h : g ≫ f = 𝒱.f i := q.w₀ i
        exact eqToIso (congrArg (fun a => (moduleInverseImage R a).obj F) h.symm) ≪≫
          (moduleInverseImageComp R f g).app F ≪≫
          (moduleInverseImage R g).mapIso (t.trivialization (q.s₀ i)) ≪≫
          (moduleInverseImageConstantIso R g).app (t.value (q.s₀ i)) }
  refine ⟨s, hfin, fun i => ?_⟩
  change IsAffine (Spec (𝒱.X i))
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
