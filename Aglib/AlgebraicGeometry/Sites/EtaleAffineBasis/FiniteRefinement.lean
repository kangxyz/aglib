/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Finite affine refinements of small étale covering sieves

A covering sieve on a quasi-compact object of the original small étale site
contains a finite jointly surjective family of affine objects. No compactness
of arbitrary objects of the small site is asserted. This is the geometric
finite-data input for continuity of sections and cohomology.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

/-- An étale cover of a quasi-compact scheme has a finite affine refinement,
with open-immersion refinement arrows. -/
theorem exists_finite_affine_refinement {X : Scheme.{u}} [CompactSpace X]
    (𝒰 : X.Cover (Scheme.precoverage
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f))) :
    ∃ (𝒱 : Scheme.AffineCover.{u}
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f) X)
      (r : 𝒱.cover ⟶ 𝒰),
      Finite 𝒱.I₀ ∧ ∀ i, IsOpenImmersion (r.h₀ i) := by
  let : Scheme.JointlySurjective
      (Scheme.precoverage (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f)) :=
    Scheme.instJointlySurjectivePrecoverage
  let : MorphismProperty.RespectsLeft
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f) @IsOpenImmersion :=
    { precomp := fun {_ _ _} i hi g hg ↦ by
        let : IsOpenImmersion i := hi
        let : AlgebraicGeometry.Etale g := hg
        exact AlgebraicGeometry.Etale.etale_comp i g }
  let : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i ↦ (𝒰.f i).isOpenMap)
  exact QuasiCompactCover.exists_hom 𝒰

/-- Every original small étale covering sieve over a quasi-compact object
contains a finite affine covering family. The resulting arrows remain literal
arrows of the original sieve. -/
theorem exists_finite_affine_family {S : Scheme.{u}} (U : S.Etale)
    [CompactSpace U.left] (R : Sieve U) (hR : R ∈ S.smallEtaleTopology U) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → S.Etale) (f : ∀ i, V i ⟶ U),
      (∀ i, IsAffine (V i).left) ∧ (∀ i, R (f i)) ∧
        Sieve.ofArrows V f ∈ S.smallEtaleTopology U := by
  let : Scheme.IsJointlySurjectivePreserving
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f) :=
    Scheme.isJointlySurjectivePreserving _
  obtain ⟨𝒰, hOver, hEtale, hle⟩ :=
    (Scheme.mem_smallGrothendieckTopology U R).mp hR
  let : 𝒰.Over S := hOver
  let (j : 𝒰.I₀) : (𝒰.X j).Over S := Scheme.Cover.Over.over (𝒰 := 𝒰) j
  let (j : 𝒰.I₀) : (𝒰.f j).IsOver S := Scheme.Cover.Over.isOver_map (𝒰 := 𝒰) j
  obtain ⟨𝒱, r, hfin, hopen⟩ := exists_finite_affine_refinement 𝒰
  let : Finite 𝒱.I₀ := hfin
  have (i : 𝒱.I₀) : Etale (𝒱.f i) := 𝒱.map_prop i
  have : Etale U.hom := U.prop
  let V (i : 𝒱.I₀) : S.Etale := Scheme.Etale.mk (𝒱.f i ≫ U.hom)
  let f (i : 𝒱.I₀) : V i ⟶ U := MorphismProperty.Over.homMk (𝒱.f i)
  refine ⟨𝒱.I₀, inferInstance, V, f, fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · change IsAffine (Spec (𝒱.X i))
    infer_instance
  · let W : S.Etale := (𝒰.X (r.s₀ i)).asOverProp S (hEtale (r.s₀ i))
    let g : W ⟶ U := (𝒰.f (r.s₀ i)).asOverProp S
    let a : V i ⟶ W := MorphismProperty.Over.homMk (r.h₀ i) (by
      exact (congrArg (fun k : W.left ⟶ S ↦ r.h₀ i ≫ k)
        (MorphismProperty.Over.w g).symm).trans
        ((Category.assoc (r.h₀ i) g.left U.hom).symm.trans
          (congrArg (fun k : Spec (𝒱.X i) ⟶ U.left ↦ k ≫ U.hom) (r.w₀ i))))
    have hg : R g := hle W g (Presieve.ofArrows.mk (C := S.Etale) (r.s₀ i))
    have ha : a ≫ g = f i := by
      apply MorphismProperty.Over.Hom.ext
      exact r.w₀ i
    simpa only [ha] using R.downward_closed hg a
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    let : Scheme.JointlySurjective
        (Scheme.precoverage (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ AlgebraicGeometry.Etale f)) :=
      Scheme.instJointlySurjectivePrecoverage
    exact 𝒱.cover.iUnion_range

end AlgebraicGeometry.Scheme.EtaleAffineBasis
