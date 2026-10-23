/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Henselian.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Henselian.ProperLimit

/-!
# Picard restriction on proper henselian schemes with two affine opens

Actual proper finite-presentation approximation reduces to the proved
arithmetic finite-data case. The conclusion retains the original residue
pullback, without Noetherianity, flatness, excellence or finite presentation
of the original proper morphism. Schemes finite over the projective line
are a direct application of their actual two-affine cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- Every actual line bundle on the original closed fibre lifts over any
henselian local base when the proper scheme has an affine binary cover. -/
theorem exists_lineBundle_lift_residue_affineBinary
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (A : Scheme.AffineBinaryCover X)
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (L : LineBundle (Limits.pullback f (LocalRing.residueSpecMap R))) :
    ∃ W : LineBundle X,
      Nonempty ((pullback (Limits.pullback.fst f (LocalRing.residueSpecMap R))).obj W.val ≅
        L.val) := by
  apply exists_lineBundle_lift_residue_affineBinary_of_finitePresentation_lifts R A f ?_ L
  intro Y g hg hfp B C
  let := hg
  let := hfp
  exact exists_lineBundle_lift_residue_affineBinary_of_finitePresentation R B g C

/-- Surjectivity of the original residue-fibre Picard pullback on every
proper scheme with an affine binary cover over an arbitrary henselian local ring. -/
theorem pullbackClass_residue_affineBinary_surjective
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (A : Scheme.AffineBinaryCover X)
    (f : X ⟶ Spec (.of R)) [IsProper f] :
    Function.Surjective (pullbackClass (Limits.pullback.fst f (LocalRing.residueSpecMap R))) := by
  intro a
  induction a using Quotient.inductionOn with
  | h L =>
    obtain ⟨M, ⟨e⟩⟩ := exists_lineBundle_lift_residue_affineBinary R A f L
    exact ⟨classOf X M, Quotient.sound ⟨e⟩⟩

/-- Actual residue-fibre bundles lift for a proper scheme affine over the
native projective line of any henselian local ring. -/
theorem exists_lineBundle_lift_residue_projectiveLine
    (R : Type u) [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (p : X ⟶ Scheme.ProjectiveLine.projectiveP1 R) [IsAffineHom p]
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (L : LineBundle (Limits.pullback f (LocalRing.residueSpecMap R))) :
    ∃ W : LineBundle X,
      Nonempty ((pullback (Limits.pullback.fst f (LocalRing.residueSpecMap R))).obj W.val ≅
        L.val) :=
  exists_lineBundle_lift_residue_affineBinary R (projectiveLineAffineBinaryCover p) f L

/-- The original Picard restriction is surjective for every scheme finite
over the native projective line over any henselian local ring. -/
theorem pullbackClass_residue_finite_projectiveLine_surjective
    (R : Type u) [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (p : X ⟶ Scheme.ProjectiveLine.projectiveP1 R) [IsFinite p] :
    Function.Surjective (pullbackClass (Limits.pullback.fst
      (p ≫ Scheme.ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))) :=
  pullbackClass_residue_affineBinary_surjective R (projectiveLineAffineBinaryCover p)
    (p ≫ Scheme.ProjectiveLine.structureMap R)

end AlgebraicGeometry.Scheme.Modules.Invertible
