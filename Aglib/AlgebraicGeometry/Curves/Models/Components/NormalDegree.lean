/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Restriction
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree
public import Aglib.AlgebraicGeometry.Curves.Abel.Degree
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse

/-!
# The degree of the actual Cartier normal bundle

Source: frozen R5 `LocalModels/Incidence/Cartier.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The original actual schemes, kernel ideals and structural triangles are retained.
Unused model wrappers are replaced by the actual scheme and map parameters.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules.Invertible
open Scheme.OverField.Curve.Picard
open Scheme.Hom.Cartier
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- Actual self-intersection: degree of the restriction of O_X(D), the dual
of the actual component kernel ideal. No integer is supplied. -/
def actualSelfIntersection {k : Type u} [Field k] {X D : Scheme.{u}}
    [IsIntegral D] [AlgebraicGeometry.IsNoetherian D]
    [∀ d : Scheme.ClosedPoint D, IsDiscreteValuationRing (D.presheaf.stalk d.val)]
    (j : D ⟶ X) (p : D ⟶ Spec (.of k))
    (hdim : topologicalKrullDim D ≤ 1) (hprod : Degree.PrincipalProductFormula D p)
    (hJ : IsLocallyRankOne X (idealModule j)) : ℤ :=
  Degree.lineBundleDegree D p hdim hprod
    (pullbackLineBundle j (dualLineBundle X ⟨idealModule j, hJ⟩))

/-- Degree algebra for actual Cartier ideals. The tensor-trivial class identity
and actual restriction isomorphism yield the result; the intersection degree
is the actual finite-scheme dimension and is not a chosen number. -/
theorem selfIntersection_eq_negative_intersectionDegree
    (havoid : IntegralAvoidanceCartierPullback.{u})
    (hdegree : Scheme.OverField.Curve.Abel.FiniteCartierIdealDegree.{u})
    {k : Type u} [Field k] {X C D : Scheme.{u}}
    [IsIntegral D] [AlgebraicGeometry.IsNoetherian D]
    [∀ d : Scheme.ClosedPoint D, IsDiscreteValuationRing (D.presheaf.stalk d.val)]
    (i : C ⟶ X) (j : D ⟶ X) (p : D ⟶ Spec (.of k))
    [IsClosedImmersion i] [IsClosedImmersion j] [IsProper p]
    [IsFinite (pullback.snd i j ≫ p)]
    (hdim : topologicalKrullDim D ≤ 1) (hprod : Degree.PrincipalProductFormula D p)
    (hI : IsLocallyRankOne X (idealModule i)) (hJ : IsLocallyRankOne X (idealModule j))
    (hn : ¬ Set.range j ⊆ Set.range i)
    (hsum : classOf X ⟨idealModule i, hI⟩ + classOf X ⟨idealModule j, hJ⟩ = 0) :
    actualSelfIntersection j p hdim hprod hJ =
      -(Scheme.Hom.finiteSchemeDegree k (pullback.snd i j ≫ p) : ℤ) := by
  let hres := cartierRestriction_invertible havoid i j hI hn
  have hcross := hdegree k D (pullback i j) p (pullback.snd i j) hdim hprod hres
    inferInstance inferInstance inferInstance
  rw [Degree.lineBundleDegree_dual D p hdim hprod ⟨idealModule (pullback.snd i j), hres⟩] at hcross
  have hiso := Degree.lineBundleDegree_iso D p hdim hprod
    (L := pullbackLineBundle j ⟨idealModule i, hI⟩)
    (N := ⟨idealModule (pullback.snd i j), hres⟩)
    (cartierRestrictionIso havoid i j hI hn)
  have hclasses : classOf X (dualLineBundle X ⟨idealModule j, hJ⟩) =
      classOf X ⟨idealModule i, hI⟩ := by
    rw [classOf_dual]
    exact (eq_neg_of_add_eq_zero_left hsum).symm
  have hself : actualSelfIntersection j p hdim hprod hJ =
      Degree.lineBundleDegree D p hdim hprod (pullbackLineBundle j ⟨idealModule i, hI⟩) :=
    congrArg (fun a => Degree.picardDegree D p hdim hprod (pullbackClass j a)) hclasses
  linarith

end AlgebraicGeometry.Scheme.Hom
