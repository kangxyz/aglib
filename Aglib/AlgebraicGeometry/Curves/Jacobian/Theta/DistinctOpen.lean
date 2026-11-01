/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.NonSpecialOpen
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.RepeatedImage

/-!
# The actual dense rank-one open avoiding the repeated Abel image

In genus at least two, remove the original proper repeated degree-g Abel
image from the original rank-one open. Its dimension bound and integrality
of the same Jacobian make the intersection nonempty and dense. In genus
one retain the rank-one open itself; no repeated-point map is required.

These are actual opens of the supplied identity component. Identification
of their evaluation fibres as simple divisors is a separate theorem, using
the effective-divisor decomposition and whole classifying maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Scheme Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

/-- The actual open complement of the repeated degree-(n+2) Abel image. -/
def nonRepeatedAbelOpen (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    (identityComponentOver P.obj).left.Opens := by
  let := picardCommGrpObj X.hom P R
  have := isProper_repeatedAbelMorphism o ho hX P R n
  exact ⟨(Set.range (repeatedAbelMorphism o ho hX P R n).left)ᶜ,
    (repeatedAbelMorphism o ho hX P R n).left.isClosedMap.isClosed_range.isOpen_compl⟩

/-- The dimension bound gives a nonempty actual complement. -/
theorem nonRepeatedAbelOpen_nonempty (n : ℕ) (hn : n + 1 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    (nonRepeatedAbelOpen hX o ho P R n : Set (identityComponentOver P.obj).left).Nonempty := by
  let := picardCommGrpObj X.hom P R
  change ((Set.range (repeatedAbelMorphism o ho hX P R n).left)ᶜ).Nonempty
  by_contra hempty
  apply not_surjective_repeatedAbelMorphism o ho hX P R n hn
  intro y
  by_contra hy
  exact hempty ⟨y, hy⟩

/-- The original rank-one open with the actual repeated image removed in
genus at least two. The genus-one branch retains the original open. -/
def rankOneNonRepeatedOpen :
    letI := picardCommGrpObj X.hom P R
    (identityComponentOver P.obj).left.Opens := by
  let := picardCommGrpObj X.hom P R
  exact if coherentGenus k X = 1 then degreeUniversalRankOneOpen hX o ho P R (coherentGenus k X)
    else degreeUniversalRankOneOpen hX o ho P R (coherentGenus k X) ⊓
      nonRepeatedAbelOpen hX o ho P R (coherentGenus k X - 2)

/-- Every retained parameter lies in the same actual rank-one open. -/
theorem rankOneNonRepeatedOpen_le_rankOne :
    letI := picardCommGrpObj X.hom P R
    rankOneNonRepeatedOpen hX o ho P R ≤
      degreeUniversalRankOneOpen hX o ho P R (coherentGenus k X) := by
  let := picardCommGrpObj X.hom P R
  unfold rankOneNonRepeatedOpen
  split
  · exact le_rfl
  · exact inf_le_left

/-- In genus at least two, the retained parameters avoid the original
repeated degree-g Abel image. -/
theorem rankOneNonRepeatedOpen_le_nonRepeated (hg : 2 ≤ coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    rankOneNonRepeatedOpen hX o ho P R ≤
      nonRepeatedAbelOpen hX o ho P R (coherentGenus k X - 2) := by
  let := picardCommGrpObj X.hom P R
  simp only [rankOneNonRepeatedOpen, ite_eq_right (by omega : coherentGenus k X ≠ 1)]
  exact inf_le_right

variable [IsAlgClosed k]

/-- In positive genus this actual open is nonempty, including genus one. -/
theorem rankOneNonRepeatedOpen_nonempty (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    (rankOneNonRepeatedOpen hX o ho P R : Set (identityComponentOver P.obj).left).Nonempty := by
  let := picardCommGrpObj X.hom P R
  have := geometricallyIntegral_identityComponentOver hX P R
  have : IsIntegral (identityComponentOver P.obj).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (identityComponentOver P.obj).hom
  have hU := degreeUniversalRankOneOpen_nonempty hX o ho P R hg
  by_cases h1 : coherentGenus k X = 1
  · simpa only [rankOneNonRepeatedOpen, ite_eq_left h1] using hU
  · have hV := nonRepeatedAbelOpen_nonempty hX o ho P R (coherentGenus k X - 2) (by omega)
    simp only [rankOneNonRepeatedOpen, ite_eq_right h1]
    exact nonempty_preirreducible_inter
      (degreeUniversalRankOneOpen hX o ho P R (coherentGenus k X)).isOpen
      (nonRepeatedAbelOpen hX o ho P R (coherentGenus k X - 2)).isOpen hU hV

/-- The same original open is dense in the integral Jacobian. -/
theorem rankOneNonRepeatedOpen_dense (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    Dense (rankOneNonRepeatedOpen hX o ho P R : Set (identityComponentOver P.obj).left) := by
  let := picardCommGrpObj X.hom P R
  have := geometricallyIntegral_identityComponentOver hX P R
  have : IsIntegral (identityComponentOver P.obj).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (identityComponentOver P.obj).hom
  exact (rankOneNonRepeatedOpen hX o ho P R).isOpen.dense
    (rankOneNonRepeatedOpen_nonempty hX o ho P R hg)

end AlgebraicGeometry.Scheme.OverField.Curve
