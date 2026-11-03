/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.AnticanonicalHilbert
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Generation.Hyperplane
public import Aglib.AlgebraicGeometry.Morphisms.Proper.GlobalSections
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Genuine anticanonical Hilbert numerics over an algebraically closed field

An actual regular hyperplane on the full CM curve supplies a finite Cartier
divisor. Its original ideal line and quotient rows give every line-power
cohomology dimension. The inverse-line cohomology hypotheses are actual H0/H1
facts, not a Hilbert identity or a canonical-generation assumption.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Over an algebraically closed field, the original embedding supplies an
actual finite Cartier representative. Its existence uses closed-stalk CM
parameters, not a three-section bound or an assumed Hilbert function. -/
theorem cmCurve_hyperplanePower_cohomology_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (ι : Type u) [Finite ι]
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    [Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 1)]
    [Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (dualLineBundle C (curveHyperplaneLine k ι j)).val 0)]
    (hO : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 0) = 1)
    (hJ : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (dualLineBundle C (curveHyperplaneLine k ι j)).val 1) = 1) (r : ℕ) :
    Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (tensorPowerLineBundle C (curveHyperplaneLine k ι j) r).val 1) ∧
    Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (tensorPowerLineBundle C (curveHyperplaneLine k ι j) r).val 0) = 2 * r + 1 := by
  let X : FScheme k := Over.mk (j ≫ toSpec k ι)
  let O := SheafOfModules.unit C.ringCatSheaf
  let L := curveHyperplaneLine k ι j
  let J := dualLineBundle C L
  let : Subsingleton (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 1) :=
    inferInstanceAs (Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 1))
  have hnonempty : Nonempty C := by
    by_contra h
    let : IsEmpty C := not_nonempty_iff.mp h
    have hsec : Subsingleton Γ(C, ⊤) := inferInstance
    let : Subsingleton (moduleCohomology k X O 0) :=
      ⟨fun a b => (moduleH0Equiv X O).injective (hsec.elim _ _)⟩
    have hz : Module.finrank k (moduleCohomology k X O 0) = 0 :=
      Module.finrank_zero_of_subsingleton
    change Module.finrank k (moduleCohomology k X O 0) = 1 at hO
    omega
  let : Nonempty X.left := hnonempty
  let : LocallyOfFiniteType X.hom :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ toSpec k ι))
  obtain ⟨x⟩ := Scheme.exists_closedPoint X
  let p := j ≫ toSpec k ι
  let a := AlgebraicGeometry.pointOfClosedPoint p x.val x.property
  have ha : a ≫ p = 𝟙 _ := AlgebraicGeometry.pointOfClosedPoint_comp p x.val x.property
  obtain ⟨c, _, hmono, hfinite, _, _⟩ :=
    exists_regular_finite_hyperplane_through_rationalPoint k ι j hCM a ha
  let := hmono
  let φ := curveHyperplaneIdealMap k ι j c
  let i := Scheme.Modules.Hom.zeroInclusion φ
  let : IsFinite (i ≫ X.hom) := hfinite
  let hI : IsLocallyRankOne C (idealModule i) := (zeroIdealLineBundle J φ).property
  let eJ : J.val ≅ idealModule i := zeroIdealLineBundleIso J φ
  let : Subsingleton (moduleCohomology k X (idealModule i) 0) :=
    (moduleCohomologyIso X eJ 0).symm.injective.subsingleton
  have hI₁ : Module.finrank k (moduleCohomology k X (idealModule i) 1) = 1 :=
    (moduleCohomologyIso X eJ 1).finrank_eq.symm.trans hJ
  let eL : L.val ≅ (dualLineBundle C ⟨idealModule i, hI⟩).val :=
    curveHyperplaneDualIdealIso k ι j c
  have h := finiteCartier_dualIdealPower_cohomology X i hI hO hI₁ r
  let eP := TrivializedPower.powerIso C eL r
  exact ⟨⟨fun a b => (moduleCohomologyIso X eP 1).injective (h.1.elim _ _)⟩,
    (moduleCohomologyIso X eP 0).finrank_eq.trans h.2⟩

/-- Actual three first-power sections give all line-power cohomology over
an algebraically closed field via the original regular finite hyperplane. -/
theorem cmCurve_hyperplanePower_cohomology_of_firstPower_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (ι : Type u) [Finite ι]
    {C : Scheme.{u}} (j : C ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (hCM : ∀ x : C, IsClosed ({x} : Set C) →
      ∃ b ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x),
        IsSMulRegular (C.presheaf.stalk x) b ∧
          (Ideal.span {b}).radical = IsLocalRing.maximalIdeal (C.presheaf.stalk x))
    [Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 1)]
    (hO : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 0) = 1)
    (hL : Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (curveHyperplaneLine k ι j).val 0) = 3) (r : ℕ) :
    Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (tensorPowerLineBundle C (curveHyperplaneLine k ι j) r).val 1) ∧
    Module.finrank k (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (tensorPowerLineBundle C (curveHyperplaneLine k ι j) r).val 0) = 2 * r + 1 := by
  let X : FScheme k := Over.mk (j ≫ toSpec k ι)
  let O := SheafOfModules.unit C.ringCatSheaf
  let L := curveHyperplaneLine k ι j
  let J := dualLineBundle C L
  let : Subsingleton (moduleCohomology k X (SheafOfModules.unit X.left.ringCatSheaf) 1) :=
    inferInstanceAs (Subsingleton (moduleCohomology k (Over.mk (j ≫ toSpec k ι))
      (SheafOfModules.unit C.ringCatSheaf) 1))
  have hnonempty : Nonempty C := by
    by_contra h
    let : IsEmpty C := not_nonempty_iff.mp h
    have hsec : Subsingleton Γ(C, ⊤) := inferInstance
    let : Subsingleton (moduleCohomology k X O 0) :=
      ⟨fun a b => (moduleH0Equiv X O).injective (hsec.elim _ _)⟩
    have hz : Module.finrank k (moduleCohomology k X O 0) = 0 :=
      Module.finrank_zero_of_subsingleton
    change Module.finrank k (moduleCohomology k X O 0) = 1 at hO
    omega
  let : Nonempty X.left := hnonempty
  let : LocallyOfFiniteType X.hom :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ toSpec k ι))
  obtain ⟨x⟩ := Scheme.exists_closedPoint X
  let p := j ≫ toSpec k ι
  let a := AlgebraicGeometry.pointOfClosedPoint p x.val x.property
  have ha : a ≫ p = 𝟙 _ := AlgebraicGeometry.pointOfClosedPoint_comp p x.val x.property
  obtain ⟨c, _, hmono, hfinite, _, _⟩ :=
    exists_regular_finite_hyperplane_through_rationalPoint k ι j hCM a ha
  let := hmono
  let φ := curveHyperplaneIdealMap k ι j c
  let i := Scheme.Modules.Hom.zeroInclusion φ
  let : IsFinite (i ≫ X.hom) := hfinite
  let hI : IsLocallyRankOne C (idealModule i) := (zeroIdealLineBundle J φ).property
  let eL : L.val ≅ (dualLineBundle C ⟨idealModule i, hI⟩).val :=
    curveHyperplaneDualIdealIso k ι j c
  have hL₀ : Module.finrank k (moduleCohomology k X
      (dualLineBundle C ⟨idealModule i, hI⟩).val 0) = 3 :=
    (moduleCohomologyIso X eL 0).finrank_eq.symm.trans hL
  have h := finiteCartier_dualIdealPower_cohomology_of_firstPower X i hI hO hL₀ r
  let eP := TrivializedPower.powerIso C eL r
  exact ⟨⟨fun a b => (moduleCohomologyIso X eP 1).injective (h.1.elim _ _)⟩,
    (moduleCohomologyIso X eP 0).finrank_eq.trans h.2⟩


end AlgebraicGeometry.Scheme.Cohomology
