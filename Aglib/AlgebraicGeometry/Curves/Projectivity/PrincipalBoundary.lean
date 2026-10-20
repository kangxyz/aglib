/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Sections

/-!
# Principal boundaries on the original integral proper curve

A principal boundary consists of an affine open `U`, a nonzero nonunit section
`f` on `U`, its finite nonempty zero set `Z` in the original scheme, and the
open complement `W`. The cover `U ∪ W` has overlap exactly the basic open of
`f`; its restriction there is a unit. Multiplication by every restriction of
`f` to a subopen of `U` is injective, including on the empty open.

The existence constructor uses the geometric nonzero-nonunit section and
curve-topology theorems in `ProperCurveFiniteness` at R5 revision
`5b493a5709ba2e4242f94cf163611602c03f3cf3`. Its ordinary mathematical route is
the principal-boundary step of the integral-curve projectivity derivation,
independently reviewed on 2026-10-17. The exact restriction map is native
`Scheme.Modules.Invertible.sectionRestrict`, from Aglib revision
`197ca0728db3cdf1552a6bcefeeda901e3377862`.

No normality, smoothness, or prior projectivity of the original curve is used.
`Z` records the underlying zero set, with no assertion about the multiplicity
of a Cartier divisor or a scheme-theoretic fibre.
-/




@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart
open AlgebraicGeometry.Scheme

open CategoryTheory AlgebraicGeometry TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.Modules.Invertible (sectionRestrict sectionRestrict_comp)

namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity

universe u

/-- Actual two-open principal data and finite closed support on the original
scheme. Its regularity and overlap fields are the native line-gluing inputs. -/
structure PrincipalBoundary (X : Scheme.{u}) where
  U : X.Opens
  W : X.Opens
  affine : IsAffineOpen U
  covers : U ⊔ W = ⊤
  f : Γ(X, U)
  f_ne_zero : f ≠ 0
  f_nonunit : ¬ IsUnit f
  Z : Set X
  zeroSet : Z = (U : Set X) \ (X.basicOpen f : Set X)
  Z_finite : Z.Finite
  Z_nonempty : Z.Nonempty
  Z_closed : IsClosed Z
  point_closed : ∀ x ∈ Z, IsClosed ({x} : Set X)
  complement : (W : Set X) = Zᶜ
  overlap : U ⊓ W = X.basicOpen f
  unit_overlap : IsUnit (sectionRestrict X (show U ⊓ W ≤ U from inf_le_left) f)
  regular : ∀ V (hV : V ≤ U),
    Function.Injective (fun a : Γ(X, V) => sectionRestrict X hV f * a)

namespace PrincipalBoundary

variable {X : Scheme.{u}} (b : PrincipalBoundary X)

/-- The recorded support is the actual zero set of the displayed section. -/
@[simp] theorem mem_Z_iff (x : X) :
    x ∈ b.Z ↔ x ∈ b.U ∧ x ∉ X.basicOpen b.f := by
  rw [b.zeroSet]
  rfl

/-- The complement contains the original generic point. -/
theorem genericPoint_mem_W [IsIntegral X] : genericPoint X ∈ b.W := by
  have hDne : (X.basicOpen b.f : Set X).Nonempty := by
    by_contra h
    exact b.f_ne_zero ((basicOpen_eq_bot_iff b.f).mp
      ((Opens.not_nonempty_iff_eq_bot (X.basicOpen b.f)).mp h))
  have hEtaD : genericPoint X ∈ X.basicOpen b.f :=
    ((genericPoint_spec X).mem_open_set_iff (X.basicOpen b.f).isOpen).mpr
      (by simpa using hDne)
  have hmem : genericPoint X ∈ b.U ⊓ b.W := by
    rw [b.overlap]
    exact hEtaD
  exact hmem.2

/-- The boundary supplies an actual nongeneric closed zero point in its
original affine open; membership outside the basic open is vanishing at that point. -/
theorem exists_nongeneric_closed_zero [IsIntegral X] :
    ∃ x : X, x ∈ b.U ∧ x ≠ genericPoint X ∧ IsClosed ({x} : Set X) ∧
      x ∉ X.basicOpen b.f := by
  obtain ⟨x, hxZ⟩ := b.Z_nonempty
  obtain ⟨hxU, hxD⟩ := (b.mem_Z_iff x).mp hxZ
  refine ⟨x, hxU, ?_, b.point_closed x hxZ, hxD⟩
  intro hx
  subst x
  have hW : genericPoint X ∈ (b.W : Set X) := b.genericPoint_mem_W
  rw [b.complement] at hW
  exact hW hxZ

end PrincipalBoundary

/-- A nonzero section on an integral scheme remains a nonzerodivisor on every
subopen, with the empty-open case supplied by its subsingleton section ring. -/
theorem principalSection_regular (X : Scheme.{u}) [IsIntegral X]
    {U : X.Opens} (f : Γ(X, U)) (hf : f ≠ 0)
    (V : X.Opens) (hV : V ≤ U) :
    Function.Injective (fun a : Γ(X, V) => sectionRestrict X hV f * a) := by
  classical
  by_cases hne : Nonempty V
  · let : Nonempty V := hne
    have hres : sectionRestrict X hV f ≠ 0 := by
      intro hzero
      apply hf
      apply map_injective_of_isIntegral X (homOfLE hV)
      change sectionRestrict X hV f = sectionRestrict X hV 0
      simpa using hzero
    exact mul_right_injective₀ hres
  · have hbot : V = ⊥ := (Opens.not_nonempty_iff_eq_bot V).mp (by simpa using hne)
    subst V
    intro a b _
    exact Subsingleton.elim a b

variable {K : Type u} [Field K]

/-- Every integral proper field curve of dimension one has an actual principal
boundary on its original scheme, without a normality or projectivity premise. -/
theorem nonempty_principalBoundary (X : FScheme K)
    [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1) :
    Nonempty (PrincipalBoundary X.left) := by
  classical
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := ⟨⟩
  obtain ⟨U, hU, f, hf, hfu⟩ := GraphInput.exists_affine_nonzero_nonunit X hdim
  let : Nonempty U.1 := hU
  let D := X.left.basicOpen f
  let Z : Set X.left := (U.1 : Set X.left) \ (D : Set X.left)
  have hDne : (D : Set X.left).Nonempty := by
    by_contra h
    exact hf ((basicOpen_eq_bot_iff f).mp ((Opens.not_nonempty_iff_eq_bot D).mp h))
  have hEtaD : genericPoint X.left ∈ D :=
    ((genericPoint_spec X.left).mem_open_set_iff D.isOpen).mpr (by simpa using hDne)
  have hDcompl : (D : Set X.left)ᶜ ≠ Set.univ := by
    intro h
    obtain ⟨x, hx⟩ := hDne
    have hx' : x ∈ (D : Set X.left)ᶜ := by rw [h]; trivial
    exact hx' hx
  have hZfinite : Z.Finite :=
    (DimensionOne.finite_of_isClosed_of_ne_univ X.left hdim.le
      D.isOpen.isClosed_compl hDcompl).subset (fun _ hx => hx.2)
  have hZnonempty : Z.Nonempty := by
    by_contra h
    apply hfu
    apply X.left.toRingedSpace.isUnit_of_isUnit_germ U.1 f
    intro x hxU
    apply (X.left.mem_basicOpen f x hxU).mp
    by_contra hxD
    exact h ⟨x, hxU, hxD⟩
  have hpoint : ∀ x ∈ Z, IsClosed ({x} : Set X.left) := by
    intro x hxZ
    rcases DimensionOne.point_eq_generic_or_isClosed X.left hdim.le x with hx | hx
    · subst x
      exact False.elim (hxZ.2 hEtaD)
    · exact hx
  have hZclosed : IsClosed Z := by
    simpa only [Set.biUnion_of_singleton] using hZfinite.isClosed_biUnion hpoint
  let W : X.left.Opens := ⟨Zᶜ, hZclosed.isOpen_compl⟩
  have hcover : U.1 ⊔ W = ⊤ := by
    apply top_unique
    intro x _
    by_cases hxU : x ∈ U.1
    · exact Or.inl hxU
    · exact Or.inr (fun hxZ => hxU hxZ.1)
  have hoverlap : U.1 ⊓ W = D := by
    ext x
    constructor
    · rintro ⟨hxU, hxW⟩
      by_contra hxD
      exact hxW ⟨hxU, hxD⟩
    · intro hxD
      exact ⟨X.left.basicOpen_le f hxD, fun hxZ => hxZ.2 hxD⟩
  have hunit : IsUnit (sectionRestrict X.left (show U.1 ⊓ W ≤ U.1 from inf_le_left) f) := by
    have hDunit : IsUnit (sectionRestrict X.left (X.left.basicOpen_le f) f) :=
      X.left.toRingedSpace.isUnit_res_basicOpen f
    simpa only [sectionRestrict_comp] using
      hDunit.map (sectionRestrict X.left hoverlap.le)
  exact ⟨{
    U := U.1
    W := W
    affine := U.2
    covers := hcover
    f := f
    f_ne_zero := hf
    f_nonunit := hfu
    Z := Z
    zeroSet := rfl
    Z_finite := hZfinite
    Z_nonempty := hZnonempty
    Z_closed := hZclosed
    point_closed := hpoint
    complement := rfl
    overlap := hoverlap
    unit_overlap := hunit
    regular := principalSection_regular X.left f hf }⟩

/-- A chosen actual principal boundary, constructed unconditionally from the
original integral proper curve and its dimension-one hypothesis. -/
def principalBoundaryOfProperIntegralCurve (X : FScheme K)
    [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1) : PrincipalBoundary X.left :=
  Classical.choice (nonempty_principalBoundary X hdim)

end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
