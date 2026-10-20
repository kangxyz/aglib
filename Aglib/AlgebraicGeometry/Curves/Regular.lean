/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RegularScheme
public import Aglib.AlgebraicGeometry.Stalk.EtalePolynomial
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Smoothness from closed DVR stalks

An integral Noetherian scheme of dimension at most one has regular stalks
when its closed stalks are DVRs. A smooth field scheme whose closed stalks
are DVRs has relative dimension one: the dimension is detected at an actual
closed point in each standard-smooth chart.

For a proper curve over an algebraically closed field these facts give
smooth relative dimension one and the bijectivity of the original
structural constants map, directly from the integral, Noetherian, closed-DVR
and dimension-one hypotheses.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.OverField.Curve

universe u

open Divisors

/-- Closed DVR stalks suffice for regularity on the original integral curve:
the only other possible point is the generic point, whose stalk is a field. -/
theorem regularStalks_of_closedDVR (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X ≤ 1) : Scheme.RegularStalks X := by
  intro x
  rcases point_eq_generic_or_isClosed X hdim x with rfl | hx
  · change IsRegularLocalRing X.functionField
    infer_instance
  · let : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      inferInstanceAs (IsDiscreteValuationRing (X.presheaf.stalk (⟨x, hx⟩ : ClosedPoint X).val))
    infer_instance

/-- Closed DVR stalks fix the relative dimension of every actual smooth chart.
The finite-type field scheme is Jacobson, so every nonempty chart contains an
actual point closed in the original scheme. -/
theorem smoothOfRelativeDimension_one_of_closedDVR
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (.of K)) [Smooth p]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] :
    SmoothOfRelativeDimension 1 p := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth p x
  have hUt : U = ⊤ := by
    apply top_unique
    intro z hz
    have hz' : z = p x := Subsingleton.elim _ _
    exact hz' ▸ e hx
  subst U
  let φ := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appLE ⊤ V e).hom
  have hφ : φ.IsStandardSmooth := by
    dsimp only [φ]
    rw [CommRingCat.hom_comp, RingHom.isStandardSmooth_respectsIso.cancel_left_isIso]
    exact hf
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hφ
  let := φ.toAlgebra
  let := hσ
  let := hι
  let n := P.dimension
  have hn : φ.IsStandardSmoothOfRelativeDimension n := ⟨ι, σ, hσ, hι, P, rfl⟩
  obtain ⟨g, _, hg⟩ := hn.exists_etale_mvPolynomial
  obtain ⟨y, hyV, hyclosed⟩ :=
    nonempty_inter_closedPoints (show (V : Set X).Nonempty from ⟨x, hx⟩)
      V.isOpen.isLocallyClosed
  let q := hV.isoSpec.hom ⟨y, hyV⟩
  have hyq : hV.fromSpec q = y := by
    change (hV.isoSpec.hom ≫ hV.fromSpec) ⟨y, hyV⟩ = y
    rw [hV.isoSpec_hom_fromSpec]
    rfl
  have hpre : hV.fromSpec ⁻¹' ({y} : Set X) = {q} := by
    ext z
    change hV.fromSpec z = y ↔ z = q
    rw [← hyq, hV.fromSpec.isOpenEmbedding.injective.eq_iff]
  have hqclosed : IsClosed ({q} : Set (Spec Γ(X, V))) := by
    rw [← hpre]
    exact hyclosed.preimage hV.fromSpec.continuous
  let : q.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hqclosed
  have hd := Scheme.etale_polynomial_stalk_dimension_of_isMaximal K n g hg q
  have hdy : ringKrullDim (X.presheaf.stalk y) = n := by
    rw [ringKrullDim_stalk_eq_coheight] at hd ⊢
    rwa [← coheight_eq_of_isOpenImmersion hV.fromSpec, hyq] at hd
  let : IsDiscreteValuationRing (X.presheaf.stalk y) :=
    inferInstanceAs (IsDiscreteValuationRing
      (X.presheaf.stalk (⟨y, hyclosed⟩ : ClosedPoint X).val))
  have hn1 : n = 1 := by
    have := hdy.symm.trans (IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk y))
    exact_mod_cast this
  have hn : φ.IsStandardSmoothOfRelativeDimension 1 := hn1 ▸ hn
  refine ⟨⊤, hU, V, hV, hx, e, ?_⟩
  dsimp only [φ] at hn
  rwa [CommRingCat.hom_comp,
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)).cancel_left_isIso] at hn

/-- All smoothness and constants applicability conditions are derived from the
original hypotheses of the high-degree vanishing family. -/
theorem regularCurve_smoothAndConstants
    (K : Type u) [Field K] [IsAlgClosed K] (X : FScheme K)
    [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left = 1) (hp : IsProper X.hom) :
    SmoothOfRelativeDimension 1 X.hom ∧ Function.Bijective (Scheme.constants X) := by
  let := hp
  let : Smooth X.hom := Smooth.of_regularStalks_of_perfectField K X.hom
    (regularStalks_of_closedDVR X.left hdim.le)
  exact ⟨smoothOfRelativeDimension_one_of_closedDVR K X.left X.hom,
    Scheme.constants_bijective_of_proper_of_isAlgClosed X⟩

end AlgebraicGeometry.Scheme.OverField.Curve
