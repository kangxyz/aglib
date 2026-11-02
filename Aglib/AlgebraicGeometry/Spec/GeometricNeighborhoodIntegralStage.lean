/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Normal.PointComponent
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Aglib.RingTheory.Henselian.StrictHenselization.GeometricNeighborhood

/-! # Integral genuine refinements of geometric etale neighborhoods

The actual normal component through the original point is a clopen principal
open defined by an idempotent. Its one native localization is regular and a
domain. The existing neighborhood presentation gives a genuine pointed etale
refinement, preserving the original transition and field-valued point.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- Select the actual clopen component of a regular affine scheme at a specified
field-valued point, using its native idempotent principal localization. -/
theorem exists_idempotent_integralLocalization
    (B Ω : Type u) [CommRing B] [IsRegularRing B] [Field Ω] (p : B →+* Ω) :
    ∃ e : B, IsIdempotentElem e ∧ p e ≠ 0 ∧
      IsDomain (Localization.Away e) ∧ IsRegularRing (Localization.Away e) := by
  let x : PrimeSpectrum B := ⟨RingHom.ker p, RingHom.ker_isPrime p⟩
  have hB : NormalStalks (Spec (.of B)) := by
    intro z
    let : IsRegularLocalRing ((Spec (.of B)).presheaf.stalk z) := regularStalks_spec B z
    exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
      IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩
  let U := normalComponentOpen (Spec (.of B)) hB x
  let V : TopologicalSpace.Opens (PrimeSpectrum B) := U
  have hV : IsClopen (V : Set (PrimeSpectrum B)) :=
    ⟨normalComponentOpen_isClosed _ hB x, U.isOpen⟩
  obtain ⟨e, he, hU⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hV
  have hx : x ∈ PrimeSpectrum.basicOpen e := by
    change x ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B))
    rw [← hU]
    exact mem_normalComponentOpen _ hB x
  have hp : p e ≠ 0 := hx
  let D : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen e
  have hEq : U = D := TopologicalSpace.Opens.ext hU
  let : IsIntegral D.toScheme := by
    rw [← hEq]
    exact normalComponentOpen_isIntegral _ hB x
  let : Nonempty (Spec (.of (Localization.Away e))) :=
    ⟨(basicOpenIsoSpecAway (R := .of B) e).hom ⟨x, hx⟩⟩
  let : IsIntegral (Spec (.of (Localization.Away e))) :=
    isIntegral_of_isOpenImmersion (basicOpenIsoSpecAway (R := .of B) e).inv
  have hdom : IsDomain (Localization.Away e) :=
    (affine_isIntegral_iff (.of (Localization.Away e))).mp inferInstance
  have hreg : RegularStalks (Spec (.of (Localization.Away e))) :=
    (regularStalks_spec B).of_isOpenImmersion (Spec.algebraMap B (Localization.Away e))
  exact ⟨e, he, hp, hdom, (regularStalks_spec_iff _).mp hreg⟩

end AlgebraicGeometry.Scheme

namespace GeometricEtaleNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [IsRegularRing R] [Field Ω] [Algebra R Ω]

/-- Every genuine stage over the regular base is itself regular. -/
theorem isRegularRing_algebra (X : GeometricEtaleNeighborhood R Ω) : IsRegularRing X.algebra := by
  let : IsNoetherianRing X.algebra := Algebra.FiniteType.isNoetherianRing R X.algebra
  let : Etale (Spec.algebraMap R X.algebra) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  apply (Scheme.regularStalks_spec_iff _).mp
  intro x
  let : IsRegularLocalRing ((Spec (.of R)).presheaf.stalk
      (Spec.algebraMap R X.algebra x)) := Scheme.regularStalks_spec R _
  exact Scheme.isRegularLocalRing_stalk_of_etale (Spec.algebraMap R X.algebra) x

/-- A genuine pointed refinement with regular domain algebra. The transition
is the original idempotent-localization map under the single native stage
presentation, and hence retains the same field-valued point. -/
theorem exists_integral_refinement (X : GeometricEtaleNeighborhood R Ω) :
    ∃ (e : X.algebra), IsIdempotentElem e ∧ X.point e ≠ 0 ∧
      ∃ (Y : GeometricEtaleNeighborhood R Ω)
        (c : Localization.Away e ≃ₐ[R] Y.algebra) (h : X ⟶ Y),
        h.val = c.toAlgHom.comp (IsScalarTower.toAlgHom R X.algebra (Localization.Away e)) ∧
        IsDomain Y.algebra ∧ IsRegularRing Y.algebra := by
  let : IsRegularRing X.algebra := isRegularRing_algebra R Ω X
  obtain ⟨e, he, hp, hdom, hreg⟩ :=
    Scheme.exists_idempotent_integralLocalization X.algebra Ω X.point.toRingHom
  let : IsDomain (Localization.Away e) := hdom
  let : IsRegularRing (Localization.Away e) := hreg
  let p : Localization.Away e →ₐ[R] Ω :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away e) (f := X.point) e
      (isUnit_iff_ne_zero.mpr hp)
  have hpoint : p.comp (IsScalarTower.toAlgHom R X.algebra (Localization.Away e)) = X.point := by
    apply AlgHom.coe_ringHom_injective
    exact IsLocalization.Away.lift_comp (S := Localization.Away e)
      (g := X.point.toRingHom) e (isUnit_iff_ne_zero.mpr hp)
  obtain ⟨Y, c, hc⟩ := exists_equiv (Localization.Away e) p
  let h : X ⟶ Y :=
    ⟨c.toAlgHom.comp (IsScalarTower.toAlgHom R X.algebra (Localization.Away e)), by
      rw [← AlgHom.comp_assoc, hc, hpoint]⟩
  exact ⟨e, he, hp, Y, c, h, rfl, Function.Injective.isDomain c.symm.toRingHom c.symm.injective,
    IsRegularRing.of_ringEquiv c.toRingEquiv⟩

end GeometricEtaleNeighborhood
