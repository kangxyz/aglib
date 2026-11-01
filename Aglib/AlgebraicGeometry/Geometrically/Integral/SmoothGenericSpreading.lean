/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Geometrically.Integral.GenericCommonOpen
public import Aglib.AlgebraicGeometry.Geometrically.Integral.CommonOpenFibres
public import Aglib.AlgebraicGeometry.Morphisms.GenericOpenDensity
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality

/-! # Generic geometric integrality for the original smooth family

Over a Noetherian domain, an actual smooth family with geometrically integral
generic fibre has integral nonempty field fibres over one principal open.
The original generic common open, coefficient-cleared hypersurface, and
fibrewise density are constructed, not supplied as descent certificates.
Nonemptiness is explicit: the theorem does not assert surjectivity or the
relative openness of the section-component locus.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- Generic geometric integrality spreads to every nonempty original field
fibre of a smooth quasi-compact quasi-separated family over a Noetherian
domain. The field maps and original pullbacks are unchanged. -/
theorem exists_ne_zero_integral_nonempty_smooth_fibres
    (R K Ω : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [QuasiCompact f] [QuasiSeparated f]
    [GeometricallyIntegral (pullback.snd f (Spec.algebraMap R K))] :
    ∃ r : R, r ≠ 0 ∧ ∀ (L : Type u) [Field L] [Algebra R L],
      algebraMap R L r ≠ 0 → Nonempty (pullback f (Spec.algebraMap R L) : Scheme.{u}) →
        IsIntegral (pullback f (Spec.algebraMap R L)) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : SmoothOfRelativeDimension n (pullback.snd f (Spec.algebraMap R K)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) f
      (Spec.algebraMap R K) inferInstance
  let : IsIntegral (pullback f (Spec.algebraMap R K)) :=
    GeometricallyIntegral.isIntegral_of_subsingleton
      (pullback.snd f (Spec.algebraMap R K))
  let : IsIntegral (pullback f (LocalRing.GenericFiber.baseMap R K)) := by
    change IsIntegral (pullback f (Spec.algebraMap R K))
    infer_instance
  let : IsReduced X := LocalRing.GenericFiber.reduced_of_reduced_generic R K f
  let : IsIntegral X := LocalRing.GenericFiber.integral_of_reduced_integral_generic R K f
  obtain ⟨Q, r, hr, hQ, V, i, j, hV, _, hi, hj, hij⟩ :=
    exists_generic_hypersurface_common_open R K Ω f n
  let := hV
  let := hi
  let := hj
  have hU : (i.opensRange : Set X).Nonempty := by
    rw [Hom.coe_opensRange]
    exact Set.range_nonempty i
  obtain ⟨s, hs, hd⟩ := exists_ne_zero_dense_open_fibres R f i.opensRange hU
  refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
  intro L _ _ hrs hnonempty
  let := hnonempty
  have hrL : algebraMap R L r ≠ 0 := by
    intro h
    exact hrs (by rw [map_mul, h, zero_mul])
  have hsL : algebraMap R L s ≠ 0 := by
    intro h
    exact hrs (by rw [map_mul, h, mul_zero])
  let A := MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span {Q}
  let q := Spec.algebraMap R A
  let b := Spec.algebraMap R L
  let : IsIntegral (pullback q b) :=
    Hypersurface.isIntegral_pullback_of_irreducible_map Q L (hQ L (algebraMap R L) hrL)
  let : IsReduced (pullback f b) :=
    (smoothFieldNormality L (pullback f b) (pullback.snd f b) inferInstance).isReduced
  let iO : Over.mk (i ≫ f) ⟶ Over.mk f := Over.homMk i rfl
  let jO : Over.mk (i ≫ f) ⟶ Over.mk q := Over.homMk j hij.symm
  let : IsOpenImmersion jO.left := by
    change IsOpenImmersion j
    exact hj
  have hdi : Dense (pullback.fst f b ⁻¹' Set.range iO.left) := by
    change Dense (pullback.fst f (Spec.algebraMap R L) ⁻¹' Set.range i)
    simpa only [Hom.coe_opensRange] using hd L hsL
  let : IsIntegral (pullback (Over.mk q).hom b) := by
    change IsIntegral (pullback q b)
    infer_instance
  let : IsReduced (pullback (Over.mk f).hom b) := by
    change IsReduced (pullback f b)
    infer_instance
  let : Nonempty (pullback (Over.mk f).hom b : Scheme.{u}) := by
    change Nonempty (pullback f (Spec.algebraMap R L) : Scheme.{u})
    exact hnonempty
  have hh := isIntegral_pullback_of_dense_common_open b iO jO (by
    change Dense (pullback.fst f b ⁻¹' Set.range iO.left)
    exact hdi)
  change IsIntegral (pullback f b) at hh
  exact hh

end AlgebraicGeometry.Scheme
