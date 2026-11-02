/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PrincipalBaseChangeLimit
public import Aglib.AlgebraicGeometry.Limits.DenseRange
public import Aglib.AlgebraicGeometry.Morphisms.Flat.GenericFiberCriteria
public import Aglib.AlgebraicGeometry.Morphisms.Etale.Reduced
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! # Density of the original fraction-field principal projections

The native principal-localization maps into the supplied original fraction
field are injective. Their literal base changes are dense along smooth maps,
including the original finite-etale covering sources. Integrality is therefore
reflected from the same generic cover, with reducedness derived internally.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

universe u

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- The supplied fraction field receives each original principal stage injectively. -/
theorem fractionProjection_injective (s : Finset R⁰) :
    Function.Injective (projection R⁰ K s) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (stage R⁰ s)
    (M := Submonoid.powers (denominator R⁰ s)) (projection R⁰ K s)
  intro x hx
  rw [projection_algebraMap] at hx
  have hx0 : x = 0 := (IsFractionRing.injective R K) (by simpa only [map_zero] using hx)
  simp only [hx0, map_zero]

instance fractionStage_domain (s : Finset R⁰) : IsDomain (stage R⁰ s) :=
  Localization.Away.isDomain (nonZeroDivisors.ne_zero (denominator_mem R⁰ s))

instance fractionProjection_dominant (s : Finset R⁰) :
    IsDominant (Spec.map (CommRingCat.ofHom (projection R⁰ K s))) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (projection R⁰ K s))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (fractionProjection_injective R K s)]
  exact bot_le

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Smooth p]

omit [IsDomain R] in
/-- The actual generic projection to a principal stage is dense, not asserted surjective. -/
theorem fractionBaseChangeProjection_dominant (s : Finset R⁰) :
    IsDominant (baseChangeProjection R⁰ K p (op s)) := by
  constructor
  exact Hom.denseRange_of_open_pullback _ _ _ _
    (baseChangeProjection_isPullback R⁰ K p s)
    (pullback.fst (Spec.algebraMap R (stage R⁰ s)) p).isOpenMap
    (Spec.map (CommRingCat.ofHom (projection R⁰ K s))).denseRange

omit [IsDomain R] in
/-- Density also holds for the same finite-etale covering source. -/
theorem fractionCoverProjection_dominant (s : Finset R⁰)
    (C : FiniteEtale ((baseChangeDiagram R⁰ p).obj (op s))) :
    IsDominant (pullback.fst C.obj.hom (baseChangeProjection R⁰ K p (op s))) := by
  constructor
  have H := (IsPullback.of_hasPullback C.obj.hom
    (baseChangeProjection R⁰ K p (op s))).paste_vert
      (baseChangeProjection_isPullback R⁰ K p s)
  exact Hom.denseRange_of_open_pullback _ _ _ _ H
    (C.obj.hom ≫ pullback.fst (Spec.algebraMap R (stage R⁰ s)) p).isOpenMap
    (Spec.map (CommRingCat.ofHom (projection R⁰ K s))).denseRange

omit [IsDomain R] in
/-- Integrality of the original generic cover reflects to the unchanged
stage cover. Its reducedness follows from the original integral target. -/
theorem fractionCover_isIntegral_of_generic [IsIntegral X] [IsLocallyNoetherian X]
    (s : Finset R⁰) (C : FiniteEtale ((baseChangeDiagram R⁰ p).obj (op s)))
    [IsIntegral ((FiniteEtale.baseChange (baseChangeProjection R⁰ K p (op s))).obj C).obj.left] :
    IsIntegral C.obj.left := by
  let b := baseChangeProjection R⁰ K p (op s)
  let : IsIntegral (pullback C.obj.hom b) :=
    inferInstanceAs (IsIntegral ((FiniteEtale.baseChange b).obj C).obj.left)
  let : Nonempty C.obj.left := Nonempty.map (pullback.fst C.obj.hom b) inferInstance
  let : Nonempty ((baseChangeDiagram R⁰ p).obj (op s)) :=
    Nonempty.map C.obj.hom inferInstance
  let : IsOpenImmersion ((schemeDiagram R⁰ p).obj (op s)).hom :=
    inferInstanceAs (IsOpenImmersion (pullback.snd (Spec.algebraMap R (stage R⁰ s)) p))
  let : IsIntegral ((baseChangeDiagram R⁰ p).obj (op s)) :=
    isIntegral_of_isOpenImmersion ((schemeDiagram R⁰ p).obj (op s)).hom
  let : IsLocallyNoetherian ((baseChangeDiagram R⁰ p).obj (op s)) :=
    LocallyOfFiniteType.isLocallyNoetherian ((schemeDiagram R⁰ p).obj (op s)).hom
  let : IsReduced C.obj.left := Etale.isReduced C.obj.hom
  let : IsDominant (pullback.fst C.obj.hom b) := fractionCoverProjection_dominant R K p s C
  exact LocalRing.GenericFiber.integral_of_dense_integral_source (pullback.fst C.obj.hom b)

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
