/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesClosedFiberGeneric
public import Aglib.RingTheory.Smooth.SplitSectionAugmentation
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # The original completion point belongs to the fibrewise dense open

The map of actual coefficient fibres is the base change of the original flat
map. Its original power-series point is therefore component-generic. For an
irreducible target fibre it belongs to every nonempty fibre open. In particular,
closed-fibre membership is a conclusion, not an input, for the original smooth
section completion. No normalization or alternative prime is chosen here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing MvPowerSeries

namespace AlgebraicGeometry.Scheme

universe u

namespace PowerSeriesClosedFiber

variable (σ : Type) (R : Type u) [CommRing R] [IsLocalRing R]
  [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (g : Spec (.of (MvPowerSeries σ R)) ⟶ X)
  (hg : g ≫ f = Spec.map (CommRingCat.ofHom (C : R →+* MvPowerSeries σ R)))

local notation "c" => Spec.map (CommRingCat.ofHom (C : R →+* MvPowerSeries σ R))

/-- The original map of the literal coefficient fibres. -/
def map : (c).fiber (closedPoint R) ⟶ f.fiber (closedPoint R) :=
  pullback.lift ((c).fiberι (closedPoint R) ≫ g)
    ((c).fiberToSpecResidueField (closedPoint R)) (by
      rw [Category.assoc, hg]
      exact (c).fiber_fac (closedPoint R))

omit [IsNoetherianRing R] in
@[reassoc (attr := simp)]
theorem map_ι : map σ R f g hg ≫ f.fiberι (closedPoint R) =
    (c).fiberι (closedPoint R) ≫ g := pullback.lift_fst _ _ _

omit [IsNoetherianRing R] in
@[reassoc (attr := simp)]
theorem map_toSpecResidueField :
    map σ R f g hg ≫ f.fiberToSpecResidueField (closedPoint R) =
      (c).fiberToSpecResidueField (closedPoint R) := pullback.lift_snd _ _ _

omit [IsNoetherianRing R] in
/-- This exact fibre map, not an isomorphic replacement, is a base change of g. -/
theorem map_isPullback : IsPullback (map σ R f g hg)
    ((c).fiberι (closedPoint R)) (f.fiberι (closedPoint R)) g := by
  apply IsPullback.of_right (h₁₂ := f.fiberToSpecResidueField (closedPoint R))
  · rw [map_toSpecResidueField, hg]
    exact (IsPullback.of_hasPullback c
      ((Spec (.of R)).fromSpecResidueField (closedPoint R))).flip
  · exact map_ι σ R f g hg
  · exact (IsPullback.of_hasPullback f
      ((Spec (.of R)).fromSpecResidueField (closedPoint R))).flip

/-- Flatness carries the original mR power-series point to a component-generic
point of the actual target closed fibre. -/
theorem map_generic [Flat g] :
    map σ R f g hg (powerSeriesClosedFiberGenericPoint σ R) ∈
      genericPoints (f.fiber (closedPoint R)) := by
  let : Flat (map σ R f g hg) :=
    MorphismProperty.of_isPullback (map_isPullback σ R f g hg).flip inferInstance
  exact powerSeriesClosedFiberGenericPoint_map_flat σ R (map σ R f g hg)

include hg in
/-- Nonemptiness of the actual fibre open supplies original mR membership. -/
theorem image_mem_open [Flat g] [IrreducibleSpace (f.fiber (closedPoint R))]
    (U : X.Opens) (hU : (f.fiberι (closedPoint R) ⁻¹' (U : Set X)).Nonempty) :
    g (powerSeriesClosedFiberPoint σ R) ∈ U := by
  have hη := map_generic σ R f g hg
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hη
  have hm : map σ R f g hg (powerSeriesClosedFiberGenericPoint σ R) ∈
      f.fiberι (closedPoint R) ⁻¹' (U : Set X) := by
    rw [hη]
    exact ((genericPoint_spec (f.fiber (closedPoint R))).mem_open_set_iff
      (U.isOpen.preimage (f.fiberι (closedPoint R)).continuous)).mpr
        (by simpa only [Set.univ_inter] using hU)
  change f.fiberι (closedPoint R)
    (map σ R f g hg (powerSeriesClosedFiberGenericPoint σ R)) ∈ U at hm
  have he := congrArg (fun k => k (powerSeriesClosedFiberGenericPoint σ R))
    (map_ι σ R f g hg)
  simp only [Hom.comp_apply, powerSeriesClosedFiberGenericPoint_image] at he
  exact he ▸ hm

end PowerSeriesClosedFiber

variable {R B : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing B] [Algebra R B] [IsNoetherianRing B]
  (ε : B →ₐ[R] R) (σ : Type)
  (e : MvPowerSeries σ R ≃ₐ[R] AdicCompletion (RingHom.ker ε.toRingHom) B)

/-- The original coefficient-to-completion map in the given power-series
coordinates. This uses the same section ideal and the same completion. -/
def smoothCompletionPowerSeriesMap : B →ₐ[R] MvPowerSeries σ R :=
  e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R B
    (AdicCompletion (RingHom.ker ε.toRingHom) B))

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- The actual completion map is flat, without normality of R or B. -/
theorem smoothCompletionPowerSeriesMap_flat :
    (smoothCompletionPowerSeriesMap ε σ e).toRingHom.Flat :=
  (RingHom.flat_algebraMap_iff.mpr
    (inferInstance : Module.Flat B (AdicCompletion (RingHom.ker ε.toRingHom) B))).comp
      (.of_bijective e.symm.bijective)

/-- The actual closed-fibre open contains the original power-series point in
section-completion coordinates. Only fibre irreducibility and nonemptiness
are required; no membership assumption is introduced. -/
theorem smoothCompletionPowerSeriesPoint_mem_open
    [IrreducibleSpace ((Spec.algebraMap R B).fiber (closedPoint R))]
    (U : (Spec (.of B)).Opens)
    (hU : ((Spec.algebraMap R B).fiberι (closedPoint R) ⁻¹'
      (U : Set (Spec (.of B)))).Nonempty) :
    Spec.map (CommRingCat.ofHom (smoothCompletionPowerSeriesMap ε σ e).toRingHom)
      (powerSeriesClosedFiberPoint σ R) ∈ U := by
  let φ := smoothCompletionPowerSeriesMap ε σ e
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : Flat g := Flat.SpecMap_iff.mpr (smoothCompletionPowerSeriesMap_flat ε σ e)
  have hg : g ≫ Spec.algebraMap R B =
      Spec.map (CommRingCat.ofHom (C : R →+* MvPowerSeries σ R)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact φ.commutes r
  exact PowerSeriesClosedFiber.image_mem_open σ R (Spec.algebraMap R B) g hg U hU

end AlgebraicGeometry.Scheme
