/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverReflection
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverPreservation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Equality of finite-etale morphisms on a geometric fibre extends to an
actual open neighbourhood. A finite family can be treated simultaneously. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange fiberToFinite)

universe u
variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X)

theorem exists_open_map_eq_of_fiber_eq {Y Z : Scheme.FiniteEtale X} (f g : Y ⟶ Z)
    (h : (fiberToFinite s).map f = (fiberToFinite s).map g) :
    ∃ U : X.Opens, s default ∈ U ∧ (baseChange U.ι).map f = (baseChange U.ι).map g := by
  have hi : IsIso ((fiberToFinite s).map (equalizer.ι f g)) :=
    isIso_limit_cone_parallelPair_of_eq h
      (isLimitOfHasEqualizerOfPreservesLimit (fiberToFinite s) f g)
  obtain ⟨U, hu, he⟩ := exists_open_isIso_of_bijective_fiber s (equalizer.ι f g)
    (ConcreteCategory.bijective_of_isIso _)
  let := he
  refine ⟨U, hu, (cancel_epi ((baseChange U.ι).map (equalizer.ι f g))).mp ?_⟩
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun k => (baseChange U.ι).map k) (equalizer.condition f g)

/-- A single finite product and equalizer yields a common open neighbourhood;
there is no connectedness, rank, characteristic, or freeness hypothesis. -/
theorem exists_open_maps_eq_of_fiber_eq {I : Type} [Finite I]
    {Y : Scheme.FiniteEtale X} {Z : I → Scheme.FiniteEtale X} (f g : ∀ i, Y ⟶ Z i)
    (h : ∀ i, (fiberToFinite s).map (f i) = (fiberToFinite s).map (g i)) :
    ∃ U : X.Opens, s default ∈ U ∧
      ∀ i, (baseChange U.ι).map (f i) = (baseChange U.ι).map (g i) := by
  classical
  have hfg : (fiberToFinite s).map (Pi.lift f) = (fiberToFinite s).map (Pi.lift g) := by
    apply (isLimitOfPreserves (fiberToFinite s) (limit.isLimit (Discrete.functor Z))).hom_ext
    intro i
    change _ ≫ (fiberToFinite s).map (Pi.π Z i.as) =
      _ ≫ (fiberToFinite s).map (Pi.π Z i.as)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact (congrArg (fun k => (fiberToFinite s).map k) (Pi.lift_comp_π f i.as)).trans
      ((h i.as).trans (congrArg (fun k => (fiberToFinite s).map k)
        (Pi.lift_comp_π g i.as)).symm)
  obtain ⟨U, hu, he⟩ := exists_open_map_eq_of_fiber_eq s (Pi.lift f) (Pi.lift g) hfg
  refine ⟨U, hu, fun i => ?_⟩
  have hi := congrArg (fun q => q ≫ (baseChange U.ι).map (Pi.π Z i)) he
  rw [← Functor.map_comp, ← Functor.map_comp] at hi
  exact (congrArg (fun k => (baseChange U.ι).map k) (Pi.lift_comp_π f i)).symm.trans
    (hi.trans (congrArg (fun k => (baseChange U.ι).map k) (Pi.lift_comp_π g i)))

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 fdf1ace232aa1f5873c756c30b8230dfbca4f9b40bacecd9467c80b10373c7a3.
Definitions, hypotheses and universes are retained modulo native names. -/
