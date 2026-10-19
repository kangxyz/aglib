/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.BaseChangeLocus
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Aglib.RingTheory.Spectrum.Prime.Bijectivity

/-!
# Vanishing of proper cohomology from vanishing on every fibre

Let `R` be a Noetherian ring, `f : X ⟶ Spec R` proper and `M` a coherent `𝒪_X`-module that is
relatively flat over `R`. If for some degree `q` the fibre cohomology `H^q(X_t, M_t)` vanishes
at every point `t` of `Spec R`, then `H^q(X, M) = 0`
(`subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper`). Here `X_t` is the fibre
product `X ×_{Spec R} Spec κ(t)` and `M_t` the pullback of `M` along its first projection.

The residue-field base-change map in degree `q` has zero target, so it is surjective; by
cohomology and base change on a basic-open neighbourhood
(`exists_basicOpen_moduleCohomologyBaseChangeMap_isIso_of_epi_residue_of_proper`) it is an
isomorphism at `t`, so `κ(t) ⊗_R H^q(X, M) = 0`. The cohomology is a finite `R`-module
(`moduleCohomology_finite_of_proper`), so Nakayama's lemma at every prime
(`Module.subsingleton_of_subsingleton_residueField_tensorProduct`) gives `H^q(X, M) = 0`.
This is the vanishing case of cohomology and base change, used in the proof of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Thm 4.3 (ii), pp. 22–23, for
the flat family `F_T`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}

/-- **Fibrewise vanishing gives vanishing** for a coherent relatively flat coefficient on a
proper scheme over a Noetherian ring. -/
theorem subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (hfib : ∀ t : PrimeSpectrum R, Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap R t.asIdeal.ResidueField))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (algebraMap R t.asIdeal.ResidueField))))).obj M)) q)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let := moduleCohomologyModuleOfHom X α M q
  have : Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) :=
    moduleCohomology_finite_of_proper R f M hM q
  refine Module.subsingleton_of_subsingleton_residueField_tensorProduct (R := R) fun t => ?_
  have := hfib t
  have hres : Epi (moduleCohomologyBaseChangeMap f (algebraMap R t.asIdeal.ResidueField) M q) :=
    (ModuleCat.isZero_of_subsingleton _).epi _
  obtain ⟨r, hr, hiso⟩ :=
    exists_basicOpen_moduleCohomologyBaseChangeMap_isIso_of_epi_residue_of_proper f M hM hflat
      q t hres
  have hu : IsUnit (algebraMap R t.asIdeal.ResidueField r) :=
    isUnit_iff_ne_zero.mpr fun h0 => hr (Ideal.algebraMap_residueField_eq_zero.mp h0)
  have h := hiso t.asIdeal.ResidueField
    (IsLocalization.Away.lift (S := Localization.Away r) r hu)
  rw [IsLocalization.Away.lift_comp] at h
  have hz : Subsingleton ((ModuleCat.extendScalars (algebraMap R t.asIdeal.ResidueField)).obj
      (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q))) :=
    ModuleCat.subsingleton_of_isZero
      ((ModuleCat.isZero_of_subsingleton _).of_iso (@asIso _ _ _ _ _ h))
  exact (ModuleCat.extendScalarsAlgebraObjIso R t.asIdeal.ResidueField
    (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q))).toLinearEquiv.toEquiv.symm
    |>.subsingleton

end AlgebraicGeometry.Scheme.Cohomology
