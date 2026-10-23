/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Separated
public import Aglib.AlgebraicGeometry.Cohomology.Affine.SheafCohomology
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenPullback
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Aglib.RingTheory.Support.FiniteLengthDetection
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Finite-length proper cohomology over an isolated non-isomorphism

Over a Noetherian local ring, a proper morphism that is an actual isomorphism
over the punctured spectrum has finite-length positive cohomology for every
coherent module sheaf. The cohomology and its structural ring action are the
original ones. Localization at a nonclosed prime is flat; its actual base
change is affine, so flat base change and affine acyclicity put the support
of positive cohomology at the closed point.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

/-- The actual complement of the closed point of a local affine scheme. -/
def localPuncturedSpectrum (R : Type u) [CommRing R] [IsLocalRing R] :
    (Spec (CommRingCat.of R)).Opens :=
  ⟨{IsLocalRing.closedPoint R}ᶜ,
    (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩

@[simp]
theorem mem_localPuncturedSpectrum (R : Type u) [CommRing R] [IsLocalRing R]
    (p : PrimeSpectrum R) :
    p ∈ localPuncturedSpectrum R ↔ p ≠ IsLocalRing.closedPoint R := Iff.rfl

private theorem range_specMap_localization_subset_localPuncturedSpectrum
    (R : Type u) [CommRing R] [IsLocalRing R] (p : PrimeSpectrum R)
    (hp : p ≠ IsLocalRing.closedPoint R) :
    Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.AtPrime p.asIdeal)))) ⊆ localPuncturedSpectrum R := by
  rintro _ ⟨x, rfl⟩
  change PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) x ∈
    localPuncturedSpectrum R
  apply (mem_localPuncturedSpectrum R _).mpr
  intro he
  apply hp
  have hle : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) x ≤ p :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime p.asIdeal) p.asIdeal x).property
  rw [he] at hle
  exact le_antisymm (show p ≤ IsLocalRing.closedPoint R from le_top) hle

namespace Cohomology

/-- Original positive cohomology of a coherent coefficient on a proper local
scheme has finite length when the original morphism is an isomorphism over
the actual punctured spectrum. No relative flatness of the coefficient is
required. -/
theorem moduleCohomology_isFiniteLength_of_proper_of_isIso_puncturedSpectrum
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hiso : IsIso (f ∣_ localPuncturedSpectrum R))
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (q : ℕ) (hq : 0 < q) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    IsFiniteLength R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom X α M (n + 1)
  let : Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1)) :=
    moduleCohomology_finite_of_proper R f M hM (n + 1)
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let : IsIso (f ∣_ localPuncturedSpectrum R) := hiso
  apply Module.isFiniteLength_of_support_subset_closedPoint
  intro p hp
  by_cases hpc : p = IsLocalRing.closedPoint R
  · subst p
    change (IsLocalRing.maximalIdeal R : Set R) ⊆ (IsLocalRing.maximalIdeal R : Set R)
    exact Set.Subset.rfl
  · suffices hloc : Subsingleton
        (LocalizedModule p.asIdeal.primeCompl
          (Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1))) by
      exact False.elim ((Module.notMem_support_iff.mpr hloc) hp)
    let Rp := Localization.AtPrime p.asIdeal
    let σ := algebraMap R Rp
    let t := Spec.map (CommRingCat.ofHom σ)
    let j := pullback.fst f t
    let g := pullback.snd f t
    let N := (Scheme.Modules.pullback j).obj M
    let : IsIso g := Hom.isIso_pullback_of_range_subset f
      (localPuncturedSpectrum R) t
      (range_specMap_localization_subset_localPuncturedSpectrum R p hpc)
    let : IsAffine (pullback f t) := IsAffine.of_isIso g
    let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (pullback f t) N) (n + 1)) :=
      subsingleton_moduleAddSheafH_of_isAffine N n
    let : IsIso (moduleCohomologyBaseChangeMap f σ M (n + 1)) :=
      moduleCohomologyBaseChangeMap_isIso_of_isSeparated f σ
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Rp p.asIdeal.primeCompl))
        M (n + 1)
    let : Subsingleton ((ModuleCat.extendScalars σ).obj
        (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1)))) :=
      ModuleCat.subsingleton_of_isZero
        ((ModuleCat.isZero_of_subsingleton _).of_iso
          (asIso (moduleCohomologyBaseChangeMap f σ M (n + 1))))
    let : Subsingleton (Rp ⊗[R] Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1)) :=
      (ModuleCat.extendScalarsAlgebraObjIso R Rp
        (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1)))).toLinearEquiv.toEquiv.symm
        |>.subsingleton
    exact (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl
      (Sheaf.H.{u + 1} (moduleAddSheaf X M) (n + 1))).toEquiv.subsingleton

end Cohomology

end AlgebraicGeometry.Scheme
