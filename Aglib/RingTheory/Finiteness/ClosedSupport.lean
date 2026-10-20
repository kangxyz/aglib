/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite modules with closed support

Localization of a module already finite over the base field remains
finite over that field. For a finite module over a finite-type field
algebra, maximality of every prime in its support gives field finiteness
through the actual annihilator quotient. Scalar towers remain the
displayed original ones.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.ProperCurveFiniteness`, R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. The native migration retains hypotheses,
universes, objects, maps and proof bodies.
-/

/- Component: Algebra. All declaration bodies preserved. -/
/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Finiteness/ClosedSupport.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`4437f209aeb7bb41e2af658bba24bcb9cd46a3552fd84f00ec1a0030da9efb6a`.
-/

@[expose] public section

noncomputable section
namespace Module
universe u v w
variable {K R M N : Type*} [Field K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]
  [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower K R N]

theorem localizedModule_finite (S : Submonoid R) (f : M →ₗ[R] N)
    [IsLocalizedModule S f] [Module.Finite K M] : Module.Finite K N := by
  let g := f.restrictScalars K
  let P := LinearMap.range g
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S f y
    let t : P →ₗ[K] P :=
      { toFun := fun z => ⟨(s : R) • z.val, by
          obtain ⟨x, hx⟩ := z.property
          exact ⟨(s : R) • x, by
            change f ((s : R) • x) = (s : R) • z.val
            rw [map_smul]; exact congrArg ((s : R) • ·) hx⟩⟩
        map_add' := by intros; ext; exact smul_add _ _ _
        map_smul' := by intros; ext; exact smul_comm _ _ _ }
    have ht : Function.Injective t := by
      intro a b hab
      apply Subtype.ext
      exact IsLocalizedModule.smul_injective f s (congrArg Subtype.val hab)
    have hts : Function.Surjective t := (LinearMap.injective_iff_surjective).mp ht
    obtain ⟨z, hz⟩ := hts ⟨g m, ⟨m, rfl⟩⟩
    have hzy : z.val = y := IsLocalizedModule.smul_injective f s
      ((congrArg Subtype.val hz).trans hs.symm)
    exact hzy ▸ z.property
  exact Module.Finite.of_surjective g hsurj

theorem finite_over_field_of_support_maximal [Algebra.FiniteType K R] [Module.Finite R M]
    (h : ∀ p ∈ Module.support R M, p.asIdeal.IsMaximal) : Module.Finite K M := by
  let I := Module.annihilator R M
  let := Module.quotientAnnihilator (R := R) (M := M)
  have : IsScalarTower R (R ⧸ I) M := (Module.isTorsionBySet_annihilator R M).isScalarTower
  have : IsScalarTower K (R ⧸ I) M := IsScalarTower.of_algebraMap_smul
    (fun k m => by change (algebraMap K R k) • m = k • m; exact algebraMap_smul R k m)
  have : Module.Finite (R ⧸ I) M := Module.Finite.of_restrictScalars_finite R (R ⧸ I) M
  have : Ring.KrullDimLE 0 (R ⧸ I) := Ring.KrullDimLE.mk₀ fun J hJ => by
    let := hJ
    have hp : Ideal.IsMaximal (J.comap (Ideal.Quotient.mk I)) := h
      ⟨J.comap (Ideal.Quotient.mk I), inferInstance⟩ (by
        rw [Module.support_eq_zeroLocus]
        change I ≤ J.comap (Ideal.Quotient.mk I)
        intro a ha
        change Ideal.Quotient.mk I a ∈ J
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
        exact J.zero_mem)
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (Ideal.Quotient.mk I)
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective) J hp
  have : Module.Finite K (R ⧸ I) := (Module.finite_iff_krullDimLE_zero K (R ⧸ I)).mpr inferInstance
  exact Module.Finite.trans (R ⧸ I) M
end Module

end
