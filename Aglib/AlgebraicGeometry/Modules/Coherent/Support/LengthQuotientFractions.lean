/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.FiniteLength
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Fractions
public import Aglib.CategoryTheory.ExactCategory.MatrixDeflation
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Property
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.AlgebraicGeometry.Modules.Support

/-!
# Finite-length support quotients and open fractions

Source-only extraction from `R5Lab.KTheory.Quillen.LengthQuotientAndFractions` at R5Lab revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing objects, maps,
hypotheses, universes, proof bodies and mathematical namespaces are retained.
The original source correspondence remains in the supplying application module.
-/



/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.LengthQuotientFractions` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`dcd0b0e7e4f15033bd09fc291380fd1592439268753ae607f94f6e7d8f43efb7`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
attribute [local instance] Abelian.hasFiniteBiproducts
open ModuleCat.FiniteLengthFamilies CategoryTheory.Pi
namespace AlgebraicGeometry.Scheme.Modules.Stalk
universe u
variable (X : Scheme.{u}) [IsNoetherian X] (p : ℕ)

/-- The existing actual quotient stalk functor also has proved finite-length values. -/
theorem quotientStalks_length (M : StratumQuotient X p) :
    familyProperty (localRings X p) ((quotientStalks X p).obj M).obj := by
  obtain ⟨N, rfl⟩ := (Localization.Construction.objEquiv (nextSupport X p).isoModSerre).surjective M
  exact ⟨coherent_height_stalk_finiteLength X p N, stratumStalks_finite X p N⟩

/-- The faithful exact quotient comparison now lands in the genuine finite-length
family category, using the maintained quotient itself. -/
def quotientLengthStalks : _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (StratumQuotient X p))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Family (localRings X p))) where
  toFunctor := (familyProperty (localRings X p)).lift
    (quotientStalks X p ⋙ (finiteSupportProperty (localRings X p)).ι)
    (quotientStalks_length X p)
  additive := {
    map_add := by
      intros
      apply (familyProperty (localRings X p)).ι.map_injective
      exact (quotientStalks X p ⋙ (finiteSupportProperty (localRings X p)).ι).map_add }
  map_conflation S h := by
    let P := familyProperty (localRings X p)
    let F := (quotientStalksExact X p).comp
      (_root_.CategoryTheory.ObjectProperty.exactInclusion (finiteSupportProperty (localRings X p)))
    have he := F.map_conflation S h
    exact { exact := Functor.reflects_exact_of_faithful P.ι _ he.exact
            mono_f := P.ι.mono_of_mono_map he.mono_f
            epi_g := P.ι.epi_of_epi_map he.epi_g }

instance quotientLengthStalks_faithful : (quotientLengthStalks X p).toFunctor.Faithful := by
  change ((familyProperty (localRings X p)).lift
    (quotientStalks X p ⋙ (finiteSupportProperty (localRings X p)).ι)
    (quotientStalks_length X p)).Faithful
  infer_instance

theorem quotientLengthStalks_forget :
    (quotientLengthStalks X p).toFunctor ⋙
      (familyProperty (localRings X p)).ιOfLE (fun _ h => h.2) = quotientStalks X p := rfl

theorem quotientLengthStalks_fac : (nextSupport X p).isoModSerre.Q ⋙
    (quotientLengthStalks X p).toFunctor = (lengthStalks X p).toFunctor := by
  exact CategoryTheory.Functor.ext (fun _ => rfl)

section OpenFractions
variable {U : Scheme.{u}} [IsLocallyNoetherian U] (j : U ⟶ X) [IsOpenImmersion j]

omit [IsLocallyNoetherian U] in
/-- A coherent sheaf supported off an open has zero actual stalk at any point of that open. -/
theorem supportedAway_stalk_zero (M :
    Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X)
    (hM : Scheme.Modules.QuasiCoherent.finiteTypeSheavesSupportedAway j M)
    (x : X) (hx : x ∈ Set.range j) : IsZero ((coherentStalk X x).toFunctor.obj M) := by
  obtain ⟨y, rfl⟩ := hx
  apply (moduleStalk_isZero_iff X M.obj (j y)).mpr
  exact (Scheme.Modules.supportedAway_iff_stalks j M.obj).mp hM y

omit [IsLocallyNoetherian U] in
/-- A genuine open-restriction denominator is inverted by every stalk in the open. -/
theorem open_denominator_stalk_isIso {M N :
    Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X}
    (s : M ⟶ N) (hs :
        (Scheme.Modules.QuasiCoherent.finiteTypeSheavesSupportedAway
        j).isoModSerre s)
    (x : X) (hx : x ∈ Set.range j) : IsIso ((coherentStalk X x).toFunctor.map s) := by
  let F := (coherentStalk X x).toFunctor
  let : PreservesFiniteLimits F := by
    change PreservesFiniteLimits
      (Scheme.Modules.QuasiCoherent.finiteTypeSheavesToModules X ⋙
          Scheme.Modules.moduleStalk X x)
    infer_instance
  let : PreservesFiniteColimits F := by
    change PreservesFiniteColimits
      (Scheme.Modules.QuasiCoherent.finiteTypeSheavesToModules X ⋙
          Scheme.Modules.moduleStalk X x)
    infer_instance
  let : F.kernel.IsSerreClass := CategoryTheory.ObjectProperty.exactKernelSerre (coherentStalk X x)
  have h : F.kernel.isoModSerre s :=
    ⟨supportedAway_stalk_zero X j _ hs.1 x hx, supportedAway_stalk_zero X j _ hs.2 x hx⟩
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms] at h
  exact h

/-- The graph-fraction part of fullness is now encoded for the actual support
quotient: any morphism on an open containing every point of height at most p
has a genuine fraction inside CohAtLeast p with next-support denominator.
Spreading an arbitrary finite stalk family to such an open remains separate. -/
theorem coherent_support_fraction
    (hU : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ p → x ∈ Set.range j)
    (M N : CohAtLeast X p)
    (φ : (Scheme.Modules.QuasiCoherent.finiteTypeSheavesRestriction
        j).obj M.obj ⟶
      (Scheme.Modules.QuasiCoherent.finiteTypeSheavesRestriction
          j).obj N.obj) :
    ∃ (H : CohAtLeast X p) (s : H ⟶ M) (g : H ⟶ N),
      (nextSupport X p).isoModSerre s ∧
      (Scheme.Modules.QuasiCoherent.finiteTypeSheavesRestriction
          j).map s.hom ≫ φ =
        (Scheme.Modules.QuasiCoherent.finiteTypeSheavesRestriction
            j).map g.hom := by
  obtain ⟨H, s, g, hs, hφ⟩ :=
      Scheme.Modules.Coherent.coherent_exists_fraction j φ
  have hH : coherentAtLeast X p H := by
    intro x
    have hi := open_denominator_stalk_isIso X j s hs x.1 (hU x.1 (le_of_lt x.2))
    exact (Iso.isZero_iff (asIso ((coherentStalk X x.1).toFunctor.map s))).mpr (M.property x)
  let H' : CohAtLeast X p := ⟨H, hH⟩
  let s' : H' ⟶ M := ObjectProperty.homMk s
  let g' : H' ⟶ N := ObjectProperty.homMk g
  refine ⟨H', s', g', ?_, hφ⟩
  rw [stalkDenominator_iff]
  have hi : IsIso ((finiteSupportProperty (localRings X p)).ι.map
      ((stratumStalks X p).toFunctor.map s')) := by
    apply (isIso_pi_iff _).mpr
    intro x
    exact open_denominator_stalk_isIso X j s hs x.1 (hU x.1 x.2.le)
  exact (finiteSupportProperty (localRings X p)).fullyFaithfulι.isIso_of_isIso_map _
end OpenFractions

end AlgebraicGeometry.Scheme.Modules.Stalk
