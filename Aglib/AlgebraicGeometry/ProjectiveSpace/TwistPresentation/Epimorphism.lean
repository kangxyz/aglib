/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.TwistPresentation.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exactness
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Actual finite negative-twist epimorphisms

Surjectivity on original standard-chart sections detects epimorphisms between actual
quasicoherent modules on polynomial projective space. Applied to the extended finite local
generators, this gives an actual epimorphism from a native finite coproduct of negative
twists onto every affine-locally finite-type module, over an arbitrary commutative ring.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original standard-chart section maps detect a quasicoherent epimorphism. -/
theorem epi_of_coordinateSections_surjective
    {P M : (ProjectiveSpace R ι).Modules} [P.IsQuasicoherent] [M.IsQuasicoherent]
    (φ : P ⟶ M)
    (hφ : ∀ i, Function.Surjective (φ.val.app (op (coordinateOpen R ι i)))) : Epi φ := by
  let hU (i : ι) := isAffineOpen_coordinateOpen R ι i
  let Y (i : ι) := Spec Γ(ProjectiveSpace R ι, coordinateOpen R ι i)
  let a (i : ι) : Y i ⟶ ProjectiveSpace R ι := (hU i).fromSpec
  have hcover : ∀ x : ProjectiveSpace R ι, ∃ (i : ι) (y : Y i), a i y = x := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup (coordinateOpen R ι) by
      rw [iSup_coordinateOpen_eq_top]; trivial)
    have hx : x ∈ Set.range (a i) := by
      change x ∈ Set.range (hU i).fromSpec
      rw [(hU i).range_fromSpec]
      exact hi
    obtain ⟨y, hy⟩ := hx
    exact ⟨i, y, hy⟩
  have hepi (i : ι) : Epi ((Scheme.Modules.restrictFunctor (a i)).map φ) := by
    let φ' := (Scheme.Modules.restrictFunctor (a i)).map φ
    let : Epi (moduleSpecΓFunctor.map φ') := by
      apply (ModuleCat.epi_iff_surjective _).mpr
      intro y
      obtain ⟨x, hx⟩ := hφ i ((toSpecTopSectionsIso M (hU i)).inv y)
      refine ⟨(toSpecTopSectionsIso P (hU i)).hom x, ?_⟩
      have h := ConcreteCategory.congr_hom
        (toSpecTopSectionsIso_naturality P φ (hU i)) x
      change (toSpecTopSectionsIso M (hU i)).hom
          (φ.val.app (op (coordinateOpen R ι i)) x) =
        φ'.app ⊤ ((toSpecTopSectionsIso P (hU i)).hom x) at h
      rw [hx, Iso.inv_hom_id_apply] at h
      exact h.symm
    exact Scheme.Modules.epi_of_epi_globalSections _ φ'
  apply Preadditive.epi_of_isZero_cokernel
  apply Scheme.Modules.isZero_of_restrict_openCover Y a hcover
  intro i
  let := hepi i
  exact (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor (a i)).map φ)).of_iso
    (PreservesCokernel.iso (Scheme.Modules.restrictFunctor (a i)) φ)

/-- Finite coproducts of actual twists are quasicoherent over every base ring. -/
theorem twistingCoproduct_isQuasicoherent {I : Type u} [Finite I] (d : I → ℤ) :
    (∐ fun a => twistingSheaf R ι (d a)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (ProjectiveSpace R ι).ringCatSheaf).prop_coproduct
    (fun a => inferInstanceAs (twistingSheaf R ι (d a)).IsQuasicoherent)

/-- Every finite-type quasicoherent module is a quotient of a finite sum of one common
negative twist, whose degree can exceed any prescribed bound. The original quotient map
is surjective on sections of every standard chart. -/
theorem exists_uniformNegativeTwistEpimorphism [Finite ι]
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ ∃ (I : Type u) (_ : Finite I)
      (π : (∐ fun _ : I => twistingSheaf R ι (-(N : ℤ))) ⟶ M),
      Epi π ∧ ∀ i, Function.Surjective (π.val.app (op (coordinateOpen R ι i))) := by
  obtain ⟨N, hN, I, hI, φ, hφ⟩ :=
    exists_uniformNegativeTwistSectionsSurjective R ι M hM B
  let := hI
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M
    (fun A j _ => (hM A j).1)
  let : (∐ fun _ : I => twistingSheaf R ι (-(N : ℤ))).IsQuasicoherent :=
    twistingCoproduct_isQuasicoherent R ι (fun _ : I => -(N : ℤ))
  exact ⟨N, hN, I, hI, Sigma.desc φ, epi_of_coordinateSections_surjective R ι _ hφ, hφ⟩

/-- Every affine-locally finite-type module on finite-coordinate polynomial projective space
is a quotient of a native finite coproduct of negative twists. The original map is also
surjective on sections of every standard chart. -/
theorem exists_negativeTwistEpimorphism [Finite ι]
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    ∃ (I : Type u) (_ : Finite I) (N : I → ℕ)
      (π : (∐ fun a => twistingSheaf R ι (-(N a : ℤ))) ⟶ M),
      Epi π ∧ ∀ i, Function.Surjective (π.val.app (op (coordinateOpen R ι i))) := by
  obtain ⟨N, _, I, hI, π, hπ⟩ := exists_uniformNegativeTwistEpimorphism R ι M hM 0
  exact ⟨I, hI, fun _ => N, π, hπ⟩

end AlgebraicGeometry.ProjectiveSpace
