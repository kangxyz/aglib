/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.SectionExtension.Bounds
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# Finite negative-twist generators on the original affine charts

An affine-locally finite-type quasicoherent module has finitely generated original section
modules on each standard chart. Extending these generators constructs a map from a native
finite coproduct of negative twists which is surjective on sections of every original chart.
The base ring is arbitrary; Noetherianity is not needed for this construction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)
  (M : (ProjectiveSpace R ι).Modules)

/-- Finite type on the canonical affine spectrum gives finite generation of the original
chart sections over the original chart ring. -/
theorem finite_coordinateSections
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (i : ι) :
    Module.Finite Γ(ProjectiveSpace R ι, coordinateOpen R ι i)
      Γ(M, coordinateOpen R ι i) := by
  let hU := isAffineOpen_coordinateOpen R ι i
  let : Module.Finite Γ(ProjectiveSpace R ι, coordinateOpen R ι i)
      Γ(M.restrict hU.fromSpec, ⊤) := by
    exact (hM _ hU.fromSpec).2
  exact Module.Finite.equiv (toSpecTopSectionsLinearEquiv M hU).symm

/-- A finite family of maps from one common negative twist, beyond any prescribed bound,
jointly surjects onto the original section module of every standard chart. -/
theorem exists_uniformNegativeTwistSectionsSurjective [Finite ι]
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ ∃ (I : Type u) (_ : Finite I)
      (φ : ∀ _ : I, twistingSheaf R ι (-(N : ℤ)) ⟶ M),
      ∀ i, Function.Surjective ((Sigma.desc φ).val.app (op (coordinateOpen R ι i))) := by
  classical
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M
    (fun A j _ => (hM A j).1)
  have hfg (i : ι) :
      (⊤ : Submodule Γ(ProjectiveSpace R ι, coordinateOpen R ι i)
        Γ(M, coordinateOpen R ι i)).FG := by
    let := finite_coordinateSections R ι M hM i
    exact Module.Finite.fg_top
  choose S hS using hfg
  let I : Type u := Σ i, (S i : Set Γ(M, coordinateOpen R ι i))
  choose k hk using fun a : I =>
    exists_negativeTwistHom_generator_eventually R ι M a.1 a.2.val
  let := Fintype.ofFinite I
  let N : ℕ := max B (Finset.univ.sup k)
  have hkN (a : I) : k a ≤ N :=
    (Finset.le_sup (f := k) (Finset.mem_univ a)).trans (le_max_right _ _)
  choose φ hφ using fun a : I => hk a N (hkN a)
  refine ⟨N, le_max_left _ _, I, inferInstance, φ, ?_⟩
  intro i
  change Function.Surjective ((Sigma.desc φ).val.app (op (coordinateOpen R ι i))).hom
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hS i]
  apply Submodule.span_le.mpr
  intro s hs
  let a : I := ⟨i, ⟨s, hs⟩⟩
  let F : I → (ProjectiveSpace R ι).Modules :=
    fun _ => twistingSheaf R ι (-(N : ℤ))
  let x : Γ(F a, coordinateOpen R ι i) :=
    (twistingSectionsEquiv R ι (-(N : ℤ)) i le_rfl).symm 1
  refine ⟨(Sigma.ι F a).val.app (op (coordinateOpen R ι i)) x, ?_⟩
  have h := congrArg (fun ψ : F a ⟶ M =>
    ψ.val.app (op (coordinateOpen R ι i)) x) (Sigma.ι_comp_desc φ a)
  change (Sigma.desc φ).val.app (op (coordinateOpen R ι i))
      ((Sigma.ι F a).val.app (op (coordinateOpen R ι i)) x) =
    (φ a).val.app (op (coordinateOpen R ι i)) x at h
  exact h.trans (hφ a)

/-- A finite family of actual negative-twist maps jointly surjects onto the section module
of every standard chart. The displayed source is the native finite coproduct of twists. -/
theorem exists_negativeTwistSectionsSurjective [Finite ι]
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    ∃ (I : Type u) (_ : Finite I) (N : I → ℕ)
      (φ : ∀ a, twistingSheaf R ι (-(N a : ℤ)) ⟶ M),
      ∀ i, Function.Surjective ((Sigma.desc φ).val.app (op (coordinateOpen R ι i))) := by
  obtain ⟨N, _, I, hI, φ, hφ⟩ :=
    exists_uniformNegativeTwistSectionsSurjective R ι M hM 0
  exact ⟨I, hI, fun _ => N, φ, hφ⟩

end AlgebraicGeometry.ProjectiveSpace
