/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.AdjoinLocalization
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Pushforward
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Sections

/-! # Actual finite-type module images for a global finite algebra

Quasicoherent module extension captures original affine sections. Their actual
images restrict compatibly, finite families generate finite-type algebras,
and original principal-open denominators clear by quasicoherence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

open Scheme.Modules
open Scheme.Modules.QuasiCoherent

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

/-- The actual affine direct-image structure module is quasicoherent. -/
theorem quasicoherent_pushforwardStructureSheaf [IsAffineHom f] :
    (pushforwardStructureSheaf f).IsQuasicoherent := by
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_unit Y
  exact Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f _

/-- Original affine sections are captured by actual finite-type subsheaf
inclusions into the original direct-image structure module. -/
theorem exists_finiteType_images_of_sections [IsAffineHom f]
    [CompactSpace X] [QuasiSeparatedSpace X] {J : Type u}
    (U : J → X.affineOpens) (x : ∀ j, Γ(Y, f ⁻¹ᵁ (U j).1)) :
    ∃ (M : J → FiniteTypeSheaves X)
      (i : ∀ j, (M j).obj ⟶ pushforwardStructureSheaf f),
      (∀ j, Mono (i j)) ∧ ∀ j, x j ∈ Set.range ((i j).app (U j).1) := by
  have : (pushforwardStructureSheaf f).IsQuasicoherent :=
    quasicoherent_pushforwardStructureSheaf f
  have h (j : J) := exists_finiteType_subsheaf_section
    (pushforwardStructureSheaf f) (U j) (x j)
  choose M i hi y hy using h
  exact ⟨M, i, hi, fun j => ⟨y j, hy j⟩⟩

variable {J : Type u} (M : J → X.Modules)
  (i : ∀ j, M j ⟶ pushforwardStructureSheaf f)

/-- The actual section images which generate the global finite algebra. -/
def sectionGenerators (U : X.Opens) : Set Γ(Y, f ⁻¹ᵁ U) :=
  ⋃ j, Set.range (fun m : Γ(M j, U) => (i j).app U m)

/-- Original restriction sends each original module-section generator to a
section of the same global finite-type subsheaf. -/
theorem sectionGenerators_restrict {U V : X.Opens} (a : V ⟶ U)
    {x : Γ(Y, f ⁻¹ᵁ U)} (hx : x ∈ sectionGenerators f M i U) :
    Y.presheaf.map (homOfLE (f.preimage_mono a.le)).op x ∈ sectionGenerators f M i V := by
  obtain ⟨j, m, rfl⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨j, (M j).presheaf.map a.op m, ?_⟩
  exact ConcreteCategory.congr_hom ((i j).mapPresheaf.naturality a.op) m

/-- Finitely many finite-type module images generate a finite-type algebra
on every original affine open. -/
theorem sectionGenerators_finiteType [Finite J]
    (hM : ∀ j, affineLocallyFiniteType X (M j)) (U : X.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    Algebra.FiniteType Γ(X, U.1)
      (Algebra.adjoin Γ(X, U.1) (sectionGenerators f M i U.1)) := by
  let := (f.app U.1).hom.toAlgebra
  have (j : J) : Module.Finite Γ(X, U.1) Γ(M j, U.1) :=
    finite_sections_of_affineLocallyFiniteType (M j) (hM j) U
  exact adjoin_iUnion_range_finiteType Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1)
    (fun j => Γ(M j, U.1)) (fun j => ((i j).val.app (op U.1)).hom)

/-- Quasicoherent module denominator clearing gives the original numerator
for every principal-open algebra generator. No target-algebra localization
compatibility is assumed. -/
theorem sectionGenerators_clear_power [∀ j, (M j).IsQuasicoherent]
    (U : X.affineOpens) (r : Γ(X, U.1))
    {x : Γ(Y, f ⁻¹ᵁ X.basicOpen r)}
    (hx : x ∈ sectionGenerators f M i (X.basicOpen r)) :
    ∃ (n : ℕ) (a : Γ(Y, f ⁻¹ᵁ U.1)), a ∈ sectionGenerators f M i U.1 ∧
      Y.presheaf.map (homOfLE (f.preimage_mono (X.basicOpen_le r))).op a =
        (f.app (X.basicOpen r)
          (X.presheaf.map (homOfLE (X.basicOpen_le r)).op r)) ^ n * x := by
  obtain ⟨j, m, rfl⟩ := Set.mem_iUnion.mp hx
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have : ((M j).restrict U.2.fromSpec).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.2.fromSpec (M j)
  obtain ⟨n, a, ha⟩ := AffineOpenSections.exists_power_mul_eq_restriction
    (M j) U.2 r m
  refine ⟨n, (i j).app U.1 a, Set.mem_iUnion.mpr ⟨j, a, rfl⟩, ?_⟩
  have hn := ConcreteCategory.congr_hom
    ((i j).mapPresheaf.naturality (homOfLE (X.basicOpen_le r)).op) a
  let ρ : Γ(X, X.basicOpen r) := X.presheaf.map (homOfLE (X.basicOpen_le r)).op r
  have h₁ : Y.presheaf.map (homOfLE (f.preimage_mono (X.basicOpen_le r))).op
      ((i j).app U.1 a) =
        (i j).app (X.basicOpen r) ((M j).presheaf.map (homOfLE (X.basicOpen_le r)).op a) :=
    hn.symm
  have h₂ : (i j).app (X.basicOpen r)
      ((M j).presheaf.map (homOfLE (X.basicOpen_le r)).op a) =
        (i j).app (X.basicOpen r) (ρ ^ n • m) :=
    congrArg (fun z : Γ(M j, X.basicOpen r) => (i j).app (X.basicOpen r) z) ha
  let y : Γ(Y, f ⁻¹ᵁ X.basicOpen r) := (i j).app (X.basicOpen r) m
  have h₃ := Scheme.Modules.Hom.app_smul (i j) (ρ ^ n) m
  change (i j).app (X.basicOpen r) (ρ ^ n • m) =
    f.app (X.basicOpen r) (ρ ^ n) * y at h₃
  rw [map_pow] at h₃
  exact h₁.trans (h₂.trans h₃)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
