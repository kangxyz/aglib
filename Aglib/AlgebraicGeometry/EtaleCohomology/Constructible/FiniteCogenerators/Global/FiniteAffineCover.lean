/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.RelativeAffine

/-! # Finite covers by the original Spec affine charts

The actual affine opens give the original spectrum charts with their original
fromSpec maps. Native finite-subcover extraction keeps a finite family of these
same charts, so original affine restriction FP applies to their actual maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

open AffineZariskiSite

/-- The actual original spectrum charts, indexed by the original affine opens. -/
def affineSpecCover (X : Scheme.{u}) : X.OpenCover where
  I₀ := X.AffineZariskiSite
  X U := Spec Γ(X, U.1)
  f U := U.2.fromSpec
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun U => IsAffineOpen.isOpenImmersion_fromSpec U.2⟩
    intro x
    let U : X.AffineZariskiSite := (directedCover X).idx x
    refine ⟨U, ?_⟩
    change x ∈ Set.range U.2.fromSpec
    rw [U.2.range_fromSpec]
    have hx : x ∈ Set.range U.1.ι := (directedCover X).covers x
    simpa only [Scheme.Opens.range_ι] using hx

/-- Native compactness chooses finitely many of these same actual Spec charts. -/
abbrev finiteAffineSpecCover (X : Scheme.{u}) [CompactSpace X] : X.OpenCover :=
  (affineSpecCover X).finiteSubcover

/-- The original selected affine open corresponding to the actual finite chart. -/
def finiteAffineSpecCoverOpen (X : Scheme.{u}) [CompactSpace X]
    (i : (finiteAffineSpecCover X).I₀) : X.AffineZariskiSite :=
  (affineSpecCover X).idx i.1

/-- Every chosen source is literally the original spectrum of its affine open. -/
theorem finiteAffineSpecCover_source (X : Scheme.{u}) [CompactSpace X]
    (i : (finiteAffineSpecCover X).I₀) :
    (finiteAffineSpecCover X).X i = Spec Γ(X, (finiteAffineSpecCoverOpen X i).1) := rfl

/-- Its original map is literally the original fromSpec chart map. -/
theorem finiteAffineSpecCover_map (X : Scheme.{u}) [CompactSpace X]
    (i : (finiteAffineSpecCover X).I₀) :
    (finiteAffineSpecCover X).f i = (finiteAffineSpecCoverOpen X i).2.fromSpec := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
