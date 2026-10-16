/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.GeometricFibre
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts
public import Aglib.RingTheory.Flat.PrincipalQuotient.Fibrewise
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Fibrewise regular line-bundle maps over arbitrary flat LFP bases

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, SHA-256
  `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The full original fibrewise-regular line-bundle interface, with the original
map, all algebraically closed field-valued fibres, and the actual zero scheme. -/
theorem mono_and_flat_zeroInclusion_comp_of_geometricFibreRegular : (∀ (X S : Scheme.{u}) (f : X ⟶
  S) (L : LineBundle X)
    (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)),
    Flat f → LocallyOfFinitePresentation f → GeometricFibreRegular f L φ →
      Mono φ ∧ Flat (Hom.zeroInclusion φ ≫ f)) := by
  intro X S f L φ hf hfp hφ
  let := hf
  let := hfp
  have hchart (V : S.affineOpens) (W : X.Opens)
      (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
      (U : X.affineOpens) (hUW : U.val ≤ W) (hUV : U.val ≤ f ⁻¹ᵁ V.val) :
      letI := (f.appLE V.val U.val hUV).hom.toAlgebra;
      IsSMulRegular Γ(X, U)
        (X.presheaf.map (homOfLE hUW).op (φ.app W (chartGenerator X L.val W e))) ∧
      Module.Flat Γ(S, V) (Γ(X, U) ⧸ Ideal.span
        {X.presheaf.map (homOfLE hUW).op (φ.app W (chartGenerator X L.val W e))}) := by
    let := (f.appLE V.val U.val hUV).hom.toAlgebra
    have : Module.Flat Γ(S, V) Γ(X, U) := f.flat_appLE V.property U.property hUV
    have : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
      f.finitePresentation_appLE V.property U.property hUV
    apply _root_.Algebra.regular_and_flat_of_fibre_regular
    intro p hp
    apply (_root_.Algebra.regular_geometric_fibre_iff p _).mp
    exact geometricFibreRegular_chart_regular f L φ hφ V U hUV W e hUW
      (AlgebraicClosure p.ResidueField)
  refine ⟨mono_of_relative_affine_chart_regular f L φ
    (fun V W e U hUW hUV ↦ (hchart V W e U hUW hUV).1), ?_⟩
  apply flat_zeroInclusion_comp_of_affine_chart_quotient_flat f L φ
  intro V hV W e U hUW hUV
  exact (hchart ⟨V, hV⟩ W e U hUW hUV).2

end AlgebraicGeometry.Scheme.Modules.Invertible
end
