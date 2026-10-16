/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Stalks
public import Aglib.AlgebraicGeometry.Stalk.IntegralExtension

/-!
# Stalk dimensions of generic finite-etale normalization

Every actual normalization stalk has the dimension of the base stalk at its structural
image, under the stated integral, locally Noetherian and normal-stalk hypotheses.
The proof uses integral going-down field factors and imposes no dimension bound.

## Extraction basis

Existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/LocalDimension.lean`, source revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`6a2e59621ddd5980c88c33794972285f67afb285c25e14ed51edf92ea74092ab`.
The source statements, binder universes, hypotheses and chosen maps are retained.
Direct Mathlib carriers/maps replace the recorded source wrappers; source-token correspondence
and those definitional substitutions are separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

universe u

/-- Actual finite-etale generic normalization charts have the same stalk
dimensions as the base. The chosen factor is obtained from the given point. -/
theorem integralClosureSpec_stalk_dimension
    (R K A : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
    (x : PrimeSpectrum (integralClosure R A)) :
    ringKrullDim ((Spec (.of (integralClosure R A))).presheaf.stalk x) =
      ringKrullDim ((Spec (.of R)).presheaf.stalk
        (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R A))) x)) := by
  obtain ⟨ι, hι, L, hL, hKL, e, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  letI := hι
  letI := hL
  letI := hKL
  letI (i : ι) : Algebra R (L i) :=
    (algebraMap K (L i)).comp (algebraMap R K) |>.toAlgebra
  haveI (i : ι) : IsScalarTower R K (L i) := IsScalarTower.of_algebraMap_eq' rfl
  haveI (i : ι) : Module.Finite K (L i) := (hfin i).1
  haveI (i : ι) : Algebra.IsSeparable K (L i) := (hfin i).2
  haveI (i : ι) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.finite R K (L i) _
  haveI (i : ι) : FaithfulSMul R (L i) :=
    (faithfulSMul_iff_algebraMap_injective R (L i)).mpr
      ((algebraMap K (L i)).injective.comp (IsFractionRing.injective R K))
  haveI (i : ι) : FaithfulSMul R (integralClosure R (L i)) := inferInstance
  haveI (i : ι) : Algebra.HasGoingDown R (integralClosure R (L i)) := inferInstance
  let eB := _root_.integralClosure.equivPi R A L (e.restrictScalars R)
  exact ringKrullDim_stalk_Spec_eq_of_piEquiv R (integralClosure R A)
    (fun i => integralClosure R (L i)) eB x

section Global

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  (C : Scheme.FiniteEtale (Spec X.functionField))

/-- Every actual normalization stalk has the same dimension as the target
stalk at its actual structural image, including split and empty covers. -/
theorem stalk_ringKrullDim (x : (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalization) :
    ringKrullDim (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalization).presheaf.stalk x)
        =
      ringKrullDim (X.presheaf.stalk ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
          X))).fromNormalization x)) := by
  let cov := (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalizationOpenCover
  let U : X.affineOpens := cov.idx x
  obtain ⟨y, hy⟩ := cov.covers x
  have hxU : x ∈ (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).fromNormalization ⁻¹ᵁ U.1 := by
    rw [Scheme.Hom.fromNormalization_preimage]
    exact ⟨y, hy⟩
  letI : Nonempty U.1 := ⟨⟨(C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).fromNormalization x,
      hxU⟩⟩
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  letI : IsIntegrallyClosed Γ(X, U.1) := isIntegrallyClosed_sections_of_isAffineOpen X U.1 U.2
  letI : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  let g := cov.f U
  haveI : IsOpenImmersion g := by dsimp [g]; infer_instance
  let p := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1)
    (integralClosure Γ(X, U.1) (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ
        U.1))))) y
  have hpoint : (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).fromNormalization (g y) =
      U.2.fromSpec p := by
    exact congrArg (fun f => f y) (isPullback_chart X C U.1 U.2).w
  have hs := integralClosureSpec_stalk_dimension Γ(X, U.1) X.functionField
    (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U.1)) y
  rw [← hy]
  calc
    ringKrullDim (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalization).presheaf.stalk (g
        y)) =
        ringKrullDim ((cov.X U).presheaf.stalk y) :=
      (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv.ringKrullDim
    _ = ringKrullDim ((Spec (.of Γ(X, U.1))).presheaf.stalk p) := hs
    _ = ringKrullDim (X.presheaf.stalk ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
        X))).fromNormalization (g y))) := by
      rw [hpoint]
      exact (asIso (U.2.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv.ringKrullDim.symm

end Global

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
