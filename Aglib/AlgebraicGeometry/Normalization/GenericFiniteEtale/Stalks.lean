/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Finite
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Normal domain stalks of generic finite-etale normalization

For the stated integral, locally Noetherian base with integrally closed stalks, every
actual normalization stalk is an integrally closed domain. Finite field components and
their actual open immersions handle split and empty covers. No integral, connected or
nonempty total normalization is asserted.

## Extraction basis

Existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/NormalStalks.lean`, source revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`a419e35892f4760d1613685421bc25ce81ec13caca35a645dc1b8c91aa05c9f3`.
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

/-- The actual normalization chart of a finite-etale generic algebra has
normal DOMAIN stalks even when the original algebra is split or disconnected.
Finite field factors are derived from the ORIGINAL etale algebra. -/
theorem integralClosureSpec_stalk_normal_domain
    (R K A : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
    (x : PrimeSpectrum (integralClosure R A)) :
    IsIntegrallyClosed ((Spec (.of (integralClosure R A))).presheaf.stalk x) ∧
      IsDomain ((Spec (.of (integralClosure R A))).presheaf.stalk x) := by
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
  haveI (i : ι) : IsDomain (integralClosure R (L i)) := inferInstance
  haveI (i : ι) : IsIntegrallyClosed (integralClosure R (L i)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (K := K)
  let eB := _root_.integralClosure.equivPi R A L (e.restrictScalars R)
  exact isIntegrallyClosed_and_isDomain_stalk_Spec_of_piEquiv (integralClosure R A)
    (fun i => integralClosure R (L i)) eB.toRingEquiv x

section Global

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  (C : Scheme.FiniteEtale (Spec X.functionField))

/-- The actual constructed normalization is locally Noetherian, from its
accepted finite structural morphism over the actual locally Noetherian X. -/
instance instIsLocallyNoetherian : IsLocallyNoetherian ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
    X))).normalization) :=
  LocallyOfFiniteType.isLocallyNoetherian ((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
      X))).fromNormalization)

/-- Every actual normalization stalk is an integrally closed domain, including split and empty
    covers. -/
theorem stalk_normal_domain (x : (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalization) :
    IsIntegrallyClosed (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
        X))).normalization).presheaf.stalk x) ∧
      IsDomain (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalization).presheaf.stalk x)
          := by
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
  have hs := integralClosureSpec_stalk_normal_domain Γ(X, U.1) X.functionField
    (Γ(C.obj.left, (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ U.1)) y
  let g := cov.f U
  haveI : IsOpenImmersion g := by dsimp [g]; infer_instance
  haveI : IsIntegrallyClosed ((cov.X U).presheaf.stalk y) := hs.1
  haveI : IsDomain ((cov.X U).presheaf.stalk y) := hs.2
  rw [← hy]
  let ρ := (asIso (g.stalkMap y)).symm.commRingCatIsoToRingEquiv
  exact ⟨IsIntegrallyClosed.of_equiv ρ, ρ.symm.toMulEquiv.isDomain _⟩

/-- Every actual normalization stalk is integrally closed under the stated base premises. -/
instance instIsIntegrallyClosedStalk (x : (C.obj.hom ≫ (X.fromSpecStalk (genericPoint
    X))).normalization) :
    IsIntegrallyClosed (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
        X))).normalization).presheaf.stalk x) :=
  (stalk_normal_domain X C x).1

/-- Every actual normalization stalk is a domain under the stated base premises. -/
instance instIsDomainStalk (x : (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalization) :
    IsDomain (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalization).presheaf.stalk x) :=
  (stalk_normal_domain X C x).2

/-- The actual local-ring conditions at every normalization point. -/
theorem stalk_conditions (x : (C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalization) :
    IsIntegrallyClosed (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
        X))).normalization).presheaf.stalk x) ∧
      IsDomain (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint X))).normalization).presheaf.stalk x) ∧
        IsNoetherianRing (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
            X))).normalization).presheaf.stalk x) ∧
          IsLocalRing (((C.obj.hom ≫ (X.fromSpecStalk (genericPoint
              X))).normalization).presheaf.stalk x) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end Global

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
