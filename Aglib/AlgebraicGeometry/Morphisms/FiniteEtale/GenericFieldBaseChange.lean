/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericFiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.Isomorphism

/-!
# Finite-etale restriction to an arbitrary fraction-field model

The generic-point triangle is already native
`Scheme.fromSpecStalk_genericPoint_naturality`. The theorem here composes the
native generic restriction with the actual isomorphism of fraction-field models.
The base ring is an integrally closed domain; Noetherianity is not required.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- Restriction to any specified fraction field of an integrally closed domain is full. -/
theorem fraction_baseChange_full (R F : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] :
    (baseChange (Spec.algebraMap R F)).Full := by
  let X := Spec (.of R)
  letI : Algebra R X.functionField :=
    (StructureSheaf.toStalk R (genericPoint X)).hom.toAlgebra
  letI : IsFractionRing R X.functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of R)
  letI : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) :=
    fun x => (Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec R x).1
  let e : X.functionField ≃ₐ[R] F := IsLocalization.algEquiv (nonZeroDivisors R) _ _
  let k : Spec (.of F) ⟶ Spec X.functionField := Spec.map (CommRingCat.ofHom e.toRingHom)
  letI : IsIso (CommRingCat.ofHom e.toRingHom) := by
    change IsIso e.toRingEquiv.toCommRingCatIso.hom
    infer_instance
  letI : IsIso k := by unfold k; infer_instance
  letI : (baseChange k).Full := baseChange_full_of_isIso k
  have hk : k ≫ (X.fromSpecStalk (genericPoint X)) = Spec.algebraMap R F := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X) = _
    rw [Spec.fromSpecStalk_eq', ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext a
    exact e.commutes a
  rw [← hk]
  exact Functor.Full.of_iso (baseChangeComp ((X.fromSpecStalk (genericPoint X))) k).symm

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/GenericFieldBaseChange.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 d461db587d320e150fe23052d2f5767ff1e0a272658ce257fbac1bd1416f38ab. -/
