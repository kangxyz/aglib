/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.StalkMap
public import Aglib.AlgebraicGeometry.Properties.Normal.GlobalSections
public import Aglib.RingTheory.IntegralClosure.TraceLattice
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Original field trace on affine sections of a finite morphism

For a finite dominant morphism of integral schemes with normal target,
field trace gives a linear map on the original sections over every
nonempty affine target open. The scalar map is the original `f.app`, and
the defining value equation uses the original section germs and the
original contravariant function-field map. The section algebra need not
be free. No separability, Noetherianity or normality of the source is
assumed.

These are the affine values needed to construct ordinary finite-morphism
trace on all opens; no global trace sheaf is asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [IsDominant f]

/-- A dominant morphism of integral schemes has nonempty inverse image
on every nonempty target open, witnessed by the original generic point. -/
theorem nonempty_preimage_of_isDominant (U : Y.Opens) [Nonempty U] :
    Nonempty (f ⁻¹ᵁ U) := by
  have hη : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ∈ U
  rwa [map_genericPoint_of_isDominant X f]

/-- Original section pullback on a nonempty open commutes with the same
generic-stalk map that defines the original function-field map. -/
theorem functionFieldMap_germ_app (U : Y.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ CommRingCat.ofHom (functionFieldMap f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  change Y.presheaf.germ U _ _ ≫
    (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap (genericPoint X)) = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes,
    Scheme.Hom.germ_stalkMap]

variable [IsFinite f]

/-- The original field trace of an affine section lies in the original
normal target section ring, with its original generic-value equation. -/
theorem exists_finiteAffineSectionTrace_value (hNormal : NormalStalks Y)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (s : Γ(X, f ⁻¹ᵁ U)) :
    letI : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
    letI := functionFieldMapAlgebra f
    ∃ a : Γ(Y, U), Y.germToFunctionField U a =
      Algebra.trace Y.functionField X.functionField
        (X.germToFunctionField (f ⁻¹ᵁ U) s) := by
  let : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
  let := functionFieldMapAlgebra f
  let C := Γ(Y, U)
  let D := Γ(X, f ⁻¹ᵁ U)
  let K := Y.functionField
  let L := X.functionField
  let : IsDomain C :=
    Function.Injective.isDomain _ (Y.germToFunctionField_injective U)
  let : IsDomain D :=
    Function.Injective.isDomain _ (X.germToFunctionField_injective (f ⁻¹ᵁ U))
  let : Algebra C D := (f.app U).hom.toAlgebra
  let : Module.Finite C D := f.finite_app U hU
  let : Algebra C L :=
    ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
  let : IsScalarTower C D L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower C K L := IsScalarTower.of_algebraMap_eq fun c =>
    (ConcreteCategory.congr_hom (functionFieldMap_germ_app f U) c).symm
  let : IsFractionRing C K := functionField_isFractionRing_of_isAffineOpen Y U hU
  let : IsFractionRing D L :=
    functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U) (hU.preimage f)
  let : IsIntegrallyClosed C :=
    Y.isIntegrallyClosed_sections U fun x => (hNormal x.val).2
  refine ⟨Algebra.TraceLattice.fieldTrace C D K L s, ?_⟩
  exact Algebra.TraceLattice.algebraMap_fieldTrace C D K L s

/-- The original field trace on a finite affine section algebra, linear
over the actual target section ring through the original `f.app` map. -/
def finiteAffineSectionTrace (hNormal : NormalStalks Y)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (f.app U).hom.toAlgebra
    Γ(X, f ⁻¹ᵁ U) →ₗ[Γ(Y, U)] Γ(Y, U) := by
  letI : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
  letI := functionFieldMapAlgebra f
  letI := (f.app U).hom.toAlgebra
  let t (s : Γ(X, f ⁻¹ᵁ U)) : Γ(Y, U) :=
    (exists_finiteAffineSectionTrace_value f hNormal U hU s).choose
  have ht (s : Γ(X, f ⁻¹ᵁ U)) : Y.germToFunctionField U (t s) =
      Algebra.trace Y.functionField X.functionField
        (X.germToFunctionField (f ⁻¹ᵁ U) s) :=
    (exists_finiteAffineSectionTrace_value f hNormal U hU s).choose_spec
  let gX := (X.germToFunctionField (f ⁻¹ᵁ U)).hom
  let gY := (Y.germToFunctionField U).hom
  let τ := Algebra.trace Y.functionField X.functionField
  refine { toFun := t, map_add' := ?_, map_smul' := ?_ }
  · intro s z
    apply Y.germToFunctionField_injective U
    calc
      gY (t (s + z)) = τ (gX (s + z)) := ht (s + z)
      _ = τ (gX s + gX z) := congrArg τ (map_add gX s z)
      _ = τ (gX s) + τ (gX z) := map_add τ (gX s) (gX z)
      _ = gY (t s) + gY (t z) := congrArg₂ (· + ·) (ht s).symm (ht z).symm
      _ = gY (t s + t z) := (map_add gY (t s) (t z)).symm
  · intro c s
    change t (f.app U c * s) = c * t s
    apply Y.germToFunctionField_injective U
    have hg := ConcreteCategory.congr_hom (functionFieldMap_germ_app f U) c
    change functionFieldMap f (Y.germToFunctionField U c) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U c) at hg
    calc
      gY (t (f.app U c * s)) = τ (gX (f.app U c * s)) := ht _
      _ = τ (gX (f.app U c) * gX s) := congrArg τ (map_mul gX _ _)
      _ = τ (functionFieldMap f (gY c) * gX s) := by rw [← hg]
      _ = gY c * τ (gX s) := by
        change τ ((gY c) • gX s) = (gY c) • τ (gX s)
        exact τ.map_smul _ _
      _ = gY c * gY (t s) := congrArg (gY c * ·) (ht s).symm
      _ = gY (c * t s) := (map_mul gY c (t s)).symm

/-- The value is exactly the trace in the original fraction-field
extension, tested by the original section-to-function-field maps. -/
theorem finiteAffineSectionTrace_germ (hNormal : NormalStalks Y)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (s : Γ(X, f ⁻¹ᵁ U)) :
    letI : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
    letI := functionFieldMapAlgebra f
    Y.germToFunctionField U (finiteAffineSectionTrace f hNormal U hU s) =
      Algebra.trace Y.functionField X.functionField
        (X.germToFunctionField (f ⁻¹ᵁ U) s) :=
  (exists_finiteAffineSectionTrace_value f hNormal U hU s).choose_spec

/-- The original generic-value equation uniquely specifies each affine
trace value; no independently chosen field identification is allowed. -/
theorem finiteAffineSectionTrace_unique (hNormal : NormalStalks Y)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (s : Γ(X, f ⁻¹ᵁ U)) (a : Γ(Y, U))
    (h : letI : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
      letI := functionFieldMapAlgebra f
      Y.germToFunctionField U a =
        Algebra.trace Y.functionField X.functionField
          (X.germToFunctionField (f ⁻¹ᵁ U) s)) :
    a = finiteAffineSectionTrace f hNormal U hU s :=
  Y.germToFunctionField_injective U
    (h.trans (finiteAffineSectionTrace_germ f hNormal U hU s).symm)

end AlgebraicGeometry.Scheme
