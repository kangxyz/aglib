/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.Separable

/-!
# Function fields of finite dominant affine charts

The inverse image of a nonempty affine chart under a finite dominant morphism of
integral schemes is nonempty. Its chart algebra, generic germ compatibility and
fraction-field scalar towers use the actual section and generic stalk maps.

The declarations in `Scheme.Hom.LocalNormAlgebra` are extracted from
`Morphisms/Finite/LocalNormAlgebra.lean` without changing their public interfaces;
the original module imports this lower provider.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra

universe u
variable {X Y : Scheme.{u}} [hX : IsIntegral X] [hY : IsIntegral Y]
variable (f : X ⟶ Y) [hDominant : IsDominant f] [hFinite : IsFinite f]
variable (U : Y.Opens) (hU : IsAffineOpen U)

instance preimage_nonempty [Nonempty U] : Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ∈ U
  rw [Scheme.map_genericPoint_of_isDominant X f]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using ‹Nonempty U›)

/-- The target-chart algebra on functions of the entire inverse-image chart, induced by the
actual map f.app U. -/
@[instance_reducible]
def chartAlgebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra

attribute [local instance] chartAlgebra

omit hFinite in
/-- Generic restriction commutes with pullback on the entire inverse-image chart. -/
-- Retain finiteness of the original finite dominant norm morphism; the germ identity alone only
-- uses its actual dominant function-field pullback.
@[nolint unusedArguments]
theorem fieldMap_germ
    [IsFinite f]
    [Nonempty U] :
    Y.germToFunctionField U ≫ CommRingCat.ofHom (Scheme.functionFieldMap f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  change Y.presheaf.germ U _ _ ≫
    (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _) = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes,
    Scheme.Hom.germ_stalkMap]

theorem chartMap_injective [Nonempty U] : Function.Injective (f.app U) := by
  intro a b hab
  apply Y.germToFunctionField_injective U
  apply (Scheme.functionFieldMap f).injective
  have h := congrArg (fun g : Γ(Y, U) ⟶ X.functionField => (g a, g b))
    (fieldMap_germ f U)
  exact (congrArg Prod.fst h).trans ((congrArg (X.germToFunctionField (f ⁻¹ᵁ U)) hab).trans
    (congrArg Prod.snd h).symm)

include hU in
omit hX hY hDominant in
-- Retain the integral-source, integral-target and dominant-map guards of the original
-- norm-chart interface; chart finiteness itself follows from finite_app.
@[nolint unusedArguments]
theorem chart_finite
    [IsIntegral X]
    [IsIntegral Y]
    [IsDominant f]
    : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU

end AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra

namespace AlgebraicGeometry.Scheme.Hom

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsDominant f]
variable (U : Y.Opens) [Nonempty U]

/-- The target-chart algebra on the source function field, using the actual generic
stalk map after restriction of target sections. -/
@[instance_reducible]
def chartFunctionFieldAlgebra : Algebra Γ(Y, U) X.functionField :=
  ((Scheme.functionFieldMap f).comp (Y.germToFunctionField U).hom).toAlgebra

/-- The actual target function field is an intermediate scalar field for the chart. -/
theorem chartFunctionField_scalarTower :
    let := Scheme.functionFieldMapAlgebra f
    let := f.chartFunctionFieldAlgebra U
    IsScalarTower Γ(Y, U) Y.functionField X.functionField := by
  let := Scheme.functionFieldMapAlgebra f
  let := f.chartFunctionFieldAlgebra U
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- Restriction through the entire source chart gives the same scalar action as
restriction through the actual target function field. -/
theorem chartFunctionField_source_scalarTower [IsFinite f] :
    let := LocalNormAlgebra.chartAlgebra f U
    let := f.chartFunctionFieldAlgebra U
    IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField := by
  let := LocalNormAlgebra.chartAlgebra f U
  let := f.chartFunctionFieldAlgebra U
  apply IsScalarTower.of_algebraMap_eq'
  exact congrArg CommRingCat.Hom.hom (LocalNormAlgebra.fieldMap_germ f U)

/-- The canonical target fraction-ring action on the actual source function field.
The equivalence is induced by the actual generic germ, not by a chosen field model. -/
@[instance_reducible]
def chartFractionRingFunctionFieldAlgebra (hU : IsAffineOpen U) :
    Algebra (FractionRing Γ(Y, U)) X.functionField := by
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  exact ((Scheme.functionFieldMap f).comp
    (FractionRing.algEquiv Γ(Y, U) Y.functionField).toRingHom).toAlgebra

/-- The canonical fraction-ring action extends the actual target-chart action. -/
theorem chartFractionRingFunctionField_scalarTower (hU : IsAffineOpen U) :
    let := f.chartFunctionFieldAlgebra U
    let := f.chartFractionRingFunctionFieldAlgebra U hU
    IsScalarTower Γ(Y, U) (FractionRing Γ(Y, U)) X.functionField := by
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  let := f.chartFunctionFieldAlgebra U
  let := f.chartFractionRingFunctionFieldAlgebra U hU
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact congrArg (Scheme.functionFieldMap f)
    ((FractionRing.algEquiv Γ(Y, U) Y.functionField).commutes a).symm

/-- Separability of the actual function-field pullback gives separability over the
canonical fraction ring of every nonempty affine target chart. -/
theorem chartFractionRingFunctionField_isSeparable (hU : IsAffineOpen U)
    (hsep : letI := Scheme.functionFieldMapAlgebra f
      Algebra.IsSeparable Y.functionField X.functionField) :
    let := f.chartFractionRingFunctionFieldAlgebra U hU
    Algebra.IsSeparable (FractionRing Γ(Y, U)) X.functionField := by
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  let := Scheme.functionFieldMapAlgebra f
  let := f.chartFractionRingFunctionFieldAlgebra U hU
  let : Algebra.IsSeparable Y.functionField X.functionField := hsep
  apply Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv Γ(Y, U) Y.functionField).symm.toRingEquiv
    (RingEquiv.refl X.functionField)
  ext a
  exact congrArg (Scheme.functionFieldMap f)
    ((FractionRing.algEquiv Γ(Y, U) Y.functionField).apply_symm_apply a)

end AlgebraicGeometry.Scheme.Hom
