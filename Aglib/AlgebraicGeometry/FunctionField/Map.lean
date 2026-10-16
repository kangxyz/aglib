/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Dominant maps on actual function fields

The map is the actual generic-point stalk map. Field constants use the supplied
structure morphism and actual global germ; no properness, normality, Noetherianity
or dimension hypothesis is introduced.

Source: `R5Lab/AlgebraicGeometry/Curves/Divisors/FunctionField.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`fbbe95c25acbf753d37313598504e298db7a52fcab8a860fa6849e371b8cf339`. Selected original ranges: [[38,
69]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.Scheme
universe u
variable {k : Type u} [Field k] (X : Scheme.{u}) [IsIntegral X]
local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

/-- The structural field map into the function field, using the actual global germ map. -/
def functionFieldConstants (p : X ⟶ Spec (.of k)) : k →+* X.functionField :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.germToFunctionField ⊤).hom

@[simp] theorem functionFieldConstants_apply (p : X ⟶ Spec (.of k)) (a : k) :
    functionFieldConstants X p a = X.germToFunctionField ⊤
      (p.appTop ((Scheme.ΓSpecIso (.of k)).inv a)) := rfl

/-- Scalar structures used by field pullback consumers are induced by this map. -/
@[instance_reducible] def functionFieldConstantsAlgebra (p : X ⟶ Spec (.of k)) : Algebra k
  X.functionField :=
  (functionFieldConstants X p).toAlgebra

theorem functionFieldConstants_injective (p : X ⟶ Spec (.of k)) :
    Function.Injective (functionFieldConstants X p) := (functionFieldConstants X p).injective

theorem map_genericPoint_of_isDominant {Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  apply Eq.symm
  apply (genericPoint_spec Y).eq
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

instance fromSpecStalk_genericPoint_dominant : IsDominant (X.fromSpecStalk (genericPoint X)) where
  denseRange := by
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
    rw [← (genericPoint_spec X).def]
    exact closure_mono (Set.singleton_subset_iff.mpr
      ⟨IsLocalRing.closedPoint X.functionField, fromSpecStalk_genericPoint_apply X
        (IsLocalRing.closedPoint X.functionField)⟩)

variable {X} {Y : Scheme.{u}} [IsIntegral Y]

/-- The contravariant function-field map induced by the actual stalk map of a dominant morphism. -/
def functionFieldMap (f : X ⟶ Y) [IsDominant f] : Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkSpecializes (specializes_of_eq (map_genericPoint_of_isDominant X f))) ≫
    f.stalkMap (genericPoint X)).hom

/-- The algebra structure used in field-cohomology pullback is this exact embedding. -/
@[instance_reducible] def functionFieldMapAlgebra (f : X ⟶ Y) [IsDominant f] :
    Algebra Y.functionField X.functionField := (functionFieldMap f).toAlgebra

theorem functionFieldMap_injective (f : X ⟶ Y) [IsDominant f] :
    Function.Injective (functionFieldMap f) := (functionFieldMap f).injective

/-- The square is the naturality theorem for the actual generic-point stalk map. -/
theorem fromSpecStalk_genericPoint_naturality (f : X ⟶ Y) [IsDominant f] :
    (X.fromSpecStalk (genericPoint X)) ≫ f =
      Spec.map (CommRingCat.ofHom (functionFieldMap f)) ≫ (Y.fromSpecStalk (genericPoint Y)) := by
  change X.fromSpecStalk _ ≫ f =
    Spec.map (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _) ≫ Y.fromSpecStalk _
  rw [Spec.map_comp, Category.assoc]
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm

local instance : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩

/-- Compatibility with actual global germs. -/
theorem functionFieldMap_germ (f : X ⟶ Y) [IsDominant f] :
    Y.germToFunctionField ⊤ ≫ CommRingCat.ofHom (functionFieldMap f) =
      f.appTop ≫ X.germToFunctionField ⊤ := by
  change Y.presheaf.germ ⊤ _ _ ≫
      (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _) = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes,
    Scheme.Hom.germ_stalkMap]
  simp [Scheme.Hom.appTop, Scheme.germToFunctionField]

variable {k l : Type u} [Field k] [Field l]

/-- Constants commute with an actual square of structure morphisms. -/
theorem functionFieldMap_constants (f : X ⟶ Y) [IsDominant f]
    (p : Y ⟶ Spec (.of k)) (q : X ⟶ Spec (.of l)) (a : k →+* l)
    (hsq : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom a)) :
    (functionFieldMap f).comp (functionFieldConstants Y p) =
      (functionFieldConstants X q).comp a := by
  suffices h : (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
    Y.germToFunctionField ⊤ ≫ CommRingCat.ofHom (functionFieldMap f) =
    CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (.of l)).inv ≫
      q.appTop ≫ X.germToFunctionField ⊤ by
    exact congrArg CommRingCat.Hom.hom h
  rw [functionFieldMap_germ, ← Category.assoc p.appTop,
    ← Scheme.Hom.comp_appTop, hsq, Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]

end AlgebraicGeometry.Scheme
