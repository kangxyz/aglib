/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections
public import Mathlib.CategoryTheory.Monoidal.Discrete

/-!
# The twisting sheaves as a monoidal functor

The twisting sheaves `O(n)` on polynomial projective space form a functor
`twistingFunctor R ι : Discrete ℤ ⥤ (ProjectiveSpace R ι).Modules`, `n ↦ O(n)`, whose maps are
the transports `eqToHom` along equalities of degrees. For the additive monoidal structure on
`Discrete ℤ` and the monoidal structure on scheme modules, it is monoidal
(`twistingFunctor_monoidal`): the tensorator is twist multiplication `twistingTensorIso a b :
O(a) ⊗ O(b) ≅ O(a + b)` and the unit comparison is the inverse of `twistingZeroIso`.

The three coherence equations are proved once, at variable degrees: associativity
(`twistingTensorMap_associativity`) by nested pure tensors, and the two unit laws
(`twistingTensorMap_leftUnitor`, `twistingTensorMap_rightUnitor`) by frame coefficients on the
coordinate charts. In each, the degree equality enters only through `eqToHom (congrArg
(twistingSheaf R ι) h)` with a free proof `h`, and transport is evaluated by the lemmas
`twistingSection_eqToHom_val` and `twistingSectionsEquiv_eqToHom` of the twisting leaf, proved by
`subst`. Consumers obtain the transports of the monoidal structure as `(twistingFunctor R ι).map`,
and never evaluate them on sections. The unitors and whiskerings of scheme modules on pure section
tensors come from `Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.ProjectiveSpace

open AlgebraicGeometry.Scheme.Modules

variable (R : Type u) [CommRing R] (ι : Type u)

/-! ### Section identities -/

/-- Twist multiplication of sections is associative, after transport along the associativity of
degrees. -/
theorem twistingSectionMul_assoc (a b c : ℤ) (h : a + b + c = a + (b + c))
    (U : (ProjectiveSpace R ι).Opens) (l : Γ(twistingSheaf R ι a, U))
    (m : Γ(twistingSheaf R ι b, U)) (n : Γ(twistingSheaf R ι c, U)) :
    (eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op U)
        (twistingSectionMul R ι (a + b) c U (twistingSectionMul R ι a b U l m) n) =
      twistingSectionMul R ι a (b + c) U l (twistingSectionMul R ι b c U m n) := by
  apply Subtype.ext
  funext i
  refine (twistingSection_eqToHom_val R ι h _ i).trans ?_
  change l.val i * m.val i * n.val i = l.val i * (m.val i * n.val i)
  exact mul_assoc _ _ _

/-! ### The coherence equations at variable degrees -/

-- The frame equivalence and the section lemmas of the twists are stated for the
-- `X.ringCatSheaf` spelling of the structure sheaf, which agrees with the module-sheaf spelling
-- only after unfolding; this needs the transparency override, as in the twisting leaves.
set_option backward.isDefEq.respectTransparency false in
/-- Associativity of twist multiplication, as morphisms out of `(O(a) ⊗ O(b)) ⊗ O(c)`; the
degree equality enters only through `eqToHom`. -/
theorem twistingTensorMap_associativity (a b c : ℤ) (h : a + b + c = a + (b + c)) :
    twistingTensorMap R ι a b ▷ twistingSheaf R ι c ≫ twistingTensorMap R ι (a + b) c ≫
        eqToHom (congrArg (twistingSheaf R ι) h) =
      (α_ (twistingSheaf R ι a) (twistingSheaf R ι b) (twistingSheaf R ι c)).hom ≫
        twistingSheaf R ι a ◁ twistingTensorMap R ι b c ≫ twistingTensorMap R ι a (b + c) := by
  apply moduleTensor_nested_hom_ext_left
  intro U l m n
  -- Both composites without the transport, on the nested pure tensor; no `eqToHom` occurs here.
  have hL : (twistingTensorMap R ι a b ▷ twistingSheaf R ι c ≫
      twistingTensorMap R ι (a + b) c).val.app (op U)
        (moduleTensorSection (ProjectiveSpace R ι)
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
            (twistingSheaf R ι b)) (twistingSheaf R ι c) U
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
            (twistingSheaf R ι b) U l m) n) =
      twistingSectionMul R ι (a + b) c U (twistingSectionMul R ι a b U l m) n := by
    change (twistingTensorMap R ι (a + b) c).val.app (op U)
      ((twistingTensorMap R ι a b ▷ twistingSheaf R ι c).val.app (op U) _) = _
    rw [whiskerRight_moduleTensorSection, twistingTensorMap_section, twistingTensorMap_section]
  have hR : ((α_ (twistingSheaf R ι a) (twistingSheaf R ι b) (twistingSheaf R ι c)).hom ≫
      twistingSheaf R ι a ◁ twistingTensorMap R ι b c ≫ twistingTensorMap R ι a (b + c)).val.app
        (op U)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a ⊗ twistingSheaf R ι b)
          (twistingSheaf R ι c) U
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
            (twistingSheaf R ι b) U l m) n) =
      twistingSectionMul R ι a (b + c) U l (twistingSectionMul R ι b c U m n) := by
    change (twistingTensorMap R ι a (b + c)).val.app (op U)
      ((twistingSheaf R ι a ◁ twistingTensorMap R ι b c).val.app (op U)
        ((α_ (twistingSheaf R ι a) (twistingSheaf R ι b) (twistingSheaf R ι c)).hom.val.app
          (op U) _)) = _
    rw [associator_hom_moduleTensorSection]
    erw [whiskerLeft_moduleTensorSection]
    rw [twistingTensorMap_section, twistingTensorMap_section]
  calc _ = (eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op U)
        ((twistingTensorMap R ι a b ▷ twistingSheaf R ι c ≫
          twistingTensorMap R ι (a + b) c).val.app (op U)
          (moduleTensorSection (ProjectiveSpace R ι)
            ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj
              (twistingSheaf R ι b)) (twistingSheaf R ι c) U
            (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
              (twistingSheaf R ι b) U l m) n)) := rfl
    _ = (eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op U)
        (twistingSectionMul R ι (a + b) c U (twistingSectionMul R ι a b U l m) n) := by rw [hL]
    _ = twistingSectionMul R ι a (b + c) U l (twistingSectionMul R ι b c U m n) :=
      twistingSectionMul_assoc R ι a b c h U l m n
    _ = _ := hR.symm

-- The frame equivalence and the section lemmas of the twists are stated for the
-- `X.ringCatSheaf` spelling of the structure sheaf, which agrees with the module-sheaf spelling
-- only after unfolding; this needs the transparency override, as in the twisting leaves.
set_option backward.isDefEq.respectTransparency false in
/-- The left unit law of twist multiplication, with the zero twist identified with the structure
module by `twistingZeroIso`. -/
theorem twistingTensorMap_leftUnitor (a : ℤ) (h : 0 + a = a) :
    (λ_ (twistingSheaf R ι a)).hom =
      MonoidalCategoryStruct.whiskerRight (C := (ProjectiveSpace R ι).Modules)
          (unitToTwistingZero R ι) (twistingSheaf R ι a) ≫ twistingTensorMap R ι 0 a ≫
        eqToHom (congrArg (twistingSheaf R ι) h) := by
  rw [← cancel_epi (λ_ (twistingSheaf R ι a)).inv, Iso.inv_hom_id]
  apply hom_ext_of_coordinateSubopens R ι
  intro i V hi t
  apply (twistingSectionsEquiv R ι a i hi).injective
  change twistingSectionsEquiv R ι a i hi t =
    twistingSectionsEquiv R ι a i hi ((eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op V)
      ((twistingTensorMap R ι 0 a).val.app (op V)
        ((MonoidalCategoryStruct.whiskerRight (C := (ProjectiveSpace R ι).Modules)
            (unitToTwistingZero R ι) (twistingSheaf R ι a)).val.app (op V)
          ((λ_ (twistingSheaf R ι a)).inv.val.app (op V) t))))
  rw [twistingSectionsEquiv_eqToHom R ι h, leftUnitor_inv_moduleTensorSection,
    whiskerRight_moduleTensorSection, twistingTensorMap_section, twistingSectionsEquiv_mul,
    unitToTwistingZero_app R ι i hi, one_mul]

-- The frame equivalence and the section lemmas of the twists are stated for the
-- `X.ringCatSheaf` spelling of the structure sheaf, which agrees with the module-sheaf spelling
-- only after unfolding; this needs the transparency override, as in the twisting leaves.
set_option backward.isDefEq.respectTransparency false in
/-- The right unit law of twist multiplication, with the zero twist identified with the
structure module by `twistingZeroIso`. -/
theorem twistingTensorMap_rightUnitor (a : ℤ) (h : a + 0 = a) :
    (ρ_ (twistingSheaf R ι a)).hom =
      MonoidalCategoryStruct.whiskerLeft (C := (ProjectiveSpace R ι).Modules)
          (twistingSheaf R ι a) (unitToTwistingZero R ι) ≫ twistingTensorMap R ι a 0 ≫
        eqToHom (congrArg (twistingSheaf R ι) h) := by
  rw [← cancel_epi (ρ_ (twistingSheaf R ι a)).inv, Iso.inv_hom_id]
  apply hom_ext_of_coordinateSubopens R ι
  intro i V hi t
  apply (twistingSectionsEquiv R ι a i hi).injective
  change twistingSectionsEquiv R ι a i hi t =
    twistingSectionsEquiv R ι a i hi ((eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op V)
      ((twistingTensorMap R ι a 0).val.app (op V)
        ((MonoidalCategoryStruct.whiskerLeft (C := (ProjectiveSpace R ι).Modules)
            (twistingSheaf R ι a) (unitToTwistingZero R ι)).val.app (op V)
          ((ρ_ (twistingSheaf R ι a)).inv.val.app (op V) t))))
  rw [twistingSectionsEquiv_eqToHom R ι h, rightUnitor_inv_moduleTensorSection,
    whiskerLeft_moduleTensorSection, twistingTensorMap_section, twistingSectionsEquiv_mul,
    unitToTwistingZero_app R ι i hi, mul_one]

/-! ### The twisting functor -/

/-- The twisting sheaves as a functor out of the discrete category of the integers; its maps are
the transports along equalities of degrees. -/
def twistingFunctor : Discrete ℤ ⥤ (ProjectiveSpace R ι).Modules where
  obj n := twistingSheaf R ι n.as
  map f := eqToHom (congrArg (twistingSheaf R ι) (Discrete.eq_of_hom f))

@[simp]
theorem twistingFunctor_obj (n : Discrete ℤ) :
    (twistingFunctor R ι).obj n = twistingSheaf R ι n.as :=
  rfl

theorem twistingFunctor_map {m n : Discrete ℤ} (f : m ⟶ n) :
    (twistingFunctor R ι).map f =
      eqToHom (congrArg (twistingSheaf R ι) (Discrete.eq_of_hom f)) :=
  rfl

/-- The monoidal structure of the twisting functor: the tensorator is twist multiplication and
the unit comparison is the inverse of the zero-twist identification. -/
def twistingFunctorCoreMonoidal : (twistingFunctor R ι).CoreMonoidal where
  εIso := (twistingZeroIso R ι).symm
  μIso m n := twistingTensorIso R ι m.as n.as
  μIso_hom_natural_left {m m'} f n := by
    obtain rfl : m = m' := Discrete.ext (Discrete.eq_of_hom f)
    obtain rfl : f = 𝟙 m := Subsingleton.elim _ _
    simp
  μIso_hom_natural_right {m m'} n f := by
    obtain rfl : m = m' := Discrete.ext (Discrete.eq_of_hom f)
    obtain rfl : f = 𝟙 m := Subsingleton.elim _ _
    simp
  associativity m n p := twistingTensorMap_associativity R ι m.as n.as p.as (add_assoc _ _ _)
  left_unitality n := twistingTensorMap_leftUnitor R ι n.as (zero_add _)
  right_unitality n := twistingTensorMap_rightUnitor R ι n.as (add_zero _)

/-- The twisting functor is monoidal, with tensorator `twistingTensorIso` and unit comparison
`twistingZeroIso.symm`. -/
instance twistingFunctor_monoidal : (twistingFunctor R ι).Monoidal :=
  (twistingFunctorCoreMonoidal R ι).toMonoidal

theorem twistingFunctor_μ (m n : Discrete ℤ) :
    Functor.LaxMonoidal.μ (twistingFunctor R ι) m n = twistingTensorMap R ι m.as n.as :=
  rfl

theorem twistingFunctor_δ (m n : Discrete ℤ) :
    Functor.OplaxMonoidal.δ (twistingFunctor R ι) m n = twistingTensorInv R ι m.as n.as :=
  rfl

theorem twistingFunctor_ε :
    Functor.LaxMonoidal.ε (twistingFunctor R ι) = unitToTwistingZero R ι :=
  rfl

theorem twistingFunctor_η :
    Functor.OplaxMonoidal.η (twistingFunctor R ι) = twistingZeroToUnit R ι :=
  rfl

theorem twistingFunctor_μIso (m n : Discrete ℤ) :
    Functor.Monoidal.μIso (twistingFunctor R ι) m n = twistingTensorIso R ι m.as n.as :=
  rfl

theorem twistingFunctor_εIso :
    Functor.Monoidal.εIso (twistingFunctor R ι) = (twistingZeroIso R ι).symm :=
  rfl

end AlgebraicGeometry.ProjectiveSpace
