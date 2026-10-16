/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.HomogeneousSections

/-!
# Multiplication on actual projective twists

The matching local functions defining `O(a)` and `O(b)` multiply to matching local functions
of `O(a+b)`. This is bilinear for the original structure-sheaf action, commutes with actual
restrictions, and is ordinary multiplication in every original standard coordinate frame.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Multiplication of actual twist sections, defined by the product of their original
matching chart functions. -/
def twistingSectionMul (a b : ℤ) (V : (ProjectiveSpace R ι).Opens)
    (s : (twistingSheaf R ι a).val.obj (op V))
    (t : (twistingSheaf R ι b).val.obj (op V)) :
    (twistingSheaf R ι (a + b)).val.obj (op V) := by
  change ((coordinateUnitCocycle R ι).zpow (-a)).Sections V at s
  change ((coordinateUnitCocycle R ι).zpow (-b)).Sections V at t
  change ((coordinateUnitCocycle R ι).zpow (-(a + b))).Sections V
  refine ⟨fun i => s.val i * t.val i, ?_⟩
  intro W hWV i j hi hj
  change sectionRestrict (ProjectiveSpace R ι) (le_inf hWV hi) (s.val i * t.val i) =
    (((coordinateUnitCocycle R ι).zpow (-(a + b))).transitionOn i j hi hj).val *
      sectionRestrict (ProjectiveSpace R ι) (le_inf hWV hj) (s.val j * t.val j)
  rw [map_mul, s.property W hWV i j hi hj, t.property W hWV i j hi hj, map_mul]
  simp only [UnitCocycle.zpow_transitionOn, neg_add, zpow_add, Units.val_mul]
  ring

/-- The multiplication retains each original matching-family component. -/
@[simp]
theorem twistingSectionMul_apply (a b : ℤ) (V : (ProjectiveSpace R ι).Opens)
    (s : (twistingSheaf R ι a).val.obj (op V))
    (t : (twistingSheaf R ι b).val.obj (op V)) (i : ι) :
    (twistingSectionMul R ι a b V s t).val i = s.val i * t.val i := rfl

/-- Twist multiplication is bilinear over the original ring of functions on the open. -/
def twistingSectionMulLinear (a b : ℤ) (V : (ProjectiveSpace R ι).Opens) :
    (twistingSheaf R ι a).val.obj (op V) →ₗ[Γ(ProjectiveSpace R ι, V)]
      (twistingSheaf R ι b).val.obj (op V) →ₗ[Γ(ProjectiveSpace R ι, V)]
        (twistingSheaf R ι (a + b)).val.obj (op V) where
  toFun s := {
    toFun := twistingSectionMul R ι a b V s
    map_add' t v := by
      apply Subtype.ext
      funext i
      change s.val i * (t.val i + v.val i) = s.val i * t.val i + s.val i * v.val i
      exact mul_add _ _ _
    map_smul' r t := by
      apply Subtype.ext
      funext i
      change s.val i * (sectionRestrict (ProjectiveSpace R ι) inf_le_left r * t.val i) =
        sectionRestrict (ProjectiveSpace R ι) inf_le_left r * (s.val i * t.val i)
      ring }
  map_add' s t := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext i
    change (s.val i + t.val i) * v.val i = s.val i * v.val i + t.val i * v.val i
    exact add_mul _ _ _
  map_smul' r s := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext i
    change (sectionRestrict (ProjectiveSpace R ι) inf_le_left r * s.val i) * t.val i =
      sectionRestrict (ProjectiveSpace R ι) inf_le_left r * (s.val i * t.val i)
    exact mul_assoc _ _ _

/-- Twist multiplication commutes with every original module-sheaf restriction. -/
theorem twistingSectionMul_restrict (a b : ℤ) {V W : (ProjectiveSpace R ι).Opens}
    (h : V ≤ W) (s : (twistingSheaf R ι a).val.obj (op W))
    (t : (twistingSheaf R ι b).val.obj (op W)) :
    (twistingSheaf R ι (a + b)).val.map (homOfLE h).op
        (twistingSectionMul R ι a b W s t) =
      twistingSectionMul R ι a b V
        ((twistingSheaf R ι a).val.map (homOfLE h).op s)
        ((twistingSheaf R ι b).val.map (homOfLE h).op t) := by
  apply Subtype.ext
  funext i
  change sectionRestrict (ProjectiveSpace R ι) (inf_le_inf h le_rfl) (s.val i * t.val i) =
    sectionRestrict (ProjectiveSpace R ι) (inf_le_inf h le_rfl) (s.val i) *
      sectionRestrict (ProjectiveSpace R ι) (inf_le_inf h le_rfl) (t.val i)
  exact map_mul _ _ _

/-- The multiplication is the ordinary product in each original standard coordinate frame. -/
theorem twistingSectionsEquiv_mul (a b : ℤ) (i : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i)
    (s : (twistingSheaf R ι a).val.obj (op V))
    (t : (twistingSheaf R ι b).val.obj (op V)) :
    twistingSectionsEquiv R ι (a + b) i hi (twistingSectionMul R ι a b V s t) =
      twistingSectionsEquiv R ι a i hi s * twistingSectionsEquiv R ι b i hi t := by
  change sectionRestrict (ProjectiveSpace R ι) (le_inf le_rfl hi) (s.val i * t.val i) =
    sectionRestrict (ProjectiveSpace R ι) (le_inf le_rfl hi) (s.val i) *
      sectionRestrict (ProjectiveSpace R ι) (le_inf le_rfl hi) (t.val i)
  exact map_mul _ _ _

/-- The same multiplication law for every original arrow of the module presheaves. -/
theorem twistingSectionMul_map (a b : ℤ) {V W : (ProjectiveSpace R ι).Opens}
    (f : op W ⟶ op V) (s : (twistingSheaf R ι a).val.obj (op W))
    (t : (twistingSheaf R ι b).val.obj (op W)) :
    (twistingSheaf R ι (a + b)).val.map f (twistingSectionMul R ι a b W s t) =
      twistingSectionMul R ι a b V
        ((twistingSheaf R ι a).val.map f s) ((twistingSheaf R ι b).val.map f t) := by
  apply Subtype.ext
  funext i
  change sectionRestrict (ProjectiveSpace R ι) (inf_le_inf (leOfHom f.unop) le_rfl)
      (s.val i * t.val i) =
    sectionRestrict (ProjectiveSpace R ι) (inf_le_inf (leOfHom f.unop) le_rfl) (s.val i) *
      sectionRestrict (ProjectiveSpace R ι) (inf_le_inf (leOfHom f.unop) le_rfl) (t.val i)
  exact map_mul _ _ _

/-- Multiplication by an actual global twist section is an actual module-sheaf morphism. -/
def twistingMultiplyGlobal (a b : ℤ)
    (s : (twistingSheaf R ι a).val.obj (op ⊤)) :
    twistingSheaf R ι b ⟶ twistingSheaf R ι (a + b) where
  val.app V := ModuleCat.ofHom (twistingSectionMulLinear R ι a b V.unop
    ((twistingSheaf R ι a).val.map (homOfLE le_top).op s))
  val.naturality {V W} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change twistingSectionMul R ι a b W.unop
        ((twistingSheaf R ι a).val.map (homOfLE le_top).op s)
        ((twistingSheaf R ι b).val.map f t) =
      (twistingSheaf R ι (a + b)).val.map f
        (twistingSectionMul R ι a b V.unop
          ((twistingSheaf R ι a).val.map (homOfLE le_top).op s) t)
    rw [twistingSectionMul_map, ← PresheafOfModules.map_comp_apply]
    apply congrArg (fun r => twistingSectionMul R ι a b W.unop r
      ((twistingSheaf R ι b).val.map f t))
    exact (twistingSheaf R ι a).val.congr_map_apply (Subsingleton.elim _ _) s

/-- The coefficient morphism is literal multiplication by the restricted global section. -/
theorem twistingMultiplyGlobal_app (a b : ℤ)
    (s : (twistingSheaf R ι a).val.obj (op ⊤)) (V : (ProjectiveSpace R ι).Opens)
    (t : (twistingSheaf R ι b).val.obj (op V)) :
    (twistingMultiplyGlobal R ι a b s).val.app (op V) t =
      twistingSectionMul R ι a b V ((twistingSheaf R ι a).val.map (homOfLE le_top).op s) t := rfl

/-- Multiplication by a sum of global twist sections is the sum of the actual coefficient
morphisms. -/
theorem twistingMultiplyGlobal_add (a b : ℤ)
    (s t : (twistingSheaf R ι a).val.obj (op ⊤)) :
    twistingMultiplyGlobal R ι a b (s + t) =
      twistingMultiplyGlobal R ι a b s + twistingMultiplyGlobal R ι a b t := by
  ext V x
  change twistingSectionMul R ι a b V
      ((twistingSheaf R ι a).val.map (homOfLE le_top).op (s + t)) x =
    twistingSectionMul R ι a b V
      ((twistingSheaf R ι a).val.map (homOfLE le_top).op s) x +
    twistingSectionMul R ι a b V
      ((twistingSheaf R ι a).val.map (homOfLE le_top).op t) x
  rw [map_add]
  exact LinearMap.congr_fun ((twistingSectionMulLinear R ι a b V).map_add _ _) x

/-- A homogeneous polynomial induces the original multiplication morphism between twists. -/
def polynomialMultiplication (n : ℕ) (p : MvPolynomial.homogeneousSubmodule ι R n) (b : ℤ) :
    twistingSheaf R ι b ⟶ twistingSheaf R ι ((n : ℤ) + b) :=
  twistingMultiplyGlobal R ι (n : ℤ) b (homogeneousSection R ι n p)

/-- On its original coordinate chart, polynomial multiplication is multiplication by the
actual homogeneous fraction `p / Xᵢ^n`. -/
theorem polynomialMultiplication_local (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι R n) (b : ℤ) (i : ι)
    (t : (twistingSheaf R ι b).val.obj (op (coordinateOpen R ι i))) :
    twistingSectionsEquiv R ι ((n : ℤ) + b) i le_rfl
        ((polynomialMultiplication R ι n p b).val.app (op (coordinateOpen R ι i)) t) =
      homogeneousChartSection R ι n p i * twistingSectionsEquiv R ι b i le_rfl t := by
  change twistingSectionsEquiv R ι ((n : ℤ) + b) i le_rfl
    (twistingSectionMul R ι (n : ℤ) b (coordinateOpen R ι i)
      ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
        (homogeneousSection R ι n p)) t) = _
  rw [twistingSectionsEquiv_mul, homogeneousSection_local]

end AlgebraicGeometry.ProjectiveSpace
