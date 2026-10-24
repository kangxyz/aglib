/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The canonical tensor comparison for linear module functors

For a linear additive functor on modules, the canonical comparison sends
`x ⊗ m` to the image of the actual coefficient map `r ↦ r • m` applied to `x`.
It is natural in every coefficient map. On a free module it is invertible if
the functor preserves the coproduct indexed by a basis. The basis may be
infinite. Ring, module-value and target universes are retained explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Module
open scoped TensorProduct

namespace ModuleCat

universe r v w i

variable (R : Type r) [CommRing R]

/-- The rank-one coefficient module in the required source value universe. -/
abbrev liftedUnit : ModuleCat.{max r v} R := ModuleCat.of R (ULift.{v} R)

variable {R}

/-- The actual coefficient map determined by an element of a module. -/
def coefficientHom {M : ModuleCat.{max r v} R} (m : M) : liftedUnit.{r, v} R ⟶ M :=
  ModuleCat.ofHom (ULift.moduleEquiv.toLinearMap.smulRight m)

@[simp]
theorem coefficientHom_apply {M : ModuleCat.{max r v} R} (m : M) (r : ULift.{v} R) :
    coefficientHom m r = r.down • m := rfl

@[simp]
theorem coefficientHom_add {M : ModuleCat.{max r v} R} (m n : M) :
    coefficientHom (m + n) = coefficientHom m + coefficientHom n := by
  ext r
  exact smul_add r.down m n

@[simp]
theorem coefficientHom_smul {M : ModuleCat.{max r v} R} (r : R) (m : M) :
    coefficientHom (r • m) = r • coefficientHom m := by
  ext s
  exact smul_comm s.down r m

@[reassoc]
theorem coefficientHom_comp {M N : ModuleCat.{max r v} R} (f : M ⟶ N) (m : M) :
    coefficientHom m ≫ f = coefficientHom (f m) := by
  ext r
  exact f.hom.map_smul r.down m

variable (F : ModuleCat.{max r v} R ⥤ ModuleCat.{w} R) [F.Additive] [F.Linear R]

/-- The bilinear pairing defined by the functor's actual coefficient maps. -/
def functorTensorPairing (M : ModuleCat.{max r v} R) :
    F.obj (liftedUnit.{r, v} R) →ₗ[R] M →ₗ[R] F.obj M where
  toFun x :=
    { toFun := fun m => F.map (coefficientHom m) x
      map_add' m n := by
        rw [coefficientHom_add, F.map_add]
        rfl
      map_smul' r m := by
        rw [coefficientHom_smul, F.map_smul]
        rfl }
  map_add' x y := by
    ext m
    exact (F.map (coefficientHom m)).hom.map_add x y
  map_smul' r x := by
    ext m
    exact (F.map (coefficientHom m)).hom.map_smul r x

/-- The canonical tensor comparison, before any coproduct-preservation hypothesis. -/
def functorTensorComparison (M : ModuleCat.{max r v} R) :
    F.obj (liftedUnit.{r, v} R) ⊗[R] M →ₗ[R] F.obj M :=
  TensorProduct.lift (functorTensorPairing F M)

/-- Pure tensors use the literal original coefficient map. -/
@[simp]
theorem functorTensorComparison_tmul (M : ModuleCat.{max r v} R)
    (x : F.obj (liftedUnit.{r, v} R)) (m : M) :
    functorTensorComparison F M (x ⊗ₜ[R] m) = F.map (coefficientHom m) x := rfl

/-- Every original linear coefficient map commutes with the canonical tensor comparison. -/
theorem functorTensorComparison_naturality {M N : ModuleCat.{max r v} R} (f : M ⟶ N) :
    (F.map f).hom.comp (functorTensorComparison F M) =
      (functorTensorComparison F N).comp (TensorProduct.map LinearMap.id f.hom) := by
  apply TensorProduct.ext'
  intro x m
  change F.map f (F.map (coefficientHom m) x) = F.map (coefficientHom (f m)) x
  rw [← coefficientHom_comp f m, F.map_comp]
  rfl

section Basis

variable {ι : Type i} {M : ModuleCat.{max r v} R} (b : Basis ι R M)

/-- The actual basis vectors exhibit a module as a coproduct of rank-one modules. -/
def basisCofan : Cofan (fun _ : ι => liftedUnit.{r, v} R) :=
  Cofan.mk M (fun i => coefficientHom (b i))

/-- The basis coproduct has its usual linear universal property, also for infinite bases. -/
def basisCofanIsColimit : IsColimit (basisCofan b) where
  desc s := ModuleCat.ofHom (b.constr R (fun i => s.ι.app ⟨i⟩ (ULift.up 1)))
  fac s i := by
    ext z
    change (b.constr R (fun i => s.ι.app ⟨i⟩ (ULift.up 1))) (z.down • b i.as) =
      s.ι.app i z
    rw [map_smul, b.constr_basis]
    calc
      z.down • s.ι.app i (ULift.up 1) = s.ι.app i (z.down • ULift.up 1) :=
        ((s.ι.app i).hom.map_smul z.down (ULift.up 1)).symm
      _ = s.ι.app i z := congrArg (s.ι.app i) (by
        apply ULift.ext
        simp)
  uniq s f h := by
    let f' : M ⟶ s.pt := f
    change f' = ModuleCat.ofHom (b.constr R (fun i => s.ι.app ⟨i⟩ (ULift.up 1)))
    apply ModuleCat.hom_ext
    apply b.ext
    intro i
    change f' (b i) = b.constr R (fun i => s.ι.app ⟨i⟩ (ULift.up 1)) (b i)
    rw [b.constr_basis]
    have hi := ConcreteCategory.congr_hom (h ⟨i⟩) (ULift.up 1)
    change f' ((1 : R) • b i) = s.ι.app ⟨i⟩ (ULift.up 1) at hi
    simpa only [one_smul] using hi

/-- The coordinate map into the actual lifted rank-one module. -/
def basisCoordinateHom (i : ι) : M ⟶ liftedUnit.{r, v} R :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp (b.coord i))

open Classical in
/-- A basis coordinate detects the corresponding coefficient in the canonical tensor map. -/
theorem functorTensorComparison_coordinate (i : ι)
    (z : F.obj (liftedUnit.{r, v} R) ⊗[R] M) :
    F.map (basisCoordinateHom b i) (functorTensorComparison F M z) =
      TensorProduct.equivFinsuppOfBasisRight b z i := by
  classical
  induction z with
  | tmul x m =>
      have h : coefficientHom m ≫ basisCoordinateHom b i =
          b.repr m i • 𝟙 (liftedUnit.{r, v} R) := by
        ext r
        change b.coord i (r.down • m) = b.repr m i * r.down
        rw [(b.coord i).map_smul]
        exact mul_comm r.down (b.repr m i)
      rw [functorTensorComparison_tmul,
        ← ModuleCat.comp_apply, ← F.map_comp, h, F.map_smul, F.map_id]
      simp
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply]
      exact congrArg₂ (· + ·) hx hy

include b in
/-- The canonical tensor comparison is injective on free coefficients, regardless
of coproduct preservation and without restricting the target value universe. -/
theorem functorTensorComparison_injective_of_basis :
    Function.Injective (functorTensorComparison F M) := by
  classical
  intro x y h
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [← functorTensorComparison_coordinate F b i,
    ← functorTensorComparison_coordinate F b i, h]

variable [PreservesColimitsOfShape (Discrete ι) F]

include b in
/-- Coproduct preservation gives surjectivity into the original functor value.
The universal-property target is the range submodule, so its universe stays unchanged. -/
theorem functorTensorComparison_surjective_of_basis :
    Function.Surjective (functorTensorComparison F M) := by
  let T := functorTensorComparison F M
  let c : Cofan (fun _ : ι => F.obj (liftedUnit.{r, v} R)) :=
    Cofan.mk (ModuleCat.of R (LinearMap.range T)) (fun i => ModuleCat.ofHom
      { toFun := fun x => ⟨F.map (coefficientHom (b i)) x, ⟨x ⊗ₜ[R] b i, rfl⟩⟩
        map_add' := fun x y => Subtype.ext ((F.map (coefficientHom (b i))).hom.map_add x y)
        map_smul' := fun r x => Subtype.ext ((F.map (coefficientHom (b i))).hom.map_smul r x) })
  let hc := isColimitCofanMkObjOfIsColimit F
    (fun _ : ι => liftedUnit.{r, v} R) (fun i => coefficientHom (b i))
    (basisCofanIsColimit b)
  let t : F.obj M ⟶ ModuleCat.of R (LinearMap.range T) := hc.desc c
  have ht : t ≫ ModuleCat.ofHom (LinearMap.range T).subtype = 𝟙 (F.obj M) := by
    apply hc.hom_ext
    intro i
    rw [← Category.assoc, hc.fac]
    ext x
    rfl
  intro y
  obtain ⟨z, hz⟩ := (t y).property
  exact ⟨z, hz.trans (ConcreteCategory.congr_hom ht y)⟩

/-- On free coefficients, preserving the actual basis-indexed coproduct makes the
canonical tensor comparison invertible. No finiteness of that basis is assumed. -/
def functorTensorEquivOfBasis : F.obj (liftedUnit.{r, v} R) ⊗[R] M ≃ₗ[R] F.obj M :=
  LinearEquiv.ofBijective (functorTensorComparison F M)
    ⟨functorTensorComparison_injective_of_basis F b,
      functorTensorComparison_surjective_of_basis F b⟩

/-- The basis proves invertibility but does not change the forward comparison. -/
@[simp]
theorem functorTensorEquivOfBasis_apply (z : F.obj (liftedUnit.{r, v} R) ⊗[R] M) :
    functorTensorEquivOfBasis F b z = functorTensorComparison F M z := rfl

end Basis

end ModuleCat
