/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.FunctorTensor
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite modules from the canonical tensor comparison

The coefficient module may be infinite as a set or as a module over the base
ring. If the rank-one functor value has a finite basis, and the coefficient
module is finite over a second commuting ring, its functor value is finite over
that second ring. The supplied scalar compatibility concerns the actual scalar
endomorphisms, not an assumed finiteness or an unrelated cohomology object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Module
open scoped TensorProduct

namespace ModuleCat

universe r v w i j l

variable {R : Type r} [CommRing R]
  (F : ModuleCat.{max r v} R ⥤ ModuleCat.{w} R) [F.Additive] [F.Linear R]
  {M : ModuleCat.{max r v} R}
  (Λ : Type l) [Ring Λ] [Module Λ M] [SMulCommClass Λ R M]
  [Module Λ (F.obj M)]
  (hscalar : ∀ (a : Λ) (x : F.obj M),
    F.map (ModuleCat.ofHom (DistribSMul.toLinearMap R M a)) x = a • x)

/-- For each rank-one cohomology class, the canonical coefficient pairing is
linear for the original commuting coefficient action. -/
def functorTensorPairingOver (x : F.obj (liftedUnit.{r, v} R)) : M →ₗ[Λ] F.obj M where
  toFun m := F.map (coefficientHom m) x
  map_add' m n := by
    rw [coefficientHom_add, F.map_add]
    rfl
  map_smul' a m := by
    let f := ModuleCat.ofHom (DistribSMul.toLinearMap R M a)
    change F.map (coefficientHom (f m)) x = a • F.map (coefficientHom m) x
    rw [← coefficientHom_comp f m, F.map_comp]
    exact hscalar a (F.map (coefficientHom m) x)

include hscalar in
/-- A finite basis on the rank-one value gives a genuine finite-module conclusion
for the original commuting scalar action. The coefficient basis can be infinite. -/
theorem finite_functorObj_of_basis
    {ι : Type i} (b : Basis ι R M) [PreservesColimitsOfShape (Discrete ι) F]
    {κ : Type j} [Finite κ] (c : Basis κ R (F.obj (liftedUnit.{r, v} R)))
    [Module.Finite Λ M] : Module.Finite Λ (F.obj M) := by
  classical
  let L : (κ →₀ M) →ₗ[Λ] F.obj M :=
    Finsupp.lsum ℤ (fun i => functorTensorPairingOver F Λ hscalar (c i))
  apply Module.Finite.of_surjective L
  intro x
  obtain ⟨z, hz⟩ := functorTensorComparison_surjective_of_basis F b x
  obtain ⟨s, hs⟩ := TensorProduct.eq_repr_basis_left c z
  refine ⟨s, ?_⟩
  change s.sum (fun i m => F.map (coefficientHom m) (c i)) = x
  rw [← hz, ← hs]
  simp only [Finsupp.sum, map_sum, functorTensorComparison_tmul]

end ModuleCat
