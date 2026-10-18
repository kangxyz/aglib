/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Coordinate
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Sections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.SMulRegular
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.RingTheory.Regular.PrimeAvoidance

/-!
# A general hyperplane avoids the associated points of coherent modules

Over an infinite field `k`, with finitely many coordinates, a general hyperplane avoids the
finitely many associated points of finitely many coherent modules on `P_k` (Nitsure,
arXiv:math/0504590v1, p. 10): for coherent modules `Fⱼ`, `j` in a finite type, some global
section `s` of `O(1)` makes every frame coefficient `s / Xᵢ` (`ProjectiveSpace.frameCoefficient`,
in `Coordinate`) a nonzerodivisor on `Γ(Fⱼ, V)` for every subopen `V ≤ D₊(Xᵢ)`
(`exists_forall_frameCoefficient_isSMulRegular`).

The chart ring `Γ(D₊(Xᵢ))` is Noetherian and `Γ(Fⱼ, D₊(Xᵢ))` is finite over it
(`finite_sections_of_affineLocallyFiniteType`), so `associatedPrimes.exists_forall_isSMulRegular`
applies to the `k`-linear maps `s ↦ s / Xᵢ`; the `k`-structures come from the structural
constants `projectiveConstants`, and `Xᵢ / Xᵢ = 1` lies in no associated prime. Regularity on the
chart passes to its subopens by `AffineOpenSections.isSMulRegular_restrict`. With the chart
criterion `mono_twistingTensorMultiply_of_isSMulRegular` this gives the hyperplane sections of
Mumford's bound (`Regularity/Mumford/InfiniteField.lean`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u)

-- The `k`-structure of the chart rings and of `Γ(O(1))` is transported along the structural
-- constants; matching it with frame coefficients unfolds the module presheaf, which needs the
-- backward transparency rule.
set_option backward.isDefEq.respectTransparency false in
/-- **A general hyperplane avoids the associated points of finitely many coherent modules**
(Nitsure, arXiv:math/0504590v1, p. 10): over an infinite field, some global section `s` of
`O(1)` has frame coefficients `s / Xᵢ` that are nonzerodivisors on the sections of each of
finitely many coherent modules over every subopen of every chart. -/
theorem exists_forall_frameCoefficient_isSMulRegular [Infinite k] [Finite ι] {J : Type*}
    [Finite J] (F : J → (ProjectiveSpace k ι).Modules)
    (hF : ∀ j, affineLocallyFiniteType (ProjectiveSpace k ι) (F j)) :
    ∃ s : (twistingSheaf k ι ((1 : ℕ) : ℤ)).val.obj (op ⊤),
      ∀ (j : J) (i : ι) (V : (ProjectiveSpace k ι).Opens) (hV : V ≤ coordinateOpen k ι i),
        IsSMulRegular Γ(F j, V) (frameCoefficient k ι s i hV) := by
  let : Module k ((twistingSheaf k ι ((1 : ℕ) : ℤ)).val.obj (op ⊤)) :=
    Module.compHom _ (projectiveConstants k ι)
  let : ∀ p : ι × J, Algebra k Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1) := fun p =>
    (((ProjectiveSpace k ι).presheaf.map (homOfLE le_top).op).hom.comp
      (projectiveConstants k ι)).toAlgebra
  have : ∀ p : ι × J, IsNoetherianRing Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1) :=
    fun p => IsLocallyNoetherian.component_noetherian ⟨_, isAffineOpen_coordinateOpen k ι p.1⟩
  have : ∀ p : ι × J, Module.Finite Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1)
      Γ(F p.2, coordinateOpen k ι p.1) := fun p =>
    finite_sections_of_affineLocallyFiniteType (F p.2) (hF p.2)
      ⟨_, isAffineOpen_coordinateOpen k ι p.1⟩
  let lam : ∀ p : ι × J, (twistingSheaf k ι ((1 : ℕ) : ℤ)).val.obj (op ⊤) →ₗ[k]
      Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1) := fun p =>
    { toFun := fun s => frameCoefficient k ι s p.1 le_rfl
      map_add' := fun s t => frameCoefficient_add k ι s t p.1 le_rfl
      map_smul' := fun c s => by
        change frameCoefficient k ι (projectiveConstants k ι c • s) p.1 le_rfl = _
        rw [frameCoefficient_smul]
        rfl }
  obtain ⟨s, hs⟩ := associatedPrimes.exists_forall_isSMulRegular
    (fun p : ι × J => Γ(ProjectiveSpace k ι, coordinateOpen k ι p.1))
    (fun p : ι × J => Γ(F p.2, coordinateOpen k ι p.1)) lam (fun p P hP =>
      ⟨coordinateSection k ι p.1, by
        change frameCoefficient k ι (coordinateSection k ι p.1) p.1 le_rfl ∉ P
        rw [frameCoefficient_coordinateSection]
        exact (Ideal.ne_top_iff_one P).mp hP.isPrime.ne_top⟩)
  refine ⟨s, fun j i V hV => ?_⟩
  have hU := isAffineOpen_coordinateOpen k ι i
  have : ((F j).restrict hU.fromSpec).IsQuasicoherent := (hF j _ hU.fromSpec).1
  rw [frameCoefficient_eq_map]
  exact AffineOpenSections.isSMulRegular_restrict (F j) hU (hs (i, j)) hV

end AlgebraicGeometry.Scheme.Cohomology
