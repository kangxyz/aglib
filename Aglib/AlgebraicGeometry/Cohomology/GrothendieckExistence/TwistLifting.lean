/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.Tower
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence.Hom
public import Aglib.AlgebraicGeometry.ProjectiveSpace.TwistPresentation.Epimorphism
public import Aglib.AlgebraicGeometry.Modules.Generators.GlobalSections

/-!
# Compatible negative-twist generators

A single bound on the first cohomology of successive twisted kernels lifts
one fixed finite negative-twist presentation of the special fibre to compatible
maps at all levels. This works for arbitrary surjective towers, including the
ordinary relation tower; no cartesian reduction or relative flatness is used.
The uniform vanishing premise is a conditional supplier, not an existence
endpoint. Epimorphy at higher levels is a separate nilpotent-generation step.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.ProjectiveSpace

universe u v w

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Compatible lifts of a prescribed map from a coproduct, using the original
coyoneda tower and native natural-number dependent lifting. -/
theorem exists_compatible_coproduct_lift {C : Type u} [Category.{v} C]
    (F : ℕᵒᵖ ⥤ C) {J : Type w} (P : J → C) [HasCoproduct P]
    (hs : ∀ j n, Function.Surjective (fun f : P j ⟶ F.obj (op (n + 1)) =>
      f ≫ F.map (homOfLE (Nat.le_succ n)).op))
    (k : ℕ) (π : (∐ P) ⟶ F.obj (op k)) :
    ∃ p : (Functor.const ℕᵒᵖ).obj (∐ P) ⟶ F, p.app (op k) = π := by
  let T (j : J) := F ⋙ coyoneda.obj (op (P j))
  have h (j : J) : ∃ s : (T j).sections, s.val (op k) = Sigma.ι P j ≫ π :=
    (T j).sections_eval_surjective_of_surjective_succ (hs j) k (Sigma.ι P j ≫ π)
  choose s hs' using h
  refine ⟨{ app := fun n => Sigma.desc (fun j => (s j).val n)
            naturality := ?_ }, ?_⟩
  · intro n m f
    change 𝟙 (∐ P) ≫ Sigma.desc (fun j => (s j).val m) =
      Sigma.desc (fun j => (s j).val n) ≫ F.map f
    rw [Category.id_comp]
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    exact ((s j).property f).symm
  · apply Sigma.hom_ext
    intro j
    simpa only [Sigma.ι_comp_desc] using hs' j

/-- Vanishing of the original twisted kernel's H¹ makes postcomposition on
negative-twist morphisms surjective. Tensor equivalence and the original
unit/global-section correspondence are used, not a replacement Hom model. -/
theorem negativeTwistHom_surjective_of_h1_vanishing
    {R : Type u} [CommRing R] {ι : Type u} (d : ℤ)
    {M N : (ProjectiveSpace R ι).Modules} (π : M ⟶ N) [Epi π]
    (hK : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj
        (kernel π))) 1)) :
    Function.Surjective (fun f : twistingSheaf R ι (-d) ⟶ M => f ≫ π) := by
  let X := ProjectiveSpace R ι
  let T := moduleTensorLeftFunctor X (twistingSheaf R ι d)
  let S := (ShortComplex.kernelSequence π).map T
  have hS : S.ShortExact := tensor_shortExact_finiteLocallyFree (twistingSheaf R ι d)
    (ShortComplex.kernelSequence π)
    { exact := ShortComplex.kernelSequence_exact π, epi_g := inferInstanceAs (Epi π) }
  have hsections : Function.Surjective ((T.map π).val.app (op ⊤)) := by
    apply surjective_of_moduleCohomologyConnectingOfHom_zero_eq_zero
      (RingHom.id Γ(X, ⊤)) S hS
    let := moduleCohomologyModuleOfHom X (RingHom.id Γ(X, ⊤)) S.X₃ 0
    let := moduleCohomologyModuleOfHom X (RingHom.id Γ(X, ⊤)) S.X₁ (0 + 1)
    apply LinearMap.ext
    intro x
    exact hK.elim _ _
  intro f
  let e := twistingTensorNegIso (R := R) (ι := ι) d
  obtain ⟨g, hg⟩ := exists_unitHom_factor_of_surjective (T.map π) hsections
    (e.inv ≫ T.map f)
  obtain ⟨a, ha⟩ := T.map_surjective (e.hom ≫ g)
  refine ⟨a, T.map_injective ?_⟩
  rw [T.map_comp, ha, Category.assoc, hg, Iso.hom_inv_id_assoc]

/-- A uniform H¹ bound supplies compatible maps from one fixed finite sum
of negative twists, whose prescribed component is an epimorphism. This
supplier applies equally to cartesian formal systems and surjective relation
towers. The degree is chosen above the given bound by the actual projective
negative-twist presentation theorem. -/
theorem exists_compatible_negativeTwist_generators_of_uniform_h1
    (R : Type u) [CommRing R] (ι : Type u) [Finite ι]
    (F : ℕᵒᵖ ⥤ (ProjectiveSpace R ι).Modules)
    (k : ℕ)
    (hF : QuasiCoherent.affineLocallyFiniteType (ProjectiveSpace R ι) (F.obj (op k)))
    (hepi : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (B : ℕ)
    (hK : ∀ d : ℕ, B ≤ d → ∀ n, Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace R ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (d : ℤ))).obj
          (kernel (F.map (homOfLE (Nat.le_succ n)).op)))) 1)) :
    ∃ d : ℕ, B ≤ d ∧ ∃ (J : Type u) (_ : Finite J)
      (p : (Functor.const ℕᵒᵖ).obj (∐ fun _ : J => twistingSheaf R ι (-(d : ℤ))) ⟶ F),
      Epi (p.app (op k)) := by
  obtain ⟨d, hd, J, hJ, π, hπ, _⟩ :=
    exists_uniformNegativeTwistEpimorphism R ι (F.obj (op k)) hF B
  let := hJ
  have hs (j : J) (n : ℕ) : Function.Surjective
      (fun f : twistingSheaf R ι (-(d : ℤ)) ⟶ F.obj (op (n + 1)) =>
        f ≫ F.map (homOfLE (Nat.le_succ n)).op) := by
    let := hepi n
    exact negativeTwistHom_surjective_of_h1_vanishing (d : ℤ)
      (F.map (homOfLE (Nat.le_succ n)).op) (hK d hd n)
  obtain ⟨p, hp⟩ := exists_compatible_coproduct_lift F
    (fun _ : J => twistingSheaf R ι (-(d : ℤ))) hs k π
  refine ⟨d, hd, J, hJ, p, ?_⟩
  rw [hp]
  exact hπ

end AlgebraicGeometry.Scheme.Cohomology
