/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.CoordinateGeneration
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Monotone
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Koszul
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.KoszulExact
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Surjectivity
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.GlobalGeneration
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.AlgebraicGeometry.Modules.Generators.GlobalSections
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.FreeDegree
public import Aglib.CategoryTheory.Preadditive.Coproducts

/-! Focused consumer of Castelnuovo–Mumford regularity on actual polynomial projective space:
the definition uses the original `Sheaf.H` of the native tensor twist `O(m - q) ⊗ F`. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

example (R : Type u) [CommRing R] (ι : Type u) (F : (ProjectiveSpace R ι).Modules) (m : ℤ) :
    IsProjectiveRegular R ι F m ↔ ∀ q : ℕ, 0 < q →
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (m - q))).obj F)) q) :=
  Iff.rfl

example (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) :
    ∃ m : ℤ, IsProjectiveRegular R ι F m :=
  exists_isProjectiveRegular R ι n e F hF

example (R : Type u) [CommRing R] (ι : Type u) [Finite ι] (F : (ProjectiveSpace R ι).Modules) :
    CategoryTheory.Epi (coordinateMultiplicationSum R ι F) :=
  inferInstance

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_isProjectiveRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.exists_isProjectiveRegular

/--
info: 'AlgebraicGeometry.ProjectiveSpace.epi_coordinateMultiplicationSum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.epi_coordinateMultiplicationSum

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiplyTo_rfl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiplyTo_rfl

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiplyTo_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiplyTo_comm

/-! Nitsure, Lemma 2.1 (b) (Stacks, Tag 08A6): regularity passes to all larger twists. -/

example (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules) [F.IsQuasicoherent]
    (m m' : ℤ) (hm : m ≤ m') (h : IsProjectiveRegular R ι F m) :
    IsProjectiveRegular R ι F m' :=
  IsProjectiveRegular.of_le R ι n e hm h

example (R : Type u) [CommRing R] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) (m m' : ℤ) (hm : m ≤ m')
    (h : IsProjectiveRegular R ι F m) : IsProjectiveRegular R ι F m' :=
  IsProjectiveRegular.of_le_of_coherent R ι n e hF hm h

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_le

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_le_of_coherent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.of_le_of_coherent

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegularFrom.succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegularFrom.succ

/-! The Koszul complex of the coordinates: its differentials compose to zero. -/

example (R : Type u) [CommRing R] (ι : Type u) [LinearOrder ι] [Fintype ι]
    (F : (ProjectiveSpace R ι).Modules) (t : ℤ) (p : ℕ) :
    koszulDifferential R ι F t (p + 1) ≫ koszulDifferential R ι F t p = 0 :=
  koszulDifferential_comp R ι F t p

/--
info: 'AlgebraicGeometry.ProjectiveSpace.koszulDifferential_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.koszulDifferential_comp

example (R : Type u) [CommRing R] (ι : Type u) [LinearOrder ι] [Fintype ι]
    (F : (ProjectiveSpace R ι).Modules) (t : ℤ) (p : ℕ) (i : ι) :
    koszulWedge R ι F t (p + 1) i ≫ koszulDifferential R ι F (t + 1) (p + 1) +
      koszulDifferential R ι F t p ≫ koszulWedge R ι F t p i =
        koszulCoordinateMul R ι F t (p + 1) i :=
  koszul_homotopy R ι F t p i

/--
info: 'AlgebraicGeometry.ProjectiveSpace.koszul_homotopy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.koszul_homotopy

/-! Free-degree forms of the monoidal twist comparisons. -/

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensor_map_multiplyTo_comp_compIsoTo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensor_map_multiplyTo_comp_compIsoTo

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiplyTo_app_comp_compIsoTo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiplyTo_app_comp_compIsoTo

/-! Exactness of the Koszul complex of the coordinates, over every base ring. -/

example (R : Type u) [CommRing R] (ι : Type u) [LinearOrder ι] [Fintype ι]
    (F : (ProjectiveSpace R ι).Modules) (t : ℤ) (p : ℕ) :
    CategoryTheory.Epi (CategoryTheory.Limits.kernel.lift (koszulDifferential R ι F t p)
      (koszulDifferential R ι F t (p + 1)) (koszulDifferential_comp R ι F t p)) :=
  epi_koszul_kernelLift R ι F t p

example (R : Type u) [CommRing R] (ι : Type u) [LinearOrder ι] [Fintype ι]
    (F : (ProjectiveSpace R ι).Modules) (t : ℤ) :
    CategoryTheory.Epi (koszulDifferential R ι F t 0) :=
  epi_koszulDifferential_zero R ι F t

/--
info: 'AlgebraicGeometry.ProjectiveSpace.epi_koszul_kernelLift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.epi_koszul_kernelLift

/--
info: 'AlgebraicGeometry.ProjectiveSpace.epi_koszulDifferential_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.epi_koszulDifferential_zero

/-! Nitsure, Lemma 2.1 (a) (Stacks, Tag 08A7): the coordinate multiplications are jointly
surjective on global sections of regular twists. -/

example (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules) [F.IsQuasicoherent]
    (m r : ℤ) (h : IsProjectiveRegular R ι F m) (hr : m ≤ r) :
    Function.Surjective ((CategoryTheory.Limits.Sigma.desc fun i : ι =>
      (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) r (coordinateSection R ι i)).app F).val.app
        (Opposite.op ⊤)) :=
  IsProjectiveRegular.surjective_coordinateMul R ι n e h hr

example (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    (m r : ℤ) (h : IsProjectiveRegular R ι F m) (hr : m ≤ r) :
    Function.Surjective ((CategoryTheory.Limits.Sigma.desc fun i : ι =>
      (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) r (coordinateSection R ι i)).app F).val.app
        (Opposite.op ⊤)) :=
  IsProjectiveRegular.surjective_coordinateMul_of_coherent R ι n e hF h hr

/-! The same statement with global sections as morphisms out of the unit: `s = ∑ᵢ tᵢ ≫ Xᵢ`. -/

example (R : Type u) [CommRing R] (ι : Type u) [Fintype ι] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules) [F.IsQuasicoherent]
    (m r : ℤ) (h : IsProjectiveRegular R ι F m) (hr : m ≤ r)
    (s : MonoidalCategory.tensorUnit (ProjectiveSpace R ι).Modules ⟶
      (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (((1 : ℕ) : ℤ) + r))).obj F) :
    ∃ t : ι → (MonoidalCategory.tensorUnit (ProjectiveSpace R ι).Modules ⟶
        (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι r)).obj F),
      s = ∑ i, t i ≫
        (twistingTensorMultiply R ι ((1 : ℕ) : ℤ) r (coordinateSection R ι i)).app F :=
  IsProjectiveRegular.exists_eq_sum_coordinateMul R ι n e h hr s

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.surjective_coordinateMul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.surjective_coordinateMul

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.surjective_coordinateMul_of_coherent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.surjective_coordinateMul_of_coherent

/-! Nitsure, Lemma 2.1 (c) (Stacks, Tag 08A8): regular twists are globally generated. -/

/-! Lemma 2.1 (c) is the conjunction of the vanishing of `H^i(O(r) ⊗ F)` for `i ≥ 1` and the
global generation of `O(r) ⊗ F`, for `r ≥ m`; neither half needs a Noetherian base. -/

example (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    (m r : ℤ) (h : IsProjectiveRegular R ι F m) (hr : m ≤ r) :
    (∀ i : ℕ, 0 < i → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι r)).obj F)) i)) ∧
      CategoryTheory.Epi (globalSectionsEval ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι r)).obj F)) :=
  ⟨fun _ hi => IsProjectiveRegular.cohomology_subsingleton_of_le_of_coherent R ι n e hF h hr hi,
    IsProjectiveRegular.epi_globalSectionsEval R ι n e hF h hr⟩

example (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules) [F.IsQuasicoherent]
    (m r : ℤ) (h : IsProjectiveRegular R ι F m) (hr : m ≤ r) (i : ℕ) (hi : 0 < i) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι r)).obj F)) i) :=
  IsProjectiveRegular.cohomology_subsingleton_of_le R ι n e h hr hi

example (R : Type u) [CommRing R] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    (m r : ℤ) (h : IsProjectiveRegular R ι F m) (hr : m ≤ r) :
    Nonempty (SheafOfModules.GeneratingSections ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι r)).obj F)) :=
  IsProjectiveRegular.nonempty_generatingSections R ι n e hF h hr

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.epi_globalSectionsEval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.epi_globalSectionsEval

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.nonempty_generatingSections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.nonempty_generatingSections

example (R : Type u) [CommRing R] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace R ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    (m r : ℤ) (h : IsProjectiveRegular R ι F m) (hr : m ≤ r) :
    ∃ σ : SheafOfModules.GeneratingSections ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι r)).obj F), σ.IsFiniteType :=
  IsProjectiveRegular.exists_generatingSections_isFiniteType R ι n e hF h hr

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.exists_generatingSections_isFiniteType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.exists_generatingSections_isFiniteType

/-! Guards for the corollaries of this repair and for the moved supporting declarations. -/

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.cohomology_subsingleton_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.cohomology_subsingleton_of_le

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.cohomology_subsingleton_of_le_of_coherent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.cohomology_subsingleton_of_le_of_coherent

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.exists_eq_sum_coordinateMul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.IsProjectiveRegular.exists_eq_sum_coordinateMul

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.twistingTensor_isQuasicoherent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.twistingTensor_isQuasicoherent

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomology_subsingleton_coproduct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomology_subsingleton_coproduct

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomology_subsingleton_tensor_target' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomology_subsingleton_tensor_target

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleCohomology_subsingleton_tensor_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleCohomology_subsingleton_tensor_kernel

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.epi_of_twisting_whiskerLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.epi_of_twisting_whiskerLeft

/--
info: 'AlgebraicGeometry.Scheme.Modules.epi_sigmaDesc_globalSectionsEval_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.epi_sigmaDesc_globalSectionsEval_comp

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_finite_sections_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_finite_sections_comp

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_generatingSections_isFiniteType_of_epi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_generatingSections_isFiniteType_of_epi

/--
info: 'AlgebraicGeometry.Scheme.Modules.monoidalPreadditive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.monoidalPreadditive

/--
info: 'AlgebraicGeometry.ProjectiveSpace.multiplyTo_comp_twistMergeInv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.multiplyTo_comp_twistMergeInv

/--
info: 'AlgebraicGeometry.ProjectiveSpace.unitMultiply_twistMerge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.unitMultiply_twistMerge

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiply_app_eq_unitMultiply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMultiply_app_eq_unitMultiply

/--
info: 'CategoryTheory.Limits.Sigma.sum_π_ι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Limits.Sigma.sum_π_ι

/--
info: 'CategoryTheory.Limits.exists_eq_sum_sigma_ι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Limits.exists_eq_sum_sigma_ι

/--
info: 'CategoryTheory.Limits.isZero_obj_of_isBilimit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Limits.isZero_obj_of_isBilimit
