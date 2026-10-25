/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstants.FiniteTypeCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstants.HenselianFieldComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstantsOne.SpecializationRing
public import Aglib.RingTheory.Henselian.HenselizationNoetherian
public import Mathlib.RingTheory.Localization.Submodule

/-! # Original finite-constant comparison over separably closed field extensions

Classes and relations descend through the actual finite-type coefficient limit.
Closed specialization uses the actual finite purely inseparable residue field.
For surjectivity, local closed-fibre injectivity detects the lifted residue class,
and the existing nonlocal henselization map returns the equality to the target.
The endpoint is restricted to schemes finite over the original projective line.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

open ConstantFinite ConstantFinite.FieldComparison

variable (k K : Type u) [Field k] [Field K] [IsSepClosed k] [Algebra k K]
  {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 k) [IsFinite f]
  (A : Type u) [AddCommGroup A] [Finite A]

/-- A relation that vanishes over the target already vanishes at a finite-type
coefficient stage. Closed specialization and finite-pure injectivity detect the
original relation. The target field need not be separably closed for this part. -/
theorem finite_projectiveLine_fieldExtension_constantRestriction_injective (q : ℕ) :
    Function.Injective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K)) q) := by
  classical
  let p := f ≫ ProjectiveLine.structureMap k
  let : IsProper p := inferInstanceAs (IsProper (f ≫ ProjectiveLine.structureMap k))
  let : ∀ s : Finset K, HasExt.{u + 2} (AbelianSheaf.{u, u + 1}
      (pullback (Spec.algebraMap k (Algebra.FiniteTypeSubalgebraLimit.stage k K s)) p)) :=
    fun s => hasExtStandard.{u, u + 1}
      (pullback (Spec.algebraMap k (Algebra.FiniteTypeSubalgebraLimit.stage k K s)) p)
  intro a b hab
  obtain ⟨s, hs⟩ := exists_cohomologyEquality_over_finiteTypeSubalgebra k K p A q a b hab
  let B := Algebra.FiniteTypeSubalgebraLimit.stage k K s
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let : m.IsMaximal := hm
  let R := Henselization.AtMaximal B m
  let : Algebra k R := Henselization.AtMaximal.baseAlgebra B m k
  let : IsScalarTower k B R := Henselization.AtMaximal.baseScalarTower B m k
  let κ := IsLocalRing.ResidueField R
  let : Module.Finite k κ := Henselization.AtMaximal.residue_finite B m k
  let : IsPurelyInseparable k κ := Henselization.AtMaximal.residue_isPurelyInseparable B m k
  let ρ : B →ₐ[k] R := IsScalarTower.toAlgHom k B R
  let β : B →ₐ[k] κ := (IsScalarTower.toAlgHom k R κ).comp ρ
  let uκ := LocalRing.coefficientBaseChangeMap p β
  let fB := pullback.snd (Spec.algebraMap k B) p
  let gκ := pullback.fst p (Spec.algebraMap k κ)
  have hu : uκ ≫ fB = gκ := LocalRing.coefficientBaseChangeMap_snd p β
  have hκ : constantRestriction A gκ q a = constantRestriction A gκ q b := by
    calc
      constantRestriction A gκ q a = constantRestriction A (uκ ≫ fB) q a := by rw [hu]
      _ = constantRestriction A uκ q (constantRestriction A fB q a) :=
        constantRestriction_comp A fB uκ q a
      _ = constantRestriction A uκ q (constantRestriction A fB q b) :=
        congrArg (constantRestriction A uκ q) hs
      _ = constantRestriction A gκ q b := by rw [← constantRestriction_comp, hu]
  exact (finitePure_constantCohomologyPullback_bijective k κ p A q).injective hκ

variable [IsSepClosed K]

/-- Every original finite-constant class on the target descends to the original
finite cover of the line. The actual generic henselization map is nonlocal;
the proof never embeds the closed residue field into the target field. -/
theorem finite_projectiveLine_fieldExtension_constantRestriction_surjective (q : ℕ) :
    Function.Surjective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K)) q) := by
  classical
  let p := f ≫ ProjectiveLine.structureMap k
  let : IsProper p := inferInstanceAs (IsProper (f ≫ ProjectiveLine.structureMap k))
  let : ∀ s : Finset K, HasExt.{u + 2} (AbelianSheaf.{u, u + 1}
      (pullback (Spec.algebraMap k (Algebra.FiniteTypeSubalgebraLimit.stage k K s)) p)) :=
    fun s => hasExtStandard.{u, u + 1}
      (pullback (Spec.algebraMap k (Algebra.FiniteTypeSubalgebraLimit.stage k K s)) p)
  intro c
  obtain ⟨s, cB, hcB⟩ := exists_cohomologyClass_over_finiteTypeSubalgebra k K p A q c
  let B := Algebra.FiniteTypeSubalgebraLimit.stage k K s
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let : m.IsMaximal := hm
  let R := Henselization.AtMaximal B m
  let : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl _ inferInstance
  let : IsNoetherianRing R := Henselization.isNoetherianRing (Localization.AtPrime m)
  let : Algebra k R := Henselization.AtMaximal.baseAlgebra B m k
  let : IsScalarTower k B R := Henselization.AtMaximal.baseScalarTower B m k
  let : Module.Finite k (IsLocalRing.ResidueField R) :=
    Henselization.AtMaximal.residue_finite B m k
  let : IsPurelyInseparable k (IsLocalRing.ResidueField R) :=
    Henselization.AtMaximal.residue_isPurelyInseparable B m k
  let : IsSepClosed (IsLocalRing.ResidueField R) :=
    Henselization.AtMaximal.residue_isSepClosed B m k
  obtain ⟨γB⟩ := Henselization.AtMaximal.nonempty_algHom B m K Subtype.val_injective
  let γ := γB.restrictScalars k
  let ρ : B →ₐ[k] R := IsScalarTower.toAlgHom k B R
  have hγ : γ.comp ρ = B.val := by
    ext b
    exact γB.commutes b
  let uR := LocalRing.coefficientBaseChangeMap p ρ
  let v := coefficientPullbackMap p γ
  let gR := pullback.fst p (Spec.algebraMap k R)
  let gK := pullback.fst p (Spec.algebraMap k K)
  obtain ⟨a, ha⟩ :=
    (finite_projectiveLine_henselianField_constantRestriction_bijective k R f A q).surjective
      (constantRestriction A uR q cB)
  refine ⟨a, ?_⟩
  calc
    constantRestriction A gK q a = constantRestriction A (v ≫ gR) q a := by
      rw [coefficientPullbackMap_fst]
    _ = constantRestriction A v q (constantRestriction A gR q a) :=
      constantRestriction_comp A gR v q a
    _ = constantRestriction A v q (constantRestriction A uR q cB) :=
      congrArg (constantRestriction A v q) ha
    _ = constantRestriction A (v ≫ uR) q cB :=
      (constantRestriction_comp A uR v q cB).symm
    _ = constantRestriction A (LocalRing.coefficientBaseChangeMap p B.val) q cB := by
      rw [coefficientBaseChangeMap_comp, hγ]
    _ = c := hcB

/-- Original finite-constant cohomology of a scheme finite over the projective
line is invariant under an arbitrary extension of separably closed fields,
in every natural cohomological degree. -/
theorem finite_projectiveLine_fieldExtension_constantRestriction_bijective (q : ℕ) :
    Function.Bijective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst (f ≫ ProjectiveLine.structureMap k) (Spec.algebraMap k K)) q) :=
  ⟨finite_projectiveLine_fieldExtension_constantRestriction_injective k K f A q,
    finite_projectiveLine_fieldExtension_constantRestriction_surjective k K f A q⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
