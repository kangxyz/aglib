/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.PGroupSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.CyclicLine

/-! # An actual constant cyclic line from p-group monodromy

Finite p-group image supplies an invariant point and its original section.
The faithful actual coefficient fibre transfers p-annihilation to the whole
represented sheaf. The original constant adjunction then gives a genuine
monomorphic prime-cyclic coefficient map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Scheme.FiniteEtale Scheme.EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open MarkedCoefficients MarkedComparisonTransport

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

/-- A nontrivial finite prime-torsion represented coefficient with actual
p-group monodromy image contains an actual constant prime-cyclic line. -/
theorem exists_cyclic_mono_of_isPGroup_image
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ X)
    [GaloisCategory (Scheme.FiniteEtale X)]
    [PreGaloisCategory.FiberFunctor (fiberToFinite s)]
    (H : Grp (Over X)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom]
    {p : ℕ} [Fact p.Prime] [Nontrivial (PointModule s H)]
    (hp : ∀ a : PointModule s H, p • a = 0)
    (himage : letI := pointEvaluationAction s H
      IsPGroup p (MulAction.toPermHom (FiberAutGroup s) (PointModule s H)).range) :
    ∃ q : ConstantFinite.coefficient (ULift.{u} (ZMod p)) X ⟶ representedSheaf H,
      Mono q := by
  obtain ⟨a, ha, r, hr⟩ := exists_represented_section_of_isPGroup_image s H hp himage
  have hk : KilledBy p (representedSheaf H) :=
    representedSheaf_killedBy_of_identity_pow H p
      (identity_pow_eq_one_of_fiber s H p (fun x =>
        congrArg Additive.toMul (hp (Additive.ofMul x))))
  have hpr : p • r = 0 := by
    let T := sheafToPresheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 X)))
    have h := congrArg (fun q : representedSheaf H ⟶ representedSheaf H => T.map q) hk
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
    have hh := congrArg (fun q : T.obj (representedSheaf H) ⟶
      T.obj (representedSheaf H) => q r) h
    simpa using hh
  refine ⟨cyclicSectionMap (representedSheaf H) p r hpr,
    cyclicSectionMap_mono_of_geometric_value s H r hpr ?_⟩
  intro hz
  apply ha
  apply Additive.toMul.injective
  exact hr.symm.trans hz

end AlgebraicGeometry.Scheme.EtaleCohomology
