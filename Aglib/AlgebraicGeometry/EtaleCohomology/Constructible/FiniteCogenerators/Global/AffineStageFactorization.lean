/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.Restriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.AffineCharts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.AffineIntegralConstants.Factorization

/-! # Original affine restriction maps through their actual finite stages

The original relative restriction isomorphism and original affine chart
identify the original direct image on a Spec chart. Ambient FP factors that
same original coefficient arrow through an actual finite-generated stage.
The complete stage, map and original equation are retained together.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

open AffineIntegralConstants

attribute [local instance] hasSheafifyLarge

/-- The original constant pushforward on the original affine Spec chart. -/
def affineConstantPushforwardRestrictionIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (B : Type u) [AddCommGroup B] [Finite B] (U : X.AffineZariskiSite) :
    letI := (f.app U.1).hom.toAlgebra
    (inverseImage U.2.fromSpec).obj
        ((constantPushforwardFunctor (X := X) B).obj (op (Over.mk f))) ≅
      (constantPushforwardFunctor (X := Spec Γ(X, U.1)) B).obj
        (op (Over.mk (Spec.algebraMap Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1)))) := by
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact (constantPushforwardRestrictionIso U.2.fromSpec B).app (op (Over.mk f)) ≪≫
    (constantPushforwardFunctor (X := Spec Γ(X, U.1)) B).mapIso
      (relativeAffineChartObjectIso f U).op

/-- One actual local finite-generated stage and the original map factoring
the original restricted coefficient arrow through its original cocone leg. -/
structure AffineConstantStage
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (B : Type u) [AddCommGroup B] [Finite B] (F : AbelianSheaf.{u, u + 1} X)
    (α : F ⟶ (constantPushforwardFunctor (X := X) B).obj (op (Over.mk f)))
    (U : X.AffineZariskiSite) where
  stage : Finset Γ(Y, f ⁻¹ᵁ U.1)
  map :
    letI := (f.app U.1).hom.toAlgebra
    (inverseImage U.2.fromSpec).obj F ⟶
      (constantPushforwardDiagram Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) B).obj (op (op stage))
  factor :
    letI := (f.app U.1).hom.toAlgebra
    map ≫ (constantPushforwardCocone Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) B).ι.app
        (op (op stage)) =
      (inverseImage U.2.fromSpec).map α ≫ (affineConstantPushforwardRestrictionIso f B U).hom

/-- FP of the original affine restriction supplies this actual stage and
the original coefficient factorization, without an integral hypothesis. -/
theorem nonempty_affineConstantStage
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (B : Type u) [AddCommGroup B] [Finite B] (F : AbelianSheaf.{u, u + 1} X)
    (α : F ⟶ (constantPushforwardFunctor (X := X) B).obj (op (Over.mk f)))
    (U : X.AffineZariskiSite)
    [IsFinitelyPresentable.{u + 1} ((inverseImage U.2.fromSpec).obj F)] :
    Nonempty (AffineConstantStage f B F α U) := by
  let R : CommRingCat.{u} := Γ(X, U.1)
  let A : CommRingCat.{u} := Γ(Y, f ⁻¹ᵁ U.1)
  let : Algebra R A := (f.app U.1).hom.toAlgebra
  obtain ⟨s, b, hb⟩ := exists_constantPushforward_stage_factorization R A B
    ((inverseImage U.2.fromSpec).obj F)
    ((inverseImage U.2.fromSpec).map α ≫ (affineConstantPushforwardRestrictionIso f B U).hom)
  exact ⟨{ stage := s, map := b, factor := hb }⟩

/-- Choose the actual stage together with its original map and equation. -/
def affineConstantStage
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (B : Type u) [AddCommGroup B] [Finite B] (F : AbelianSheaf.{u, u + 1} X)
    (α : F ⟶ (constantPushforwardFunctor (X := X) B).obj (op (Over.mk f)))
    (U : X.AffineZariskiSite)
    [IsFinitelyPresentable.{u + 1} ((inverseImage U.2.fromSpec).obj F)] :
    AffineConstantStage f B F α U :=
  Classical.choice (nonempty_affineConstantStage f B F α U)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
