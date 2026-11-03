/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.GenericCoefficientZeroSpreading
public import
  Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.CoefficientBaseChangeReconstruction

/-! # The original reconstructed coefficient cover on a principal open

The whole coefficient-generic square and the original common-field map feed
arbitrary-coefficient fraction continuity directly. The supplied generic zero
is retained as an explicit hypothesis; this theorem does not produce that zero
or assert that the nonempty principal open contains a prescribed closed point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u eX e eZ
attribute [local instance] hasSheafifyLarge

variable (A B F E : Type u) [CommRing A] [CommRing B] [IsDomain B]
  [Field F] [Field E] [Algebra A B] [Algebra A F] [Algebra A E] [Algebra B E]
  [IsScalarTower A B E] [IsFractionRing B E] (a : F →ₐ[A] E)
  {X : Scheme.{u}} (p : X ⟶ Spec (.of A))
  (G : FiniteEtale X) (Z : FiniteEtale (pullback p (Spec.algebraMap A F)))
  (r : (baseChange (pullback.fst p (Spec.algebraMap A F))).obj G ≅ Z)

local notation "Y" => pullback p (Spec.algebraMap A B)
local notation "h" => pullback.fst p (Spec.algebraMap A B)
local notation "b" => pullback.snd p (Spec.algebraMap A B)
local notation "δ" => pullback.fst b (Spec.algebraMap B E)
local notation "gCE" => coefficientGenericMap A B F E a p
local notation "GB" => Functor.obj (baseChange h) G
local notation "ZE" => Functor.obj (baseChange gCE) Z

include r in
/-- A supplied original generic class zero on the original reconstructed
cover spreads on the coefficient base, without changing the fraction field,
coefficient sheaf, class, or any of the original projection maps. -/
theorem exists_coefficientGenericCover_principalOpen_zero
    [CompactSpace (GB).obj.left] [QuasiSeparatedSpace (GB).obj.left]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (GB).obj.left)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} (ZE).obj.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (GB).obj.hom δ))]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback ((GB).obj.hom ≫ b) (Spec.algebraMap B E)))]
    [∀ s : Finset B⁰, HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((PrincipalNeighborhoodLimit.baseChangeDiagram B⁰ ((GB).obj.hom ≫ b)).obj (op s)))]
    [∀ s : Finset B⁰, HasExt.{e} (AbelianSheaf.{u, u + 1}
      (stageSourceOpen B⁰ ((GB).obj.hom ≫ b) s))]
    [HasColimitsOfShape (Finset B⁰) AddCommGrpCat.{e}] [UnivLE.{u, e}]
    (M : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (c : Sheaf.H.{eX} M q)
    (hc : cohomologyPullback.{u, eX, eZ} ((ZE).obj.hom ≫ δ) M q c = 0) :
    ∃ s : Finset B⁰, denominator B⁰ s ≠ 0 ∧ Nonempty (stageBaseOpen B⁰ s) ∧
      cohomologyPullback.{u, eX, e}
        ((stageSourceOpen B⁰ ((GB).obj.hom ≫ b) s).ι ≫ (GB).obj.hom) M q c = 0 := by
  let eR := coefficientGenericCoverReconstruction A B F E a p G Z r
  have hz : eR.hom.hom.left ≫ ((ZE).obj.hom ≫ δ) =
      pullback.fst (GB).obj.hom δ ≫ (GB).obj.hom := by
    rw [← Category.assoc, coefficientGenericCoverReconstruction_over]
    exact (pullback.condition (f := (GB).obj.hom) (g := δ)).symm
  exact exists_fraction_principalOpen_composite_zero_of_reconstruction
    B E ((GB).obj.hom ≫ b) (GB).obj.hom
    (pullback.fst (GB).obj.hom δ)
    (pullback.snd (GB).obj.hom δ ≫ pullback.snd b (Spec.algebraMap B E))
    (coefficientGenericCover_isPullback (A := A) (B := B) (E := E) (p := p) G)
    eR.hom.hom.left ((ZE).obj.hom ≫ δ) hz M q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
