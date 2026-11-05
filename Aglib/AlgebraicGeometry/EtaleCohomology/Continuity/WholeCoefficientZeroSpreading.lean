/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.GenericCoefficientZeroSpreading
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! # Coefficient-open zero on one unchanged whole source cover

The coefficient generic fibre is the direct original base change over the
coefficient domain. Its actual lift to the source fibre gives the complete
cover reconstruction by native inverse-image composition. Fraction continuity
then restricts only the coefficient base; it never restricts the source base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.WholeCoefficient

universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard

variable (A B E : Type u) [CommRing A] [CommRing B] [Field E]
    [Algebra A B] [Algebra B E]
    {X F : Scheme.{u}} (p : X ⟶ Spec (.of A)) (f : F ⟶ Spec (.of A))
    (a : Spec (.of E) ⟶ F)
    (ha : a ≫ f = Spec.algebraMap B E ≫ Spec.algebraMap A B)

local notation "YB" => pullback p (Spec.algebraMap A B)
local notation "b" => pullback.snd p (Spec.algebraMap A B)
local notation "D" => pullback b (Spec.algebraMap B E)
local notation "δ" => pullback.fst b (Spec.algebraMap B E)
local notation "ε" => pullback.snd b (Spec.algebraMap B E)
local notation "π" => pullback.fst p f

/-- The direct original coefficient generic fibre maps to the original source
fibre using its specified two projections. -/
def genericMap : D ⟶ pullback p f :=
  pullback.lift (δ ≫ pullback.fst p (Spec.algebraMap A B)) (ε ≫ a) (by
    calc
      _ = δ ≫ (b ≫ Spec.algebraMap A B) := by
        rw [Category.assoc, pullback.condition]
      _ = (ε ≫ Spec.algebraMap B E) ≫ Spec.algebraMap A B := by
        rw [← Category.assoc, pullback.condition]
      _ = (ε ≫ a) ≫ f := by
        simpa only [Category.assoc] using congrArg (fun m => ε ≫ m) ha.symm)

@[reassoc (attr := simp)]
theorem genericMap_source :
    genericMap A B E p f a ha ≫ π = δ ≫ pullback.fst p (Spec.algebraMap A B) :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem genericMap_field :
    genericMap A B E p f a ha ≫ pullback.snd p f = ε ≫ a :=
  pullback.lift_snd ..

variable (G : FiniteEtale X) (Z : FiniteEtale (pullback p f))
    (r : (baseChange (pullback.fst p f)).obj G ≅ Z)

local notation "C" => Functor.obj (baseChange (pullback.fst p (Spec.algebraMap A B))) G
local notation "ZE" => Functor.obj (baseChange (genericMap A B E p f a ha)) Z

/-- The same global cover is reconstructed on the original coefficient generic fibre. -/
def coverReconstruction : (baseChange δ).obj C ≅ ZE :=
  (baseChangeComp (pullback.fst p (Spec.algebraMap A B)) δ).symm.app G ≪≫
    eqToIso (congrArg (fun m => (baseChange m).obj G)
      (genericMap_source A B E p f a ha).symm) ≪≫
    (baseChangeComp π (genericMap A B E p f a ha)).app G ≪≫
    (baseChange (genericMap A B E p f a ha)).mapIso r

include r in
/-- Generic zero gives a nonempty principal coefficient-open zero on the
actual coefficient pullback of the unchanged whole source cover. -/
theorem exists_open_zero_of_reconstruction [IsDomain B] [IsFractionRing B E]
    [QuasiCompact p] [QuasiSeparated p]
    {T : Scheme.{u}} (h : pullback p (Spec.algebraMap A B) ⟶ T)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} T)]
    (M : AbelianSheaf.{u, u + 1} T) (degree : ℕ) (c : Sheaf.H.{eX} M degree)
    (hc : cohomologyPullback.{u, eX, u + 2}
      ((ZE).obj.hom ≫ δ ≫ h) M degree c = 0) :
    ∃ t : Finset B⁰, denominator B⁰ t ≠ 0 ∧ Nonempty (stageBaseOpen B⁰ t) ∧
      cohomologyPullback.{u, eX, u + 2}
        ((stageSourceOpen B⁰ ((C).obj.hom ≫ b) t).ι ≫ (C).obj.hom ≫ h) M degree c = 0 := by
  let eR := coverReconstruction A B E p f a ha G Z r
  let : QuasiSeparatedSpace (YB : Scheme.{u}) := quasiSeparatedSpace_of_quasiSeparated b
  let : QuasiSeparatedSpace (C).obj.left :=
    quasiSeparatedSpace_of_quasiSeparated ((C).obj.hom ≫ b)
  let : CompactSpace (C).obj.left :=
    QuasiCompact.compactSpace_of_compactSpace ((C).obj.hom ≫ b)
  have hz : eR.hom.hom.left ≫ ((ZE).obj.hom ≫ δ ≫ h) =
      pullback.fst (C).obj.hom δ ≫ ((C).obj.hom ≫ h) := by
    have ho : eR.hom.hom.left ≫ (ZE).obj.hom = pullback.snd (C).obj.hom δ :=
      Over.w eR.hom.hom
    have hp := pullback.condition (f := (C).obj.hom) (g := δ)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ δ ≫ h) ho).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ h) hp.symm).trans (Category.assoc _ _ _))))
  exact exists_fraction_principalOpen_composite_zero_of_reconstruction.{u, eX, u + 2, u + 2}
    B E ((C).obj.hom ≫ b) ((C).obj.hom ≫ h)
    (pullback.fst (C).obj.hom δ) (pullback.snd (C).obj.hom δ ≫ ε)
    ((IsPullback.of_hasPullback (C).obj.hom δ).paste_vert
      (IsPullback.of_hasPullback b (Spec.algebraMap B E)))
    eR.hom.hom.left ((ZE).obj.hom ≫ δ ≫ h) hz M degree c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.WholeCoefficient
