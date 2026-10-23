/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.ActionDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Representatives
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperHenselian.General

/-! # Original finite constant H1 under proper henselian closed-fibre restriction -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u w w'

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

section Restriction

variable {X S : Scheme.{u}} (f : S ⟶ X)
  [(Scheme.FiniteEtale.baseChange f).IsEquivalence]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- An actual finite-cover equivalence lifts every represented finite torsor class,
retaining the original H1 pullback and its native represented-coefficient isomorphism. -/
theorem represented_h1Pullback_surjective
    (G : Grp (Over X)) [IsCommMonObj G.X] [IsFinite G.X.hom] [Etale G.X.hom]
    (hG : IsFiniteLocallyConstant (representedSheaf G)) :
    Function.Surjective (h1Pullback f (representedSheaf G)) := by
  intro c
  let F := Scheme.FiniteEtale.baseChange f
  let G₀ := baseChangedGroup f G
  let eG := representedSheafBaseChangeIso f G
  have hG₀ : IsFiniteLocallyConstant (representedSheaf G₀) :=
    (isFiniteLocallyConstant_iff_of_iso eG).mp (isFiniteLocallyConstant_pullback f hG)
  obtain ⟨a, ha⟩ := (stacks03AJ S).bijective (representedSheaf G₀) |>.surjective
    (coefficientIso eG c)
  revert ha
  refine Quotient.inductionOn a ?_
  intro P hP
  change torsorExtClass P = coefficientIso eG c at hP
  let Y₀ := P.finiteEtaleRepresentative (stacks03RV S) hG₀
  let eP := P.finiteEtaleRepresentativeIso (stacks03RV S) hG₀
  have hY₀ : Surjective Y₀.obj.hom := P.represented_surjective G₀ Y₀ eP
  let σ := P.representedSchemeAction G₀ Y₀ eP
  let Y := F.objPreimage Y₀
  let e := F.objObjPreimageIso Y₀
  let eY := (Scheme.FiniteEtale.forget S).mapIso e
  have hFY : Surjective (F.obj Y).obj.hom := by
    have heq : eY.hom.left ≫ Y₀.obj.hom = (F.obj Y).obj.hom := Over.w eY.hom
    have : IsIso ((Over.forget S).map eY.hom) := inferInstance
    have : Surjective eY.hom.left := inferInstance
    rw [← heq]
    infer_instance
  have hY : Surjective Y.obj.hom := ActionDescent.surjective_of_baseChange f Y
  let τ := ActionDescent.transportCarrier σ eY
  let α := ActionDescent.descendedAction f G Y τ
  let Q := torsorOfSchemeAction G Y α
  let θ : Torsor.Iso (torsorOfSchemeAction G₀ (F.obj Y) τ)
      (torsorOfSchemeAction G₀ Y₀ σ) :=
    torsorOfSchemeActionIso G₀ (F.obj Y) Y₀ τ σ eY (by
      intro T b x
      change (σ.act b (x ≫ eY.hom) ≫ eY.inv) ≫ eY.hom = σ.act b (x ≫ eY.hom)
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  have hclass : torsorExtClass (torsorOfSchemeAction G₀ (F.obj Y) τ) =
      coefficientIso eG c :=
    (torsorExtClass_iso (θ.trans (P.representedSchemeActionIso G₀ Y₀ eP))).trans hP
  refine ⟨torsorExtClass Q, ?_⟩
  apply (coefficientIso eG).injective
  have h := SchemeTorsorBaseChange.torsorExtClass_pullbackSchemeAction f G Y α
  rw [ActionDescent.pullback_descendedAction] at h
  exact h.trans hclass

/-- The actual H1 pullback is surjective for every finite locally constant
coefficient when the actual finite-cover restriction is an equivalence. -/
theorem h1Pullback_surjective_of_isEquivalence
    (L : AbelianSheaf.{u, u + 1} X) (hL : IsFiniteLocallyConstant L) :
    Function.Surjective (h1Pullback f L) := by
  let D := CoefficientRepresentation.ofFiniteLocallyConstant L (stacks03RV X) hL
  have hD : IsFiniteLocallyConstant (representedSheaf D.group) :=
    (isFiniteLocallyConstant_iff_of_iso D.iso).mpr hL
  intro c
  obtain ⟨a, ha⟩ := (represented_h1Pullback_surjective f D.group hD)
    ((coefficientIso ((inverseImage f).mapIso D.iso)).symm c)
  refine ⟨coefficientMap D.iso.hom a, ?_⟩
  rw [h1Pullback_coefficientMap, ha]
  exact (coefficientIso ((inverseImage f).mapIso D.iso)).apply_symm_apply c

/-- Fullness detects classes and essential surjectivity lifts them, for the
original map and every actual finite locally constant abelian coefficient. -/
theorem h1Pullback_bijective_of_isEquivalence
    (L : AbelianSheaf.{u, u + 1} X) (hL : IsFiniteLocallyConstant L) :
    Function.Bijective (h1Pullback f L) :=
  ⟨FiniteEtaleRigidity.h1Pullback_injective_finite_of_full f
      (stacks03AJ X) (stacks03RV X) (stacks03AJ S) L hL,
    h1Pullback_surjective_of_isEquivalence f L hL⟩

end Restriction

section ProperLocal

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1}
    (pullback p (LocalRing.residueSpecMap R)))]

/-- Original finite locally constant H1 restricts bijectively to the actual
closed residue fibre over every proper henselian local base. -/
theorem properHenselian_h1Pullback_bijective
    (L : AbelianSheaf.{u, u + 1} X) (hL : IsFiniteLocallyConstant L) :
    Function.Bijective (h1Pullback (pullback.fst p (LocalRing.residueSpecMap R)) L) := by
  let := Scheme.FiniteEtale.properHenselian_baseChange_isEquivalence p
  exact h1Pullback_bijective_of_isEquivalence _ L hL

variable (A : Type u) [AddCommGroup A] [Finite A]

/-- The original H1 map with finite constant coefficients is bijective after
closed-residue pullback, followed by the canonical inverse-image constant isomorphism.
No order-invertibility, marking, Galois, or fundamental-group hypothesis is used. -/
theorem properHenselian_pullbackH1_bijective :
    Function.Bijective (pullbackH1 A (pullback.fst p (LocalRing.residueSpecMap R))) := by
  exact (coefficientIso ((inverseImageConstantIso
    (pullback.fst p (LocalRing.residueSpecMap R))).app (value A))).bijective.comp
      (properHenselian_h1Pullback_bijective p _ (isFiniteLocallyConstant A X))

/-- In particular, every actual closed-fibre finite constant H1 class lifts. -/
theorem properHenselian_pullbackH1_surjective :
    Function.Surjective (pullbackH1 A (pullback.fst p (LocalRing.residueSpecMap R))) :=
  (properHenselian_pullbackH1_bijective p A).surjective

end ProperLocal
end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
