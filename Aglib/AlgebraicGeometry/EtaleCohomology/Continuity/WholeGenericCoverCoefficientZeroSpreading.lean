/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.GenericCoefficientZeroSpreading
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.GenericLocalWholePointedExtension

/-! # Original arbitrary-coefficient zero on the same whole cover

A complete generic-fibre reconstruction of a cover on the whole target
transports a supplied original generic zero to that same cover. Existing
arbitrary-coefficient continuity then supplies a nonzero principal open of
the coefficient-support base. The original cover and its pointed extension
are not replaced or restricted in the construction. The resulting open need
not contain a closed point and no generic zero is produced by this theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u eX e eY

attribute [local instance] hasSheafifyLarge

/-- The complete original generic reconstruction supplied by whole-target
extension carries an arbitrary original class-zero to a nonempty principal
coefficient-base open of the same whole cover. Source, reconstructed-cover,
and localization-system Ext worlds remain independent. -/
theorem exists_wholeGenericCover_principalOpen_cohomologyPullback_eq_zero
    (R : Type u) [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
    (G : FiniteEtale X) [CompactSpace G.obj.left] [QuasiSeparatedSpace G.obj.left]
    (Y : FiniteEtale (pullback p
      ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))))))
    (E : (FiniteEtale.baseChange (pullback.fst p
      ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R)))))).obj G ≅ Y)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y.obj.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} G.obj.left)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback G.obj.hom (pullback.fst p
        ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R)))))))]
    [HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback (G.obj.hom ≫ p)
        ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))))))]
    [∀ s : Finset R⁰, HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((PrincipalNeighborhoodLimit.baseChangeDiagram R⁰ (G.obj.hom ≫ p)).obj (op s)))]
    [∀ s : Finset R⁰, HasExt.{e} (AbelianSheaf.{u, u + 1}
      (stageSourceOpen R⁰ (G.obj.hom ≫ p) s))]
    [HasColimitsOfShape (Finset R⁰) AddCommGrpCat.{e}] [UnivLE.{u, e}]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{eX} F q)
    (hc : cohomologyPullback.{u, eX, eY}
      (Y.obj.hom ≫ pullback.fst p
        ((Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))))) F q c = 0) :
    ∃ s : Finset R⁰, denominator R⁰ s ≠ 0 ∧ Nonempty (stageBaseOpen R⁰ s) ∧
      cohomologyPullback.{u, eX, e}
        ((stageSourceOpen R⁰ (G.obj.hom ≫ p) s).ι ≫ G.obj.hom) F q c = 0 := by
  let γ := (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R)))
  let B : Scheme.{u} := pullback p γ
  let π : B ⟶ X := pullback.fst p γ
  let T : Scheme.{u} := pullback G.obj.hom π
  let pG := G.obj.hom ≫ p
  let a : T ⟶ G.obj.left := pullback.fst G.obj.hom π
  let b : T ⟶ Spec (Spec (.of R)).functionField :=
    pullback.snd G.obj.hom π ≫ pullback.snd p γ
  let z : T ⟶ Y.obj.left := E.hom.hom.left
  have he : z ≫ Y.obj.hom = pullback.snd G.obj.hom π := Over.w E.hom.hom
  have hz : z ≫ (Y.obj.hom ≫ π) = a ≫ G.obj.hom := by
    rw [← Category.assoc, he]
    exact (pullback.condition (f := G.obj.hom) (g := π)).symm
  have H : IsPullback a b pG γ :=
    (IsPullback.of_hasPullback G.obj.hom π).paste_vert (IsPullback.of_hasPullback p γ)
  let : Algebra R (Spec (.of R)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of R)
  let : IsFractionRing R (Spec (.of R)).functionField :=
    functionField_isFractionRing_of_affine (.of R)
  have hγ : γ = Spec.algebraMap R (Spec (.of R)).functionField :=
    Spec.fromSpecStalk_eq' (.of R) (genericPoint (Spec (.of R)))
  let : HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback pG (Spec.algebraMap R (Spec (.of R)).functionField))) :=
    (congrArg (fun δ => HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback pG δ))) hγ).mp
      (inferInstance : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback pG γ)))
  have Hγ : IsPullback a b pG (Spec.algebraMap R (Spec (.of R)).functionField) :=
    (congrArg (fun δ => IsPullback a b pG δ) hγ).mp H
  exact exists_fraction_principalOpen_composite_zero_of_reconstruction
    R (Spec (.of R)).functionField pG G.obj.hom a b Hγ z (Y.obj.hom ≫ π) hz F q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
