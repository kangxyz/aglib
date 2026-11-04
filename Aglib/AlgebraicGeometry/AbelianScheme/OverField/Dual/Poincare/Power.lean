/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare
public import Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified.Power

/-!
# The original Poincare parameter-power isomorphism

On the single locally Noetherian universal parameter, the original Picard
addition law identifies the two actual rigidified pairs. All other parameters
receive the pullback of this isomorphism. Its source and parameter unit laws
use the same rigidifications as the original Poincare pair.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible Scheme.Group

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsProper G.hom] [GeometricallyIntegral G.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

local notation "D" => picardIdentityComponent G.hom P R

/-- The power of the original Poincare pair is the actual parameter pullback
along multiplication by `n`. Existence uses the supplied representation at
its locally Noetherian identity component. -/
def poincarePowerIso (n : ℕ) :
    RigidifiedPair.Iso ((poincareRigidifiedPair G P R).power n)
      (poincarePullback G P R ((𝟙 D) ^ n)) := by
  letI := picardCommGrpObj G.hom P R
  let i : D ⟶ P.obj := picardIdentityComponentι G.hom P R
  let : IsMonHom i := isMonHom_picardIdentityComponentι G.hom P R
  let : IsLocallyNoetherian (D).left := LocallyOfFiniteType.isLocallyNoetherian (D).hom
  let T : LocallyNoetherianOver (Spec (.of k)) := ⟨D, inferInstance⟩
  let Q := poincareRigidifiedPair G P R
  let a := classOf (pullback G.hom (D).hom) Q.bundle
  let q : PicardGroup (pullback G.hom (D).hom) →+
      (fppfPicardSheaf G.hom).obj.obj (op D) :=
    ((quotientProjection G.hom ≫ toFppfPicardSheaf G.hom).app (op D)).hom
  let E : Additive (D ⟶ P.obj) ≃+ (fppfPicardSheaf G.hom).obj.obj (op D) :=
    picardHomAddEquiv G.hom P R T
  have hI : q a = E (Additive.ofMul i) := by
    have h := poincarePullback_fppfClass G P R (T := T) (𝟙 D)
    change q (classOf (pullback G.hom (D).hom)
      (poincarePullback G P R (𝟙 D)).bundle) = E (Additive.ofMul (𝟙 D ≫ i)) at h
    have hc : classOf (pullback G.hom (D).hom) (poincarePullback G P R (𝟙 D)).bundle = a :=
      Quotient.sound ⟨(poincarePullbackIdIso G P R).iso⟩
    rw [hc, Category.id_comp] at h
    exact h
  refine (poincarePullbackIsoOfFppfClass G P R (T := T) ((𝟙 D) ^ n) (Q.power n) ?_).symm
  change E (Additive.ofMul (((𝟙 D) ^ n) ≫ i)) = q (classOf _ (Q.power n).bundle)
  have hi : ((𝟙 D) ^ n) ≫ i = i ^ n := by rw [MonObj.pow_comp, Category.id_comp]
  rw [hi, _root_.ofMul_pow, map_nsmul, RigidifiedPair.classOf_power, map_nsmul, hI]

/-- Source-origin normalization makes the actual universal isomorphism unique. -/
theorem poincarePowerIso_unique (n : ℕ)
    (e : RigidifiedPair.Iso ((poincareRigidifiedPair G P R).power n)
      (poincarePullback G P R ((𝟙 D) ^ n))) : e = poincarePowerIso G P R n :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (by simp) _ _

/-- The same universal isomorphism on any test, through the original
power and pullback comparisons. -/
def poincarePullbackPowerIso {T : Over (Spec (.of k))} (f : T ⟶ D) (n : ℕ) :
    RigidifiedPair.Iso ((poincarePullback G P R f).power n)
      (poincarePullback G P R (f ≫ (𝟙 D) ^ n)) :=
  (RigidifiedPair.mapPowerIso f (poincareRigidifiedPair G P R) n).symm.trans
    ((RigidifiedPair.Iso.map f (poincarePowerIso G P R n)).trans
      (poincarePullbackCompIso G P R f ((𝟙 D) ^ n)).symm)

/-- On actual bundles the comparison uses the original native power
comparison and the pullback of the same universal map. -/
theorem poincarePullbackPowerIso_iso {T : Over (Spec (.of k))} (f : T ⟶ D) (n : ℕ) :
    (poincarePullbackPowerIso G P R f n).iso =
      (PowerPullback.pullbackPowerIso ((familyScheme G.hom).map f)
        (poincareRigidifiedPair G P R).bundle n).symm ≪≫
      (Scheme.Modules.pullback ((familyScheme G.hom).map f)).mapIso
        (poincarePowerIso G P R n).iso ≪≫
      (poincarePullbackCompIso G P R f ((𝟙 D) ^ n)).iso.symm := rfl

/-- Composition of arbitrary tests respects the original normalized comparison. -/
theorem poincarePullbackPowerIso_naturality {T T' : Over (Spec (.of k))}
    (a : T' ⟶ T) (f : T ⟶ D) (n : ℕ) :
    ((poincarePullbackCompIso G P R a f).power n).trans
        ((RigidifiedPair.mapPowerIso a (poincarePullback G P R f) n).symm.trans
          (RigidifiedPair.Iso.map a (poincarePullbackPowerIso G P R f n))) =
      (poincarePullbackPowerIso G P R (a ≫ f) n).trans
        ((RigidifiedPair.mapCongrIso (Category.assoc a f ((𝟙 D) ^ n))
          (poincareRigidifiedPair G P R)).trans
          (poincarePullbackCompIso G P R a (f ≫ (𝟙 D) ^ n))) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (by simp) _ _

omit [GrpObj G] [IsProper G.hom] [GeometricallyIntegral G.hom] in
/-- Multiplication preserves the original parameter unit on every test. -/
theorem poincarePower_unit_comp (T : Over (Spec (.of k))) (n : ℕ) :
    (1 : T ⟶ D) ≫ (𝟙 D) ^ n = 1 := by
  rw [MonObj.comp_pow, Category.comp_id, one_pow]

/-- Restriction to the parameter unit is the original canonical power of
the unit trivialization, with its original source rigidification. -/
theorem poincarePullbackPowerIso_unit (T : Over (Spec (.of k))) (n : ℕ) :
    (poincarePullbackPowerIso G P R (1 : T ⟶ D) n).trans
        ((RigidifiedPair.mapCongrIso (poincarePower_unit_comp G P R T n)
          (poincareRigidifiedPair G P R)).trans (poincareUnitIso G P R T)) =
      ((poincareUnitIso G P R T).power n).trans
        (RigidifiedPair.trivialPowerIso T n) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    G.hom η[G].left (by simp) _ _

end AlgebraicGeometry.Scheme.RelativePicard
