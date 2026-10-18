/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Determinant.Gluing

/-!
# Ordered comparison of the actual top differential line with the residue twist

The original determinant isomorphism composes with the same ordered coefficient frame on the
actual exterior power of the degree-one polynomial module. The original tilde and pullback
unit comparisons and the original tensor right-unitor are retained. This gives an actual
isomorphism to `O(-(n + 1))`, the residue twist used by projective Serre after the displayed
coordinate order identifies the coordinate count with `n + 1`.

The whole native over and scheme restrictions and the original signed ratio-differential
wedge formula are proved. Changing the coordinate order changes the whole isomorphism by the
actual permutation determinant sign; the original coefficient wedge and frame have that same
explicit determinant factor. Any commutative ring, dimension zero and the zero ring are allowed,
with a supplied order and no public finiteness choice. Laurent trace normalization is a later
cohomological comparison.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
local notation "P" => ProjectiveSpace R ι
local notation "Ω" => Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
local notation "K" => moduleExteriorPower P Ω n
local notation "L" => twistingSheaf R ι (-(n + 1 : ℤ))

/-- The actual determinant isomorphism followed by its original ordered coefficient frame. -/
def differentialDeterminantTwistingIso : K ≅ L :=
  differentialDeterminantIso R ι n e ≪≫ differentialDeterminantTargetIsoTwist R ι n e

/-- The comparison uses exactly the original determinant and coefficient-trivialization maps. -/
theorem differentialDeterminantTwistingIso_hom :
    (differentialDeterminantTwistingIso R ι n e).hom =
      (differentialDeterminantIso R ι n e).hom ≫
        (differentialDeterminantTargetIsoTwist R ι n e).hom := rfl

/-- The same original chart map followed by the original coefficient frame on the over-site. -/
def differentialDeterminantTwistingOverIso (i : ι) :
    (K).over (coordinateOpen R ι i) ≅ (L).over (coordinateOpen R ι i) :=
  differentialDeterminantChartIso R ι n e i ≪≫
    (SheafOfModules.overFunctor (P).ringCatSheaf (coordinateOpen R ι i)).mapIso
      (differentialDeterminantTargetIsoTwist R ι n e)

/-- The whole native over restriction is the same original composed chart isomorphism. -/
theorem differentialDeterminantTwistingIso_over (i : ι) :
    (SheafOfModules.overFunctor (P).ringCatSheaf (coordinateOpen R ι i)).mapIso
      (differentialDeterminantTwistingIso R ι n e) =
        differentialDeterminantTwistingOverIso R ι n e i := by
  apply Iso.ext
  change (SheafOfModules.overFunctor (P).ringCatSheaf (coordinateOpen R ι i)).map
    ((differentialDeterminantIso R ι n e).hom ≫
      (differentialDeterminantTargetIsoTwist R ι n e).hom) = _
  rw [Functor.map_comp, differentialDeterminantIso_over]
  rfl

/-- The same original native scheme-restriction chart map and coefficient frame. -/
def differentialDeterminantTwistingRestrictIso (i : ι) :
    (K).restrict (coordinateOpen R ι i).ι ≅ (L).restrict (coordinateOpen R ι i).ι :=
  differentialDeterminantChartRestrictIso R ι n e i ≪≫
    (Scheme.Modules.restrictFunctor (coordinateOpen R ι i).ι).mapIso
      (differentialDeterminantTargetIsoTwist R ι n e)

/-- The whole actual scheme restriction retains the original chart and coefficient maps. -/
theorem differentialDeterminantTwistingIso_restrict (i : ι) :
    (Scheme.Modules.restrictFunctor (coordinateOpen R ι i).ι).mapIso
      (differentialDeterminantTwistingIso R ι n e) =
        differentialDeterminantTwistingRestrictIso R ι n e i := by
  apply Iso.ext
  change (Scheme.Modules.restrictFunctor (coordinateOpen R ι i).ι).map
    ((differentialDeterminantIso R ι n e).hom ≫
      (differentialDeterminantTargetIsoTwist R ι n e).hom) = _
  rw [Functor.map_comp, differentialDeterminantIso_restrict]
  rfl

/-- The original ordered ratio wedge maps to the signed original inverse-twist generator. -/
theorem differentialDeterminantTwistingIso_wedge (i : ι)
    (W : (coordinateOpen R ι i).toScheme.Opens) :
    (differentialDeterminantTwistingIso R ι n e).hom.val.app
      (op ((coordinateOpen R ι i).ι ''ᵁ W))
      ((SheafOfModulesOfCommRing.exteriorPowerMk (P).sheaf Ω n).app
        (op ((coordinateOpen R ι i).ι ''ᵁ W))
        (fun a => (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
          (eulerCoordinateRatio R ι i (e.symm ((e i).succAbove a))
            ((coordinateOpen R ι i).ι_image_le W)))) =
      (-1 : Γ(P, (coordinateOpen R ι i).ι ''ᵁ W)) ^ (e i).val •
        twistingGenerator R ι (-(n + 1 : ℤ)) i ((coordinateOpen R ι i).ι_image_le W) := by
  let U := coordinateOpen R ι i
  let T := U.ι ''ᵁ W
  let q := differentialDeterminantTargetIsoTwist R ι n e
  have h := congrArg (q.hom.val.app (op T))
    (differentialDeterminantIso_wedge R ι n e i W)
  change (differentialDeterminantTwistingIso R ι n e).hom.val.app (op T) _ = _
  exact h.trans (by
    rw [(q.hom.val.app (op T)).hom.map_smul,
      differentialDeterminantTargetIsoTwist_generator])

/-- The original pivot form evaluates arbitrary original wedges under the same comparison. -/
theorem differentialDeterminantTwistingIso_mk (i : ι)
    {T : (P).Opens} (hi : T ≤ coordinateOpen R ι i)
    (s : Fin n → Γ(Ω, T)) :
    (differentialDeterminantTwistingIso R ι n e).hom.val.app (op T)
      ((SheafOfModulesOfCommRing.exteriorPowerMk (P).sheaf Ω n).app (op T) s) =
      determinantEulerPivotForm R ι n e i hi s •
        twistingGenerator R ι (-(n + 1 : ℤ)) i hi := by
  let V := op (Over.mk (homOfLE hi))
  let w := (SheafOfModulesOfCommRing.exteriorPowerMk (P).sheaf Ω n).app (op T) s
  let q := differentialDeterminantTargetIsoTwist R ι n e
  have h := (congrArg (fun f => f.val.app V w)
    (differentialDeterminantIso_over R ι n e i)).trans
      (differentialDeterminantChartIso_mk R ι n e i hi s)
  have h' := congrArg (q.hom.val.app (op T)) h
  change q.hom.val.app (op T)
    ((differentialDeterminantIso R ι n e).hom.val.app (op T) w) = _
  exact h'.trans (by
    rw [(q.hom.val.app (op T)).hom.map_smul,
      differentialDeterminantTargetIsoTwist_generator, ← determinantEulerPivotForm_apply])

private theorem determinantBasis_reindex_comp {S M α : Type*} [CommRing S]
    [AddCommGroup M] [Module S M] (m : ℕ) (b : Module.Basis α S M)
    (e e' : α ≃ Fin m) : b.reindex e' = (b.reindex e).reindex (e.symm.trans e') := by
  apply Module.Basis.eq_of_apply_eq
  intro a
  simp only [Module.Basis.reindex_apply]
  simp

/-- Reordering uses the original degree-one basis and the displayed finite permutation. -/
theorem determinantDegreeOneBasis_reindex (e' : ι ≃ Fin (n + 1)) :
    determinantDegreeOneBasis R ι n e' =
      (determinantDegreeOneBasis R ι n e).reindex (e.symm.trans e') := by
  exact determinantBasis_reindex_comp (n + 1)
    (MvPolynomial.homogeneousDegreeOneBasis R ι) e e'

/-- The actual original coefficient wedge changes by the original permutation sign. -/
theorem determinantCoefficientGenerator_orderSign (e' : ι ≃ Fin (n + 1)) :
    determinantCoefficientGenerator R ι n e' =
      Equiv.Perm.sign (e.symm.trans e') • determinantCoefficientGenerator R ι n e := by
  let b := determinantDegreeOneBasis R ι n e
  rw [determinantCoefficientGenerator, determinantDegreeOneBasis_reindex R ι n e e']
  rw [Module.Basis.coe_reindex]
  change exteriorPower.ιMulti R (n + 1) (b ∘ (e.symm.trans e').symm) = _
  exact (exteriorPower.ιMulti R (n + 1)).map_perm b (e.symm.trans e').symm |>.trans (by
    rw [Equiv.Perm.sign_symm]
    rfl)

/-- The determinant of the actual reordered degree-one basis is the same sign in the base ring. -/
theorem determinantCoefficientBasis_det_order (e' : ι ≃ Fin (n + 1)) :
    (determinantDegreeOneBasis R ι n e).det (determinantDegreeOneBasis R ι n e') =
      ((Equiv.Perm.sign (e.symm.trans e') : ℤ) : R) := by
  let b := determinantDegreeOneBasis R ι n e
  rw [determinantDegreeOneBasis_reindex R ι n e e']
  rw [Module.Basis.coe_reindex]
  change b.det (b ∘ (e.symm.trans e').symm) = _
  rw [b.det.map_perm, b.det_self, Equiv.Perm.sign_symm]
  change (Equiv.Perm.sign (e.symm.trans e') : ℤ) • (1 : R) = _
  rw [← Int.cast_smul_eq_zsmul R, smul_eq_mul, mul_one]

/-- The same original Euler middle frame retains the displayed basis permutation. -/
theorem determinantMiddleSectionsBasis_reindex (e' : ι ≃ Fin (n + 1)) (i : ι)
    {T : (P).Opens} (hi : T ≤ coordinateOpen R ι i) :
    determinantMiddleSectionsBasis R ι n e' i hi =
      (determinantMiddleSectionsBasis R ι n e i hi).reindex (e.symm.trans e') := by
  apply Module.Basis.eq_of_apply_eq
  intro a
  simp only [Module.Basis.reindex_apply, determinantMiddleSectionsBasis_apply]
  simp

/-- The original scalar pivot form retains that same actual frame determinant sign. -/
theorem determinantEulerPivotForm_orderSign (e' : ι ≃ Fin (n + 1)) (i : ι)
    {T : (P).Opens} (hi : T ≤ coordinateOpen R ι i) (s : Fin n → Γ(Ω, T)) :
    determinantEulerPivotForm R ι n e' i hi s =
      Equiv.Perm.sign (e.symm.trans e') • determinantEulerPivotForm R ι n e i hi s := by
  change (determinantMiddleSectionsBasis R ι n e' i hi).det
    (Matrix.vecCons (eulerMiddleGenerator R ι i i hi)
      (fun a => (eulerDifferential R ι).val.app (op T) (s a))) = _
  rw [determinantMiddleSectionsBasis_reindex R ι n e e' i hi, Module.Basis.det_reindex]
  exact (determinantMiddleSectionsBasis R ι n e i hi).det.map_perm _ (e.symm.trans e')


private theorem determinantZsmul_hom_app (X : Scheme.{u}) {M N : X.Modules}
    (z : ℤ) (f : M ⟶ N) (T : X.Opens) (s : M.val.obj (op T)) :
    (z • f).val.app (op T) s = z • f.val.app (op T) s := by
  change (((SheafOfModules.forget X.ringCatSheaf).map (z • f)).app (op T)) s = _
  erw [Functor.map_zsmul, PresheafOfModules.zsmul_app]
  rfl

private theorem determinantInt_smul_assoc {S : Type*} [CommRing S]
    {M : Type*} [AddCommGroup M] [Module S M] (z : ℤ) (r : S) (m : M) :
    (z • r) • m = z • (r • m) := by
  calc
    (z • r) • m = ((z : S) * r) • m := by
      rw [← Int.cast_smul_eq_zsmul S]
      rfl
    _ = (z : S) • (r • m) := (smul_smul (z : S) r m).symm
    _ = z • (r • m) := Int.cast_smul_eq_zsmul S z (r • m)

/-- Reordering the displayed coefficient basis changes the whole twist comparison by its sign. -/
theorem differentialDeterminantTwistingIso_orderSign (e' : ι ≃ Fin (n + 1)) :
    differentialDeterminantTwistingIso R ι n e' =
      Equiv.Perm.sign (e.symm.trans e') • differentialDeterminantTwistingIso R ι n e := by
  apply Iso.ext
  let z : ℤ := Equiv.Perm.sign (e.symm.trans e')
  change (differentialDeterminantTwistingIso R ι n e').hom =
    z • (differentialDeterminantTwistingIso R ι n e).hom
  have hlocal (i : ι) :
      (SheafOfModules.overFunctor (P).ringCatSheaf (coordinateOpen R ι i)).map
        (differentialDeterminantTwistingIso R ι n e').hom =
      (SheafOfModules.overFunctor (P).ringCatSheaf (coordinateOpen R ι i)).map
        (z • (differentialDeterminantTwistingIso R ι n e).hom) := by
    let U := coordinateOpen R ι i
    apply (cancel_epi (moduleExteriorPowerOverIso P Ω n U).hom).mp
    apply SheafOfModulesOfCommRing.exteriorPower_hom_ext
      ((P).sheaf.over U) ((Ω).over U) ((L).over U) n
    intro V s
    change (differentialDeterminantTwistingIso R ι n e').hom.val.app
        ((Over.forget U).op.obj V)
        ((moduleExteriorPowerOverIso P Ω n U).hom.val.app V
          ((SheafOfModulesOfCommRing.exteriorPowerMk ((P).sheaf.over U)
            ((Ω).over U) n).app V s)) =
      (z • (differentialDeterminantTwistingIso R ι n e).hom).val.app
        ((Over.forget U).op.obj V)
        ((moduleExteriorPowerOverIso P Ω n U).hom.val.app V
          ((SheafOfModulesOfCommRing.exteriorPowerMk ((P).sheaf.over U)
            ((Ω).over U) n).app V s))
    simp only [moduleExteriorPowerOverIso_hom_mk]
    change (differentialDeterminantTwistingIso R ι n e').hom.val.app (op V.unop.left)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (P).sheaf Ω n).app
          (op V.unop.left) s) =
      (z • (differentialDeterminantTwistingIso R ι n e).hom).val.app (op V.unop.left)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (P).sheaf Ω n).app
          (op V.unop.left) s)
    rw [determinantZsmul_hom_app]
    let T := V.unop.left
    let hi : T ≤ coordinateOpen R ι i := leOfHom V.unop.hom
    let g : (L).val.obj (op T) := twistingGenerator R ι (-(n + 1 : ℤ)) i hi
    have hl := differentialDeterminantTwistingIso_mk R ι n e' i hi s
    have hr := differentialDeterminantTwistingIso_mk R ι n e i hi s
    have hf := determinantEulerPivotForm_orderSign R ι n e e' i hi s
    exact hl.trans ((congrArg (β := (L).val.obj (op T))
      (fun r : Γ(P, T) => r • g) hf).trans
        ((determinantInt_smul_assoc z _ g).trans (congrArg (z • ·) hr.symm)))
  apply hom_ext_of_coordinateSubopens R ι
  intro i T hi s
  exact congrArg (fun f => f.val.app (op (Over.mk (homOfLE hi))) s) (hlocal i)


/-- The original ordered frame on the actual coefficient exterior power retains its sign. -/
theorem determinantCoefficientFrame_orderSign (e' : ι ≃ Fin (n + 1))
    (x : determinantCoefficientModule R ι n) :
    determinantCoefficientFrame R ι n e x =
      ((Equiv.Perm.sign (e.symm.trans e') : ℤ) : R) *
        determinantCoefficientFrame R ι n e' x := by
  exact (determinantCoefficientFrame_changeBasis R ι n e
    (determinantDegreeOneBasis R ι n e') x).trans (by
      rw [determinantCoefficientBasis_det_order]
      rfl)


end AlgebraicGeometry.ProjectiveSpace
