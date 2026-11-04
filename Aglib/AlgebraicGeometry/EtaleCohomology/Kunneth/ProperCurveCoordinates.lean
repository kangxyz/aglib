/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Rank
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PointPurity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kunneth.ConstantMap

/-! Constant unit Ext on the original smooth proper curve has free graded coordinates. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve

universe u w

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

/-- The ranks in the original constant-coefficient table of a proper curve. -/
def properCurveConstantRank (genus : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 2 * genus
  | 2 => 1
  | _ + 3 => 0

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{w} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]

/-- Graded coordinates on the native module-unit Ext of the proper curve,
through the original constant-coefficient cohomology comparison. -/
@[no_expose]
def properCurveConstantModuleExtAddEquiv (p : ℕ) :
    constantModuleExt.{u, w} n X.left p ≃+
      (Fin (properCurveConstantRank (coherentGenus k X) p) → ZMod n) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X.left) := hasExtStandard X.left
  let e (q : ℕ) := (etaleModuleExtCohomologyAddEquivLargeScalars X.left (constantRing X.left Λ)
    (moduleUnit X.left Λ) q).trans
    (((Sheaf.functorH (Scheme.smallEtaleTopology X.left) q).mapIso
      (moduleUnitCoefficientIso X.left n)).addCommGroupIsoToAddEquiv).symm
  let e1 := (AddEquiv.piUnique (fun _ : Fin 1 => ZMod n)).symm
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero (n : k) := ⟨hunit.ne_zero⟩
  match p with
  | 0 =>
    exact (e 0).trans ((Curves.constantZeroAddEquiv hX n hn hunit).trans
      ((Kummer.HenselianConstant.fieldCyclicCoordinates k n).symm.trans e1))
  | 1 => exact (e 1).trans (Curves.constantOneRankAddEquiv hX n hn hunit)
  | 2 =>
    exact (e 2).trans ((Curves.constantTwoAddEquiv hX n hn hunit
      (modulePoint_globalLevelInvertible n hunit)).trans e1)
  | q + 3 =>
    have h := Curves.constant_subsingleton_H_of_curve hX n hn hunit
      (modulePoint_globalLevelInvertible n hunit) (q + 3) (by omega)
    let : Subsingleton (constantModuleExt.{u, w} n X.left (q + 3)) :=
      ⟨fun a b => (e (q + 3)).injective (h.elim _ _)⟩
    change constantModuleExt.{u, w} n X.left (q + 3) ≃+ (Fin 0 → ZMod n)
    exact AddEquiv.ofBijective (0 : constantModuleExt.{u, w} n X.left (q + 3) →+
      (Fin 0 → ZMod n))
        ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, by funext i; exact i.elim0⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
