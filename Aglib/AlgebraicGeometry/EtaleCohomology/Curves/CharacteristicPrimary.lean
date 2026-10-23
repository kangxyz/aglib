/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ArtinSchreierVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.StructureFrobenius
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CyclicCoefficientSequence

/-!
# Characteristic-primary assembly from original structure cohomology

The original Artin–Schreier sequence and genuine cyclic extensions reduce the
characteristic-primary conclusion to the actual structure-cohomology comparison.
Proper coherent finiteness and dimension vanishing must still discharge those
geometric inputs. No perfection, smoothness or reducedness is required here.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge structureCohomologyModule

/-- Removing the redundant value lift identifies the original cyclic and AS coefficients. -/
def cyclicPrimeFieldIso (X : Scheme.{u}) (p : ℕ) :
    ConstantFinite.coefficient (ULift.{u} (ZMod p)) X ≅ primeFieldSheaf X p :=
  (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).mapIso
    ((AddEquiv.ulift : ULift.{u + 1} (ULift.{u} (ZMod p)) ≃+ ULift.{u} (ZMod p)).trans
      (AddEquiv.ulift.trans
        (AddEquiv.ulift : ULift.{u + 1} (ZMod p) ≃+ ZMod p).symm)).toAddCommGrpIso

variable {k : Type u} [Field k] [IsSepClosed k] (Y : FScheme k)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y.left)]

/-- Actual p-power vanishing once the original structure-cohomology geometric inputs are closed. -/
theorem characteristicPrimary_vanishing_of_structure_cohomology
    (p : ℕ) [Fact p.Prime] [CharP k p]
    [FiniteDimensional k (Sheaf.H.{w} (additiveStructureSheaf Y.left) 1)]
    (hvanish : ∀ q : ℕ, 1 < q →
      Subsingleton (Sheaf.H.{w} (additiveStructureSheaf Y.left) q))
    (m r : ℕ) : Subsingleton
      (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) Y.left) (m + 2)) := by
  let : Subsingleton (Sheaf.H.{w} (primeFieldSheaf Y.left p) (m + 2)) :=
    primeField_vanishing_of_structure_cohomology Y.left p (Fact.out)
      (primeCast_global_eq_zero Y p) (artinSchreier_cohomology_surjective Y p 1) hvanish m
  let e :
      Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod p)) Y.left) (m + 2) ≃+
        Sheaf.H.{w} (primeFieldSheaf Y.left p) (m + 2) :=
    ((Sheaf.functorH (Scheme.smallEtaleTopology Y.left) (m + 2)).mapIso
    (cyclicPrimeFieldIso Y.left p)).addCommGroupIsoToAddEquiv
  let : Subsingleton
      (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod p)) Y.left) (m + 2)) :=
    e.injective.subsingleton
  exact cyclicPrimePower_vanishing Y.left p (Nat.Prime.pos (Fact.out)) (m + 2) r

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
