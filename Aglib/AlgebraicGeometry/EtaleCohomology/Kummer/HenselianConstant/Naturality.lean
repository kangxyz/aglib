/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-!
# Compatible constant-root coordinates for geometric pullback

Choose the target coordinate by pulling the source coordinate through the
original constant and root transports. This retains the original pullback in
every degree and requires no independently chosen arithmetic marking.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant

universe u w w'
variable {X S : Scheme.{u}} (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))

/-- Transport an actual source coordinate through the canonical coefficient comparisons. -/
def transportConstantRootIso
    (e : ConstantFinite.coefficient (ULift.{u} (ZMod n)) X ≅ mu X n) :
    ConstantFinite.coefficient (ULift.{u} (ZMod n)) S ≅ mu S n :=
  ((inverseImageConstantIso f).app (ConstantFinite.value (ULift.{u} (ZMod n)))).symm ≪≫
    (inverseImage f).mapIso e ≪≫ rootsPullbackIso f n hn hinv

/-- The coefficient square retains the exact original constant and root transports. -/
theorem transportConstantRootIso_square
    (e : ConstantFinite.coefficient (ULift.{u} (ZMod n)) X ≅ mu X n) :
    ((inverseImageConstantIso f).app (ConstantFinite.value (ULift.{u} (ZMod n)))).hom ≫
        (transportConstantRootIso f n hn hinv e).hom =
      (inverseImage f).map e.hom ≫ (rootsPullbackIso f n hn hinv).hom := by
  simp only [transportConstantRootIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Original all-degree constant pullback is conjugate to original roots pullback. -/
theorem transportConstantRootIso_cohomology
    (e : ConstantFinite.coefficient (ULift.{u} (ZMod n)) X ≅ mu X n) (q : ℕ)
    (a : Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X) q) :
    Sheaf.H.map (transportConstantRootIso f n hn hinv e).hom q
        (Sheaf.H.map
          ((inverseImageConstantIso f).app (ConstantFinite.value (ULift.{u} (ZMod n)))).hom q
          (cohomologyPullback f (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X) q a)) =
      rootsCohomologyPullback f n hn hinv q (Sheaf.H.map e.hom q a) := by
  rw [← Sheaf.H.map_comp_apply, transportConstantRootIso_square,
    Sheaf.H.map_comp_apply, ← cohomologyPullback_coefficientMap]
  rfl

/-- A strictly henselian base supplies source coordinates for this square without a marking. -/
theorem henselianConstantRoot_cohomology
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] (p : X ⟶ Spec (.of R))
    (hR : IsUnit (n : Γ(Spec (.of R), ⊤))) (q : ℕ)
    (a : Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X) q) :
    Sheaf.H.map
        (transportConstantRootIso f n hn (levelInvertible p n hR)
          (constantRootIsoOver R n hn hR p)).hom q
        (Sheaf.H.map
          ((inverseImageConstantIso f).app (ConstantFinite.value (ULift.{u} (ZMod n)))).hom q
          (cohomologyPullback f (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X) q a)) =
      rootsCohomologyPullback f n hn (levelInvertible p n hR) q
        (Sheaf.H.map (constantRootIsoOver R n hn hR p).hom q a) :=
  transportConstantRootIso_cohomology f n hn (levelInvertible p n hR)
    (constantRootIsoOver R n hn hR p) q a

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant
