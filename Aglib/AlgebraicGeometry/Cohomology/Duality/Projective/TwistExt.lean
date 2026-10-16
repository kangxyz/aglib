/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
# Native Ext from original projective twists

The actual twist tensor equivalence promotes its adjunction to native Ext. Original right
unit and twist multiplication isomorphisms then identify Ext from a twist to another twist
with original sheaf cohomology of the difference. The sharp twist calculation proves the
positive Ext vanishing used in coherent Serre duality, over every commutative base ring.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Native Ext between actual twists identifies additively with the original cohomology of
the difference twist, using the original tensor functors and original unit and product maps. -/
def twistingExtCohomologyAddEquiv (a b : ℤ) (q : ℕ) :
    Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
        (twistingSheaf R ι a) (twistingSheaf R ι b) q ≃+
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
        (twistingSheaf R ι (-a + b))) q := by
  let X := ProjectiveSpace R ι
  let O := SheafOfModules.unit X.ringCatSheaf
  let T := twistingTensorEquivalence R ι a
  letI : T.functor.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι a)).Additive
  letI : T.inverse.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι (-a))).Additive
  let e₁ : Ext.{u + 1} (C := X.Modules) (twistingSheaf R ι a)
      (twistingSheaf R ι b) q ≃+
      Ext.{u + 1} (C := X.Modules) (T.functor.obj O) (twistingSheaf R ι b) q :=
    (((extFunctor (C := X.Modules) q).mapIso (twistingTensorUnitIso R ι a).op).app
      (twistingSheaf R ι b)).addCommGroupIsoToAddEquiv
  let e₂ : Ext.{u + 1} (C := X.Modules) (T.functor.obj O) (twistingSheaf R ι b) q ≃+
      Ext.{u + 1} (C := X.Modules) O (T.inverse.obj (twistingSheaf R ι b)) q :=
    T.toAdjunction.extEquiv
  let e₃ : Ext.{u + 1} (C := X.Modules) O (T.inverse.obj (twistingSheaf R ι b)) q ≃+
      Ext.{u + 1} (C := X.Modules) O (twistingSheaf R ι (-a + b)) q :=
    ((extFunctorObj O q).mapIso (twistingTensorIso R ι (-a) b)).addCommGroupIsoToAddEquiv
  exact e₁.trans (e₂.trans (e₃.trans
    (moduleExtCohomologyAddEquiv X (twistingSheaf R ι (-a + b)) q)))

/-- The original positive Ext groups between two actual twists vanish in the sharp
nonnegative-cohomology range of the difference twist. -/
theorem twistingExt_subsingleton_of_neg_le_difference (n : ℕ) (e : ι ≃ Fin (n + 1))
    (a b : ℤ) (q : ℕ) (hd : -(n : ℤ) ≤ -a + b) (hq : q ≠ 0) :
    Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι a) (twistingSheaf R ι b) q) := by
  let := twistingCohomology_subsingleton_of_neg_le_degree R ι n e (-a + b) q hd hq
  exact (twistingExtCohomologyAddEquiv R ι a b q).injective.subsingleton

/-- Sufficiently negative actual twists have no positive Ext into the original dualizing
 twist. The cardinal bound is retained and dimension zero is included. -/
theorem negativeTwistExt_dualizing_subsingleton [Fintype ι]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : ℕ) (hN : Fintype.card ι ≤ N)
    (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι (-(N : ℤ)))
      (twistingSheaf R ι (-(Fintype.card ι : ℤ))) q) :=
  twistingExt_subsingleton_of_neg_le_difference R ι n e _ _ q (by
    have hN' : (Fintype.card ι : ℤ) ≤ N := by exact_mod_cast hN
    omega) hq

end AlgebraicGeometry.Scheme.Cohomology
