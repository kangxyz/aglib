/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteLocalFactors
public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Standard

/-!
# Original cohomology of finite strictly local components

A finite local algebra over a strictly local base has no positive original
small-etale cohomology, for every actual abelian sheaf. Apply this in particular
to the native localization at any maximal point of a finite algebra. The base,
algebra, coefficient and Ext universes are not identified.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u v w

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Positive original cohomology vanishes on any finite local algebra over a
strictly local base, in the native coefficient universe of the target scheme. -/
theorem finiteLocal_subsingleton_H
    (B : Type v) [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B]
    [HasSheafify (Scheme.smallEtaleTopology (Spec (.of B))) AddCommGrpCat.{v + 1}]
    [HasExt.{w} (AbelianSheaf.{v, v + 1} (Spec (.of B)))]
    (F : AbelianSheaf.{v, v + 1} (Spec (.of B))) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} F q) := by
  let := HenselianLocalRing.of_finite_local_algebra R B
  let := HenselianLocalRing.residueField_isSepClosed_of_finite_local_algebra R B
  exact StrictlyLocal.subsingleton_H_standard B F q hq

/-- The same vanishing for the literal selected maximal localization of a finite
algebra. No separability or torsion condition is imposed on the coefficient sheaf. -/
theorem localizationAtPrime_subsingleton_H
    (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
    (p : Ideal A) [p.IsMaximal]
    [HasSheafify (Scheme.smallEtaleTopology (Spec (.of (Localization.AtPrime p))))
      AddCommGrpCat.{v + 1}]
    [HasExt.{w} (AbelianSheaf.{v, v + 1} (Spec (.of (Localization.AtPrime p))))]
    (F : AbelianSheaf.{v, v + 1} (Spec (.of (Localization.AtPrime p))))
    (q : ℕ) (hq : 0 < q) : Subsingleton (Sheaf.H.{w} F q) := by
  let := HenselianLocalRing.finite_localizationAtPrime R A p
  exact finiteLocal_subsingleton_H R (Localization.AtPrime p) F q hq

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
