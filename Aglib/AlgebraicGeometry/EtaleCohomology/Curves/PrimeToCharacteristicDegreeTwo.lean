/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ResidueFiber
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant.Naturality
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Henselian.General

/-!
# Degree-two comparison from the original Picard lift

For a finite cover of the projective line over a strictly henselian local ring,
the original degree-two restriction with cyclic coefficients is surjective
provided the target's original Kummer boundary is surjective. This is an explicit
intermediate: the target boundary hypothesis is not proved here. There is no
arithmetic marking or Noetherian hypothesis on the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w w'

attribute [local instance] hasSheafifyLarge

private theorem cohomologyIso_leftInverse {C : Type*} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    {L M : Sheaf J AddCommGrpCat.{u}} (e : L ≅ M) (q : ℕ) :
    Function.LeftInverse (Sheaf.H.map e.inv q) (Sheaf.H.map e.hom q) := by
  intro a
  rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]

private theorem roots_two_surjective_of_picard
    {X S : Scheme.{u}} (f : S ⟶ X)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (hpic : Function.Surjective (pullbackClass f))
    (hboundary : Function.Surjective (picardBoundary S n hn (levelInvertible f n hinv))) :
    Function.Surjective (rootsCohomologyPullback f n hn hinv 2) := by
  intro a
  obtain ⟨c, hc⟩ := hboundary a
  obtain ⟨d, hd⟩ := hpic c
  refine ⟨picardBoundary X n hn hinv d, ?_⟩
  exact (picardBoundary_pullback f n hn hinv d).trans
    ((congrArg (picardBoundary S n hn (levelInvertible f n hinv)) hd).trans hc)

private theorem constant_two_surjective_of_picard
    {X S : Scheme.{u}} (f : S ⟶ X)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (e : ConstantFinite.coefficient (ULift.{u} (ZMod n)) X ≅ mu X n)
    (hpic : Function.Surjective (pullbackClass f))
    (hboundary : Function.Surjective (picardBoundary S n hn (levelInvertible f n hinv))) :
    Function.Surjective (constantRestriction (ULift.{u} (ZMod n)) f 2) := by
  intro a
  let eS := transportConstantRootIso f n hn hinv e
  obtain ⟨b, hb⟩ := roots_two_surjective_of_picard f n hn hinv hpic hboundary
    (Sheaf.H.map eS.hom 2 a)
  refine ⟨Sheaf.H.map e.inv 2 b, ?_⟩
  apply (cohomologyIso_leftInverse eS 2).injective
  have hnat := transportConstantRootIso_cohomology f n hn hinv e 2
    (Sheaf.H.map e.inv 2 b)
  refine hnat.trans ?_
  exact (congrArg (rootsCohomologyPullback f n hn hinv 2)
    (cohomologyIso_leftInverse e.symm 2 b)).trans hb

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {Y : Scheme.{u}} (p : Y ⟶ ProjectiveLine.projectiveP1 R) [IsFinite p]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (residueFiber p))]

/-- The original degree-two cyclic restriction is surjective once the target's original
Kummer boundary is surjective. The base may be non-Noetherian; no marking is an input. -/
theorem finite_projectiveLine_constantRestriction_two_surjective_of_picardBoundary_surjective
    (n : ℕ) (hn : 0 < n) (hR : IsUnit (n : Γ(Spec (.of R), ⊤)))
    (hboundary : Function.Surjective (picardBoundary (residueFiber p) n hn
      (levelInvertible
        (pullback.fst (p ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) n
        (levelInvertible (p ≫ ProjectiveLine.structureMap R) n hR)))) :
    Function.Surjective (constantRestriction (ULift.{u} (ZMod n))
      (pullback.fst (p ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) 2) := by
  exact constant_two_surjective_of_picard
    (pullback.fst (p ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
    n hn (levelInvertible (p ≫ ProjectiveLine.structureMap R) n hR)
    (constantRootIsoOver R n hn hR (p ≫ ProjectiveLine.structureMap R))
    (pullbackClass_residue_finite_projectiveLine_surjective R p) hboundary

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
