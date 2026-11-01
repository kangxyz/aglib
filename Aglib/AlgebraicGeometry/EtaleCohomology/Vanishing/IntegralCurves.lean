/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.CurveGaloisCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ConstructibleCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ConstructiblePrimeReduction
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GenericTrivializationConstructible
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CurveCompletionBoundary

/-! # Torsion cohomology vanishing on proper integral curves

An actual dense Galois trivialization of a constructible prime coefficient is
split by its Sylow quotient. The actual finite completion of that quotient
and its zero-dimensional boundary supply the geometric inputs to the original
trace argument. Original localization removes the omitted boundary of the
initial curve. Prime reduction, constructible presentations and the factorial
annihilator colimit then give every internally torsion abelian coefficient.

The field is separably closed, not necessarily perfect. The curve need not be
normal or smooth. The final coefficient has no global annihilator hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

open Constructible.Modules

universe u e

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Every genuine constructible prime coefficient on a proper integral curve
has zero original cohomology above degree two, in every characteristic. -/
theorem subsingleton_H_of_constructible_zmod_of_proper_integral_curve
    {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (p : ℕ) [Fact p.Prime] (F : ModuleSheaf (ZMod p) X)
    (hF : IsConstructible F) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{e} ((moduleUnderlying (ZMod p) X).obj F) q) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  let t := denseGaloisConstantTrivializationOfConstructible F hF
  let : IsAffine t.base := t.affine_base
  let : IsOpenImmersion t.inclusion := t.open_inclusion
  let : IsDominant t.inclusion := t.dense_inclusion
  let : ConnectedSpace t.base := t.connected_base
  let : PreGaloisCategory.IsGalois t.cover := t.galois_cover
  let : ConnectedSpace t.cover.obj.left := t.connected_cover
  let : Surjective t.cover.obj.hom := t.surjective_cover
  let : IsAffine t.cover.obj.left := isAffine_of_isAffineHom t.cover.obj.hom
  let : Module.Finite (ZMod p) t.value := t.finite_value
  let P : Sylow p (Aut t.cover) := Classical.choice inferInstance
  let Z : Scheme.FiniteEtale t.base :=
    Scheme.FiniteEtale.galoisSubgroupQuotient t.cover P.toSubgroup
  obtain ⟨C, j', b, hj', _, hb, _, hdimC, sq, D, i, hi, hcompC, hdimD⟩ :=
    Scheme.exists_finite_proper_completion_with_boundary_of_fieldCurve
      f hdim Z.obj.hom t.inclusion
  let : IsOpenImmersion j' := hj'
  let : IsFinite b := hb
  let : IsClosedImmersion i := hi
  let E := (moduleInverseImage (ZMod p) t.inclusion).obj F
  let t' : (moduleInverseImage (ZMod p) t.cover.obj.hom).obj E ≅
      (constantSheaf t.cover.obj.left.smallEtaleTopology (ModuleCat.{u + 1} (ZMod p))).obj
        t.value :=
    ((moduleInverseImageComp (ZMod p) t.inclusion t.cover.obj.hom).app F).symm ≪≫ t.iso
  have hvalue (x : t.value) : p • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod p), ZMod.natCast_self, zero_smul]
  let : Subsingleton (Sheaf.H.{e} ((etaleLowerShriek t.inclusion).obj
      ((moduleUnderlying (ZMod p) t.base).obj E)) q) :=
    subsingleton_H_etaleLowerShriek_of_galois_finite_completion
      f t.inclusion (ZMod p) t.cover p P b j' sq i hcompC hdimC hdimD E t.value hvalue t' q hq
  let A := (moduleUnderlying (ZMod p) X).obj F
  let d : (moduleUnderlying (ZMod p) t.base).obj E ≅
      (inverseImage t.inclusion).obj A :=
    (moduleInverseImageUnderlyingIso (ZMod p) t.inclusion).app F
  have hleft : Subsingleton (Sheaf.H.{e} ((etaleLowerShriek t.inclusion).obj
      ((inverseImage t.inclusion).obj A)) q) :=
    (cohomologyMapIso_bijective ((etaleLowerShriek t.inclusion).mapIso d) q).surjective.subsingleton
  obtain ⟨B, a, ha, hcomp, hdimB⟩ :=
    t.inclusion.exists_closedComplement_topologicalKrullDim_le 0 (by simpa using hdim)
  let : IsClosedImmersion a := ha
  exact (subsingleton_H_etaleLowerShriek_restrict_iff
    f t.inclusion a hcomp (by simpa using hdimB) A q (by omega)).mp hleft

/-- Proper integral dimension-at-most-one schemes over separably closed fields
have original torsion étale cohomological dimension at most two. Internal
torsion, rather than a uniform exponent, is the final coefficient condition. -/
theorem subsingleton_H_of_isTorsion_of_proper_integral_curve
    {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : 2 < q) : Subsingleton (Sheaf.H.{e} F q) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  apply subsingleton_H_of_isTorsion_of_constructible q ?_ F hF
  intro G hG
  apply subsingleton_H_of_constructible_of_prime_zmod q ?_ G hG
  intro p _ M hM
  exact subsingleton_H_of_constructible_zmod_of_proper_integral_curve f hdim p M hM q hq

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
