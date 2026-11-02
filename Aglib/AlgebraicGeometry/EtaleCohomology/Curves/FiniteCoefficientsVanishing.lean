/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteCoefficientsVanishing.Open
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Proper
public import Aglib.AlgebraicGeometry.Geometrically.Connected.PointedCurve

/-!
# Proper-curve applications of original finite-local-system high vanishing

The original public proper-curve API is retained. Its coefficient tensor,
p-group, Sylow/coprime and positive-annihilator proofs are supplied once by
the generic original-R coefficient family. The finite-type dimension/roots
application discharges its actual prime-constant tests. Original coefficients,
cohomology maps, conditions and independent Ext worlds are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

open Constructible.Modules

universe u r w w'

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  Coefficients.hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : FScheme k) (hX : Curve.Properties X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

include hX

/-- The actual prime-field constant coefficient has zero cohomology above
degree two, by the existing cyclic and roots vanishing theorem. -/
theorem primeField_subsingleton_H_of_proper_curve
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k)) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{w} (primeFieldSheaf X.left p) q) := by
  let : LocallyOfFiniteType X.hom := Curve.curveProperties_locallyOfFiniteType hX
  let := hX.proper
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact primeField_high_subsingleton_of_finiteType_curve X.left X.hom
    hX.topologicalKrullDim_eq_one.le p hunit q hq

/-- Every original finite constant module killed by an invertible prime has
zero cohomology above degree two, retaining its original coefficient action. -/
theorem constantModuleSheaf_subsingleton_H_of_prime_nsmul
    (R : Type r) [CommRing R] [Finite R]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k)) (q : ℕ) (hq : 2 < q)
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] (hM : ∀ m : M, p • m = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj
      ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)) := by
  exact Constructible.Modules.constantCohomology_subsingleton_of_prime_field
    X.left R p q (primeField_subsingleton_H_of_proper_curve X hX p hunit q hq) M hM

/-- Actual prime-killed modules trivialized by an actual p-group finite étale
cover have zero cohomology above degree two on the original proper curve. -/
theorem moduleSheaf_subsingleton_H_of_pGroup_trivialization
    [ConnectedSpace X.left] (R : Type r) [CommRing R] [Finite R]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k))
    (Y : Scheme.FiniteEtale X.left) [PreGaloisCategory.IsGalois Y]
    [Surjective Y.obj.hom] [ConnectedSpace Y.obj.left]
    [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (hY : IsPGroup p (Aut Y)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R X.left) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  exact Constructible.Modules.moduleSheaf_cohomology_subsingleton_of_pGroup_trivialization
    X.left R p q (primeField_subsingleton_H_of_proper_curve X hX p hunit q hq)
    Y hY F M hM t

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)] in
/-- A connected actual finite étale cover of the original proper curve is
again a proper smooth geometrically connected curve over the same field. -/
theorem curveProperties_of_connected_finiteEtale
    (Y : Scheme.FiniteEtale X.left) [ConnectedSpace Y.obj.left] :
    Curve.Properties (Over.mk (Y.obj.hom ≫ X.hom)) := by
  let Z : FScheme k := Over.mk (Y.obj.hom ≫ X.hom)
  change Curve.Properties Z
  let : ConnectedSpace Z.left := inferInstanceAs (ConnectedSpace Y.obj.left)
  let := hX.smooth
  let := hX.proper
  let : SmoothOfRelativeDimension 1 Z.hom := by
    change SmoothOfRelativeDimension 1 (Y.obj.hom ≫ X.hom)
    have h := smoothOfRelativeDimension_comp 0 1 Y.obj.hom X.hom
    simpa only [Nat.zero_add] using h
  let : IsProper Z.hom := inferInstanceAs (IsProper (Y.obj.hom ≫ X.hom))
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : IsNoetherian Z.left := ⟨⟩
  let : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set Z.left).Nonempty) isOpen_univ.isLocallyClosed
  exact ⟨inferInstance, inferInstance,
    Scheme.geometricallyConnected_of_pointed_proper_smooth_curve Z.hom
      (pointOfClosedPoint Z.hom x hx) (pointOfClosedPoint_comp Z.hom x hx)⟩

/-- The actual Sylow quotient and the original coprime trace retraction remove
the p-group condition on the finite Galois cover. Its degree need not be
coprime to the coefficient prime. -/
theorem moduleSheaf_subsingleton_H_of_galois_prime_trivialization
    [ConnectedSpace X.left] (R : Type r) [CommRing R] [Finite R]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k))
    (Y : Scheme.FiniteEtale X.left) [PreGaloisCategory.IsGalois Y]
    [Surjective Y.obj.hom]
    [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R X.left) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  let : IsNoetherian X.left := Curve.curveProperties_isNoetherian hX
  let : LocallyOfFiniteType X.hom := Curve.curveProperties_locallyOfFiniteType hX
  let : ConnectedSpace Y.obj.left :=
    Scheme.FiniteEtale.Connectedness.connectedSpace_of_categoricalConnected Y
  apply Constructible.Modules.moduleSheaf_cohomology_subsingleton_of_galois_prime_trivialization
    X.left R p q ?_ Y F M hM t
  intro Z
  let : CompactSpace Z.obj.left := QuasiCompact.compactSpace_of_compactSpace Z.obj.hom
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Z.obj.left) := hasExtStandard Z.obj.left
  have hdimZ : topologicalKrullDim Z.obj.left ≤ 1 :=
    dimension_le_one_of_etale Z.obj.hom hX.topologicalKrullDim_eq_one.le
  exact primeField_high_subsingleton_of_finiteType_curve Z.obj.left
    (Z.obj.hom ≫ X.hom) hdimZ p hunit q hq

/-- Every finite-LCC coefficient killed by an invertible prime has zero
original module cohomology above degree two. Its global cover is constructed. -/
theorem moduleSheaf_subsingleton_H_of_prime_nsmul
    (R : Type r) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (p : ℕ) [Fact p.Prime] (hunit : IsUnit (p : k)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R X.left) (hF : IsFiniteTypeLocallyConstant F)
    (hp : p • 𝟙 F = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  let : LocallyOfFiniteType X.hom := Curve.curveProperties_locallyOfFiniteType hX
  let := hX.proper
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact moduleSheaf_high_subsingleton_of_finiteType_curve X.left X.hom
    hX.topologicalKrullDim_eq_one.le R p (Fact.out : p.Prime).pos hunit q hq F hF hp

/-- Every finite-LCC coefficient with a positive invertible annihilator has
zero original cohomology above degree two. The prime dévissage uses the actual
kernel and cokernel of scalar multiplication on the same coefficient sheaf. -/
theorem moduleSheaf_subsingleton_H_of_pos_nsmul
    (R : Type r) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf R X.left) (hF : IsFiniteTypeLocallyConstant F)
    (hkill : n • 𝟙 F = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  let : ConnectedSpace X.left := Curve.curveProperties_connectedSpace hX
  let : LocallyOfFiniteType X.hom := Curve.curveProperties_locallyOfFiniteType hX
  let := hX.proper
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact moduleSheaf_high_subsingleton_of_finiteType_curve X.left X.hom
    hX.topologicalKrullDim_eq_one.le R n hn hunit q hq F hF hkill

/-- Positive lifted-ZMod finite local systems on the proper curve have zero
original cohomology above degree two, including composite levels and level one. -/
theorem uLiftZMod_moduleSheaf_subsingleton_H_of_curve
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 < q)
    (F : ModuleSheaf (ULift.{u + 1} (ZMod n)) X.left)
    (hF : IsFiniteTypeLocallyConstant F) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology
      (ULift.{u + 1} (ZMod n)) q).obj F) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1}).Full :=
    ModuleCat.uLiftZMod_forget₂_full n
  apply moduleSheaf_subsingleton_H_of_pos_nsmul X hX
    (ULift.{u + 1} (ZMod n)) n hn hunit q hq F hF
  apply ObjectProperty.hom_ext
  ext V m
  change n • m = 0
  rw [← Nat.cast_smul_eq_nsmul (R := ULift.{u + 1} (ZMod n))]
  have hnzero : (n : ULift.{u + 1} (ZMod n)) = 0 := by
    apply ULift.ext
    simp
  rw [hnzero, zero_smul]

/-- The same proper finite-LCC vanishing on the original native unit-Ext
carrier. Module and abelian Ext universes remain independent. -/
theorem moduleUnitExt_subsingleton_of_finiteLocallyConstant
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 < q)
    [HasExt.{w'} (Coefficients.ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
    (M : Coefficients.ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hM : IsFiniteTypeLocallyConstant
      ((Coefficients.moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj M)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{w'}
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) M q) := by
  let F := (Coefficients.moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj M
  let : Subsingleton (Sheaf.H.{w}
      ((moduleUnderlying (ULift.{u + 1} (ZMod n)) X.left).obj F) q) :=
    uLiftZMod_moduleSheaf_subsingleton_H_of_curve X hX n hn hunit q hq F hM
  let E : CategoryTheory.Abelian.Ext.{w'}
      (moduleUnit X.left (ULift.{u + 1} (ZMod n))) M q ≃+
      Sheaf.H.{w} ((moduleUnderlying (ULift.{u + 1} (ZMod n)) X.left).obj F) q :=
    (etaleModuleExtCohomologyAddEquivLargeScalars X.left
    (Coefficients.constantRing X.left (ULift.{u + 1} (ZMod n))) M q).trans
      (((Sheaf.functorH X.left.smallEtaleTopology q).mapIso
        ((Coefficients.moduleSheafInverseUnderlyingIso X.left
          (ULift.{u + 1} (ZMod n))).app M).symm).addCommGroupIsoToAddEquiv)
  exact E.injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
