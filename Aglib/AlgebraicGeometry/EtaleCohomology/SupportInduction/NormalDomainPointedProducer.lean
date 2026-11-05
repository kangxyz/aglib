/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.NormalDomainProducer
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointedTargetRestriction

/-! # Original pointed normal-domain effacement in any Cartesian presentation

The actual field-valued section point determines an affine open target chart.
Its algebra action and point triangle are retained, and the produced etale
stage is composed with that open immersion. A specified original Cartesian
family is compared with the native pullback using its actual isomorphism and
coefficient carrier. The same original class and field point are returned.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients TwoFieldEffacement
open _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Finite
  _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Normal-domain effacement with the complete original geometric point and
arbitrary actual Cartesian family. The target chart is genuinely an affine
open, not an arbitrary affine map, and its mark retains the original field. -/
theorem exists_normal_domain_pointed_H1_zero_of_lower_rank
    (d : ℕ) (ih : ∀ q < d, PointedCurveModuleInjectiveH1Effacement.{u} q)
    (A B k K : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field k] [Field K]
    [Algebra A B] [Algebra A k] [IsFractionRing A k]
    [Algebra A K] [Algebra B K] [IsFractionRing B K] [Algebra k K]
    [IsScalarTower A B K] [IsScalarTower A k K]
    (hA : IsNagataRing.{u, 0} A) (hB : IsNagataRing.{u, 0} B)
    (hd : ringKrullDim B ≤ (d : ℕ))
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F]
      (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of A)),
      IsAffine (pullback p z : Scheme.{u}))
    (a : Y ⟶ X) (b : Y ⟶ Spec (CommRingCat.of B))
    (H : IsPullback a b p (Spec.algebraMap A B))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf (Spec (CommRingCat.of B)) (ULift.{u + 1} (ZMod n))) [Injective I]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
        (ULift.{u + 1} (ZMod n)))).obj I)) 1)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A)) :
    ∃ (U : X.Etale) (xU : Spec (CommRingCat.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ≫ σ ∧
      cohomologyPullback.{u, eY, u + 2} (pullback.snd U.hom a) _ 1 c = 0 := by
  let M := (SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
    (ULift.{u + 1} (ZMod n)))).obj I
  let E : (inverseImage H.isoPullback.inv).obj ((inverseImage b).obj M) ≅
      (inverseImage (pullback.snd p (Spec.algebraMap A B))).obj M :=
    ((inverseImageComp b H.isoPullback.inv).symm.app M) ≪≫
      eqToIso (congrArg (fun f => (inverseImage f).obj M) H.isoPullback_inv_snd)
  let c₀ := Sheaf.H.map E.hom 1
    (cohomologyPullback.{u, eY, u + 2} H.isoPullback.inv ((inverseImage b).obj M) 1 c)
  obtain ⟨R₀, hR₀, hAlg, e, he, hxe⟩ := exists_affineSpec_chart_of_fieldPoint Ω (x ≫ σ)
  let : CommRing R₀ := hR₀
  let : Algebra R₀ Ω := hAlg
  let : IsOpenImmersion e := he
  have hpoint : (Spec.algebraMap R₀ Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ := by
    rw [hxe]
    exact ⟨x (IsLocalRing.closedPoint Ω), rfl⟩
  obtain ⟨V, hV⟩ := exists_normal_domain_affine_stage_H1_zero_of_lower_rank
    d ih A B k K R₀ Ω hA hB hd p σ hσ haff e hpoint n hn hunit I c₀
  let t : Spec (.of V.algebra) ⟶ Spec (.of R₀) := (etaleObject R₀ Ω V).hom
  let : Etale t := (etaleObject R₀ Ω V).prop
  let U : X.Etale := Scheme.Etale.mk (t ≫ e)
  let xU : Spec (CommRingCat.of Ω) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom V.point.toRingHom)
  have hxU : xU ≫ U.hom = x ≫ σ := by
    change Spec.map (CommRingCat.ofHom V.point.toRingHom) ≫ (t ≫ e) = _
    exact (Category.assoc (Spec.map (CommRingCat.ofHom V.point.toRingHom)) t e).symm.trans
      ((congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R₀) => f ≫ e)
        (stagePoint_over R₀ Ω V)).trans hxe)
  have hcanon : cohomologyPullback.{u, eY, u + 2}
      (pullback.snd U.hom (pullback.fst p (Spec.algebraMap A B)) ≫ H.isoPullback.inv)
      ((inverseImage b).obj M) 1 c = 0 :=
    (coefficient_iso_restriction_zero_iff_composite_zero H.isoPullback.inv
      (pullback.snd U.hom (pullback.fst p (Spec.algebraMap A B)))
      ((inverseImage b).obj M) _ E 1 c).mp hV
  let l : pullback U.hom a ⟶
      pullback U.hom (pullback.fst p (Spec.algebraMap A B)) :=
    pullback.lift (pullback.fst U.hom a) (pullback.snd U.hom a ≫ H.isoPullback.hom)
      (by rw [Category.assoc, H.isoPullback_hom_fst]; exact pullback.condition)
  have hlf : l ≫ pullback.snd U.hom (pullback.fst p (Spec.algebraMap A B)) =
      pullback.snd U.hom a ≫ H.isoPullback.hom := pullback.lift_snd ..
  have hl : l ≫
      (pullback.snd U.hom (pullback.fst p (Spec.algebraMap A B)) ≫ H.isoPullback.inv) =
        pullback.snd U.hom a := by
    rw [← Category.assoc, hlf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact ⟨U, xU, hxU, original_class_zero_of_map_law l _ _ hl _ 1 c hcanon⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
