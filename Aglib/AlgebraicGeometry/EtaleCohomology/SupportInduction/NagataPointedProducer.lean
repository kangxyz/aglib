/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.NormalArrayAffineProducer
public import Aglib.AlgebraicGeometry.Spec.MinimalPrimeNormalizationArrow

/-! # The complete arbitrary Nagata-arrow induction step

Every coefficient minimal-prime normalization and its actual kernel-normalized
source are retained. Their unchanged normal arrows form a finite two-axis
family. Its coefficient cover is surjective and its dimensions stay within
the original bound. The full finite-array producer returns the original class
and mark; no injectivity or normality of the original rings is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients
open AlgebraicGeometry.Scheme.EtaleCohomology.Finite
open AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The full induction step for arbitrary Nagata rings and an arbitrary
original coefficient arrow, without a local-zero premise. -/
theorem exists_nagata_arrow_pointed_H1_zero_of_lower_rank
    (d : ℕ) (ih : ∀ q < d, PointedCurveModuleInjectiveH1Effacement.{u} q)
    (A B : Type u)
    [CommRing A]
    [CommRing B]
    (f : A →+* B)
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
    (H : IsPullback a b p (Spec.map (CommRingCat.ofHom f)))
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
  classical
  let : IsNoetherianRing B := hB.isNoetherianRing
  let : Fintype (minimalPrimes B) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := B)).fintype
  let R (i : minimalPrimes B) : Type u := RingHom.MinimalPrimeNormalization.sourceComponent f i
  let S (i : minimalPrimes B) : Type u := Algebra.minimalPrimeNormalization B i
  have hR (i : minimalPrimes B) :=
    RingHom.MinimalPrimeNormalization.sourceComponent_properties f hA i
  have hS (i : minimalPrimes B) :=
    RingHom.MinimalPrimeNormalization.coefficientComponent_properties hB i
  let : ∀ i, CommRing (R i) := fun i => inferInstance
  let : ∀ i, CommRing (S i) := fun i => inferInstance
  let : ∀ i, IsDomain (R i) := fun i => (hR i).1
  let : ∀ i, IsIntegrallyClosed (R i) := fun i => (hR i).2.1
  let : ∀ i, IsDomain (S i) := fun i => (hS i).2.1
  let : ∀ i, IsIntegrallyClosed (S i) := fun i => (hS i).2.2.1
  let r (i : minimalPrimes B) : R i →+* S i := RingHom.MinimalPrimeNormalization.componentMap f i
  let s (i : minimalPrimes B) : A →+* R i := RingHom.MinimalPrimeNormalization.sourceMap f i
  let t (i : minimalPrimes B) : B →+* S i := algebraMap B (S i)
  obtain ⟨R₀, hR₀, hAlg, e, he, hxe⟩ :=
    exists_affineSpec_chart_of_fieldPoint Ω (x ≫ σ)
  let : CommRing R₀ := hR₀
  let : Algebra R₀ Ω := hAlg
  let : IsOpenImmersion e := he
  have hpoint : (Spec.algebraMap R₀ Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ := by
    rw [hxe]
    exact ⟨x (IsLocalRing.closedPoint Ω), rfl⟩
  have hsquare (i : minimalPrimes B) : (r i).comp (s i) = (t i).comp f :=
    RingHom.MinimalPrimeNormalization.componentMap_sourceMap f i
  have hgfinite : IsFinite (Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (t i)))) :=
    MinimalPrimeNormalizationArrow.coefficientCover_isFinite hB
  have hgsurj : Surjective (Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (t i)))) :=
    MinimalPrimeNormalizationArrow.coefficientCover_surjective hB
  obtain ⟨V, hV⟩ := exists_normal_array_affine_stage_H1_zero_of_lower_rank
    (ι := minimalPrimes B)
    d ih A B R S (fun i => (hR i).2.2.1) (fun i => (hS i).2.2.2.1)
    (fun i => (hS i).2.2.2.2.trans hd)
    r (fun i => RingHom.MinimalPrimeNormalization.componentMap_injective f i)
    s t (fun i => RingHom.MinimalPrimeNormalization.sourceMap_finite f hA i)
    p σ hσ haff f
    hsquare a b H hgfinite hgsurj
    n hn hunit I c R₀ Ω e hpoint
  let v : Spec (CommRingCat.of V.algebra) ⟶ Spec (CommRingCat.of R₀) :=
    (etaleObject R₀ Ω V).hom
  let : Etale v := (etaleObject R₀ Ω V).prop
  let U : X.Etale := Scheme.Etale.mk (v ≫ e)
  let xU : Spec (CommRingCat.of Ω) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom V.point.toRingHom)
  refine ⟨U, xU, ?_, hV⟩
  change Spec.map (CommRingCat.ofHom V.point.toRingHom) ≫ (v ≫ e) = _
  exact (Category.assoc (Spec.map (CommRingCat.ofHom V.point.toRingHom)) v e).symm.trans
    ((congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R₀) => k ≫ e)
      (stagePoint_over R₀ Ω V)).trans hxe)

/-- The full uniform rank property, closed by natural-number strong induction.
The original coefficient ring may be nonreduced and the original arrow may
have a kernel. Every local-zero input of the construction is discharged. -/
theorem pointedCurveModuleInjectiveH1Effacement (d : ℕ) :
    PointedCurveModuleInjectiveH1Effacement.{u} d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro R S hR hS hNagR hNagS hd G Y p hp hgc hqc hqs σ hσ haff β a b H
      n hn hunit I hI c Ω hΩ hSep x
    let f : R →+* S := (Spec.preimage β).hom
    have hf : Spec.map (CommRingCat.ofHom f) = β := Spec.map_preimage β
    have Hf : IsPullback a b p (Spec.map (CommRingCat.ofHom f)) := hf.symm ▸ H
    exact exists_nagata_arrow_pointed_H1_zero_of_lower_rank d ih R S f
      hNagR hNagS hd p σ hσ haff a b Hf n hn hunit I c Ω x

end AlgebraicGeometry.Scheme.EtaleCohomology
