/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticPrincipalOpenDegreeStep
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.UniformCoefficientRefinementReturn
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.FinitePrincipalClosedResidual
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ArithmeticPrincipalLowerVanishing

/-! # Fixed-degree arithmetic support induction after finite coefficient change

A single genuine injective on the actual finite coefficient model is chosen
before refinement. Its original transformed class inherits the produced
principal-open zero. The smaller-rank branch supplies a target chart; the
same finite retract returns zero of the original class on that chart.
The source curve, whole section, marked field, and target axis are unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Consume the actual finite-model principal zero and smaller-rank induction.
Only strictly lower positive degrees are required on the refined open part. -/
theorem exists_arithmetic_finite_coefficient_degree_refinement_of_lower_rank
    (q : ℕ) (hq : 0 < q)
    (houter : ∀ r : ℕ, 1 ≤ r → r < q → ArithmeticCurveModuleInjectiveVanishing.{u} r)
    (d : ℕ)
    (ih : ∀ r < d, ArithmeticPointedCurveModuleEffacement.{u} q r)
    (R S L : Type u) [CommRing R] [CommRing S] [CommRing L] [IsDomain L]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ L]
    [Algebra S L] [Module.Finite S L] [Surjective (Spec.algebraMap S L)]
    (hd : ringKrullDim S ≤ (d : ℕ))
    {G Y : Scheme.{u}} (p : G ⟶ Spec (.of R))
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (.of R) ⟶ G) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (K : Type u) [Field K] (z : Spec (.of K) ⟶ Spec (.of R)),
      IsAffine (pullback p z : Scheme.{u}))
    (β : Spec (.of S) ⟶ Spec (.of R))
    (a : Y ⟶ G) (b : Y ⟶ Spec (.of S)) (H : IsPullback a b p β)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (.of S)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of S))
        (ULift.{u + 1} (ZMod n)))).obj I)) q)
    (s : L) (hs : s ≠ 0)
    (hopen : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd (principalSupportOpen L s).ι (pullback.snd b (Spec.algebraMap S L)) ≫
        pullback.fst b (Spec.algebraMap S L)) _ q c = 0)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of R)) :
    ∃ (U : G.Etale) (xU : Spec (.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ≫ σ ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ q c = 0 := by
  let g := Spec.algebraMap S L
  let v := pullback.fst b g
  let bL := pullback.snd b g
  let aL := v ≫ a
  have Hbase : IsPullback v bL b g := IsPullback.of_hasPullback b g
  have HL : IsPullback aL bL p (g ≫ β) := Hbase.paste_horiz H
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let : SmoothOfRelativeDimension 1 bL :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{u} 1) HL
      (inferInstance : SmoothOfRelativeDimension 1 p)
  have hunitL : IsUnit (n : L) := by
    simpa only [map_natCast] using hunit.map (Spec.preimage (g ≫ β)).hom
  have hdL : ringKrullDim L ≤ (d : ℕ) :=
    (RingHom.IsIntegral.ringKrullDim_le
      (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral S L))).trans hd
  let : IsFinite g := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite S L))
  obtain ⟨J, hJ, α, hreturn⟩ :=
    Finite.exists_uniform_finite_coefficient_refinement_return
      g (ULift.{u + 1} (ZMod n)) I
  let : Injective J := hJ
  let cL := moduleFiniteImageClass g v b bL Hbase.w
    (ULift.{u + 1} (ZMod n)) I J α q c
  have hopenL : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd (principalSupportOpen L s).ι bL) _ q cL = 0 :=
    coefficient_restriction_zero_of_composite_zero v
      (pullback.snd (principalSupportOpen L s).ι bL) _ _
      (moduleClosedPullbackCoefficientMap g v b bL Hbase.w
        (ULift.{u + 1} (ZMod n)) I J α) q c hopen
  obtain ⟨U, z, hz, hc⟩ := exists_arithmetic_principalOpen_degree_refinement_of_lower_rank
    q hq d ih R L hdL p σ hσ haff (g ≫ β) aL bL HL n hn hunit J cL s hs
    hopenL (fun U => arithmetic_principal_refinement_lower_higherImage_isZero
      q houter L s bL aL n hn hunitL J U) Ω x
  let t := pullback.snd U.hom a
  let t' := pullback.fst v t
  let v₂ := pullback.snd v t
  have hcL : cohomologyPullback.{u, u + 2, u + 2} t' _ q cL = 0 := by
    let E := ((IsPullback.of_hasPullback U.hom a).flip).familyPullbackIso v
    exact TwoFieldEffacement.original_class_zero_of_map_law E.hom
      (pullback.snd U.hom aL) t'
      (((IsPullback.of_hasPullback U.hom a).flip).familyPullbackIso_hom_snd v)
      _ q cL hc
  exact ⟨U, z, hz, hreturn v b bL Hbase.flip t t' v₂
    (IsPullback.of_hasPullback v t) q c hcL⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
