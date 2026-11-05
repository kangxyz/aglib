/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.WholeNormalPrincipalStep
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericH1NormalWholeOpenEffacement
public import Aglib.AlgebraicGeometry.Spec.SeparableNormalModelInduction

/-! # Selected-field normal-domain effacement from smaller coefficient rank

The generic producer is invoked on the original bounded class, without a
zero premise. Its actual two fields, literal finite normal models, whole
marked cover and coefficient-open zero feed the support-induction step.
Only after these models have been produced is one genuine coefficient and
its original detector chosen. The same coefficient is used on every later
chart. The induction hypothesis remains the full Nagata-ring property, so
the nonnormal principal quotient belongs to its actual scope.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Finite
  _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
  TwoFieldEffacement

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The actual selected generic normal models supply the pointed original-class
zero using only the full smaller-rank induction property. All ambient fields
remain variable so their original algebra structures specialize only once. -/
theorem exists_normal_domain_affine_stage_H1_zero_of_generic_whole_open
    (d : ℕ) (ih : ∀ q < d, PointedCurveModuleInjectiveH1Effacement.{u} q)
    (A B k K R₀ Ω : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field k] [Field K] [CommRing R₀] [Field Ω] [Algebra R₀ Ω] [IsSepClosed Ω]
    [Algebra A B] [Algebra A k] [IsFractionRing A k]
    [Algebra A K] [Algebra B K] [IsFractionRing B K] [Algebra k K]
    [IsScalarTower A B K] [IsScalarTower A k K]
    (hA : IsNagataRing.{u, 0} A) (hB : IsNagataRing.{u, 0} B)
    (hd : ringKrullDim B ≤ (d : ℕ))
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 p]
    [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F]
      (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of A)),
      IsAffine (pullback p z : Scheme.{u}))
    (e : Spec (CommRingCat.of R₀) ⟶ X)
    (hpoint : (Spec.algebraMap R₀ Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf (Spec (CommRingCat.of B)) (ULift.{u + 1} (ZMod n))) [Injective I]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap A B)))]
    (c : Sheaf.H.{eY} ((inverseImage (pullback.snd p (Spec.algebraMap A B))).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
        (ULift.{u + 1} (ZMod n)))).obj I)) 1)
    (L F E : Type u) [Field L] [Field F] [Field E]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra k L] [IsScalarTower k K L]
    [Algebra k F] [Module.Finite k F]
    [Algebra L E] [Module.Finite L E] [Algebra k E] [IsScalarTower k L E]
    (a : F →ₐ[k] E)
    (Z : FiniteEtale (pullback (pullback.snd p (Spec.algebraMap A k))
      (Spec.algebraMap k (separableClosure k F))))
    (z : Fiber (separableSourcePoint k F (pullback.snd p (Spec.algebraMap A k))
      (normalModelSection p σ hσ (Spec.algebraMap A k))
      (normalModelSection_over p σ hσ (Spec.algebraMap A k))) Z)
    (Hnormal :
      letI : IsNoetherianRing A := hA.isNoetherianRing
      letI : IsNoetherianRing B := hB.isNoetherianRing
      GenericH1NormalWholeOpenStageResult A B k K p σ hσ L F E a Z z
        ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
          (ULift.{u + 1} (ZMod n)))).obj I) c) :
    ∃ V : GeometricEtaleNeighborhood R₀ Ω,
      cohomologyPullback.{u, eY, u + 2}
        (pullback.snd (Spec.algebraMap R₀ V.algebra ≫ e)
          (pullback.fst p (Spec.algebraMap A B))) _ 1 c = 0 := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  let : IsNoetherianRing B := hB.isNoetherianRing
  let M := (SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
    (ULift.{u + 1} (ZMod n)))).obj I
  let F₀ := separableClosure k F
  let E₀ := separableClosure L E
  let : Algebra L E₀ := (separableClosure L E).toSubalgebra.algebra
  let : SMul L E₀ := Algebra.toSMul
  let : Algebra K E₀ := ((algebraMap L E₀).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L E₀ := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k K E₀ := IsScalarTower.of_algebraMap_eq fun x =>
    (IsScalarTower.algebraMap_apply k L E₀ x).trans
      (congrArg (algebraMap L E₀) (IsScalarTower.algebraMap_apply k K L x))
  let : Algebra A F₀ := ((algebraMap k F₀).comp (algebraMap A k)).toAlgebra
  let : IsScalarTower A k F₀ := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A E₀ := ((algebraMap k E₀).comp (algebraMap A k)).toAlgebra
  let : IsScalarTower A k E₀ := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra B E₀ := ((algebraMap K E₀).comp (algebraMap B K)).toAlgebra
  let : IsScalarTower B K E₀ := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B E₀ := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap k E₀ (algebraMap A k x) =
      algebraMap K E₀ (algebraMap B K (algebraMap A B x))
    rw [IsScalarTower.algebraMap_apply k K E₀,
      ← IsScalarTower.algebraMap_apply A k K, IsScalarTower.algebraMap_apply A B K]
  let : Module.Finite K E₀ := Module.Finite.trans L E₀
  let : Algebra.IsSeparable K E₀ := Algebra.IsSeparable.trans K L E₀
  let a₀ := separableSourceMap k F L E a
  change LiteralNormalWholeCoefficientOpen A B k K F₀ E₀ a₀ p σ hσ Z z
    ((inverseImage (pullback.snd p (Spec.algebraMap A B))).obj M) 1 c at Hnormal
  let R := integralClosure A F₀
  let S := integralClosure B E₀
  obtain ⟨_hfinR, hnoethR, hnormR, hfracR, hR, _hrankR, hspecR, _hsurjR⟩ :=
    SeparableBaseSquare.normal_finite_model_induction A k F₀ hA
  obtain ⟨_hfinS, hnoethS, hnormS, hfracS, hS, hrankS, hspecS, hsurjS⟩ :=
    SeparableBaseSquare.normal_finite_model_induction B K E₀ hB
  let : IsNoetherianRing R := hnoethR
  let : IsIntegrallyClosed R := hnormR
  let : IsFractionRing R F₀ := hfracR
  let : IsNoetherianRing S := hnoethS
  let : IsIntegrallyClosed S := hnormS
  let : IsFractionRing S E₀ := hfracS
  let : IsFinite (Spec.algebraMap A R) := hspecR
  let : IsFinite (Spec.algebraMap B S) := hspecS
  let : Surjective (Spec.algebraMap B S) := hsurjS
  let φ := SeparableBaseSquare.closureMap A B k F₀ E₀ a₀
  let : Algebra R S := φ.toRingHom.toAlgebra
  let : Algebra R E₀ := (a₀.toRingHom.comp (algebraMap R F₀)).toAlgebra
  let : IsScalarTower R S E₀ := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨_hfR, _hfR', _hfS, _hnS, _hiS, _hfS',
    G, _hGI, _hcardG, ρ, hρ, _rG, _wG, _hwG, _hwzG, t, ht, _hne, hopen⟩ := Hnormal
  obtain ⟨J, hJ, α, hdetect⟩ :=
    exists_moduleInjective_finite_refinement_detector.{u, u + 2, u + 2}
      (Spec.algebraMap B S) (ULift.{u + 1} (ZMod n)) I
  let : Injective J := hJ
  have hρ' : ρ ≫ G.obj.hom = pullback.sectionMap p (Spec.algebraMap A R) σ hσ := hρ
  have hunitR : IsUnit (n : R) := by
    simpa only [map_natCast] using hunit.map (algebraMap A R)
  exact exists_affine_stage_zero_of_whole_normal_open_lower_rank
    d ih R₀ Ω A B R S hR hS (hrankS.trans hd) p σ hσ haff
    (Spec.algebraMap A R) (Spec.algebraMap A B) (Spec.algebraMap B S)
    (Spec.map (CommRingCat.ofHom φ.toRingHom))
    (SeparableBaseSquare.spec_square A B k F₀ E₀ a₀) e hpoint
    G.obj.hom ρ hρ' n hn hunitR I J α
    (fun l b₀ b₁ H q d₀ hd₀ => hdetect l b₀ b₁ H q d₀ hd₀)
    c t ht hopen

end AlgebraicGeometry.Scheme.EtaleCohomology
