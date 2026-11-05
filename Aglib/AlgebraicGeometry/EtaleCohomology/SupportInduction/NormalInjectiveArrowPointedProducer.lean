/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.NormalDomainPointedProducer
public import Aglib.RingTheory.Localization.FractionRing.InjectiveMapTowers

/-! # Pointed effacement for the original injective normal-domain arrow

The original ring map determines both fraction-field maps and their scalar
laws. The normal-domain construction is applied to those canonical choices;
no compatible fraction-field realization is an additional hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The complete normal-domain pointed producer for a given injective arrow,
using its original fraction fields and retaining the original class and mark. -/
theorem exists_normal_injective_arrow_pointed_H1_zero_of_lower_rank
    (d : ℕ) (ih : ∀ q < d, PointedCurveModuleInjectiveH1Effacement.{u} q)
    (A B : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    (f : A →+* B) (hf : Function.Injective f)
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
  let : Algebra A B := f.toAlgebra
  let : Algebra A (FractionRing B) :=
    ((algebraMap B (FractionRing B)).comp f).toAlgebra
  let : Algebra (FractionRing A) (FractionRing B) :=
    (integralClosure.fractionMapOfInjective f hf).toAlgebra
  let : SMul A B := Algebra.toSMul
  let : SMul A (FractionRing A) := Algebra.toSMul
  let : SMul B (FractionRing B) := Algebra.toSMul
  let : SMul A (FractionRing B) := Algebra.toSMul
  let : SMul (FractionRing A) (FractionRing B) := Algebra.toSMul
  have ht := integralClosure.fractionMapOfInjective_towers f hf
  let : IsScalarTower A B (FractionRing B) := ht.1
  let : IsScalarTower A (FractionRing A) (FractionRing B) := ht.2
  exact exists_normal_domain_pointed_H1_zero_of_lower_rank
    d ih A B (FractionRing A) (FractionRing B) hA hB hd
    p σ hσ haff a b H n hn hunit I c Ω x

end AlgebraicGeometry.Scheme.EtaleCohomology
