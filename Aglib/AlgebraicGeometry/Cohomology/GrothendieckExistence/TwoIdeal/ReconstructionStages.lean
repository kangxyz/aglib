/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.OriginalStageMap
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.OriginalStageTransitions
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.IndependentQuotientDefects
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientCompletionCoefficient

/-! # Original finite stages of a concrete bounded reconstruction triple

The input is an actual coherent coefficient G and its specified K-completion
comparison. No effectivity or uniqueness oracle is introduced. These comparisons
and original target squares are the inputs to bounded-candidate uniqueness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology
private theorem recovery_map_aux {T : Type*} [Category T]
    {P Q R S U V : T} (i : P ⟶ Q) (b : Q ⟶ R) (e : R ⟶ S)
    (a : S ⟶ U) (q : R ⟶ V) (r : Q ⟶ V) (g : P ⟶ U) (j : U ≅ V)
    (h₁ : e ≫ a = q ≫ j.inv) (h₂ : b ≫ q = r)
    (h₃ : g ≫ j.hom = i ≫ r) : (i ≫ b ≫ e) ≫ a = g := by
  calc
    (i ≫ b ≫ e) ≫ a = i ≫ b ≫ (e ≫ a) := by simp only [Category.assoc]
    _ = i ≫ b ≫ (q ≫ j.inv) := by rw [h₁]
    _ = (i ≫ (b ≫ q)) ≫ j.inv := by simp only [Category.assoc]
    _ = (i ≫ r) ≫ j.inv := by rw [h₂]
    _ = (g ≫ j.hom) ≫ j.inv := by rw [h₃]
    _ = g := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (K : X.IdealSheafData)
  (h : ClosedThickeningCompletionEssSurj f I K)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))
  {G H : X.CoherentSheaf}
local notation "J" => idealThickeningIdealSheaf f I
local notation "C" => completionFunctor X K
local notation "D" => twoIdealCoefficientSystem I f K h F

/-- Completing the actual I-power quotient of a concrete reconstructed sheaf
recovers the K-completion of the original I-formal stage. -/
def twoIdealReconstructionStageIso (β : (C).obj G ≅ D) (n : ℕ) :
    (C).obj (idealSheafCoherentQuotient X (J ^ n) G) ≅
      (C).obj (originalStageCoherent I f F n) :=
  idealSheafQuotientCompletionIso X K (J ^ n) G ≪≫
    (AdicSystem.quotientFunctor X K (J ^ n)).mapIso β ≪≫
    twoIdealOriginalStageIso I f K h F n

/-- The actual reconstructed-stage comparison retains its original target map. -/
theorem twoIdealReconstructionStageIso_map
    (φ : F ⟶ (completionFunctor X J).obj H) (a : G ⟶ H)
    (β : (C).obj G ≅ D)
    (hβ : β.hom ≫ twoIdealCoefficientMap I f K h F φ = (C).map a) (n : ℕ) :
    (twoIdealReconstructionStageIso I f K h F β n).hom ≫
        (C).map (originalStageCoherentMap I f F φ n) =
      (C).map (idealSheafCoherentQuotientHom X (J ^ n) a) := by
  apply recovery_map_aux
    (idealSheafQuotientCompletionIso X K (J ^ n) G).hom
    ((AdicSystem.quotientFunctor X K (J ^ n)).map β.hom)
    (twoIdealOriginalStageIso I f K h F n).hom
    ((C).map (originalStageCoherentMap I f F φ n))
    ((AdicSystem.quotientFunctor X K (J ^ n)).map
      (twoIdealCoefficientMap I f K h F φ))
    ((AdicSystem.quotientFunctor X K (J ^ n)).map ((C).map a))
    ((C).map (idealSheafCoherentQuotientHom X (J ^ n) a))
    (idealSheafQuotientCompletionIso X K (J ^ n) H)
  · exact (twoIdealOriginalStageIso_map I f K h F φ n).symm
  · exact ((AdicSystem.quotientFunctor X K (J ^ n)).map_comp _ _).symm.trans
      (congrArg (fun z => (AdicSystem.quotientFunctor X K (J ^ n)).map z) hβ)
  · exact idealSheafQuotientCompletionIso_coefficient_naturality X K (J ^ n) a

/-- The actual comparisons retain the original I-transition before uniqueness. -/
theorem twoIdealReconstructionStageIso_transition (β : (C).obj G ≅ D) (n : ℕ) :
    (C).map (idealSheafCoherentQuotientMap X (J ^ (n + 1))
        (idealSheaf_pow_le X J (Nat.le_succ n)) G) ≫
      (twoIdealReconstructionStageIso I f K h F β n).hom =
    (twoIdealReconstructionStageIso I f K h F β (n + 1)).hom ≫
      (C).map (originalStageCoherentTransition I f F n) := by
  let q := idealSheaf_pow_le X J (Nat.le_succ n)
  have h₁ : CommSq
      ((C).map (idealSheafCoherentQuotientMap X (J ^ (n + 1)) q G))
      (idealSheafQuotientCompletionIso X K (J ^ (n + 1)) G).hom
      (idealSheafQuotientCompletionIso X K (J ^ n) G).hom
      (AdicSystem.quotientMap X K (J ^ (n + 1)) q ((C).obj G)) :=
    ⟨idealSheafQuotientCompletionIso_ideal_naturality X K (J ^ (n + 1)) q G⟩
  have h₂ : CommSq
      (AdicSystem.quotientMap X K (J ^ (n + 1)) q ((C).obj G))
      ((AdicSystem.quotientFunctor X K (J ^ (n + 1))).map β.hom)
      ((AdicSystem.quotientFunctor X K (J ^ n)).map β.hom)
      (AdicSystem.quotientMap X K (J ^ (n + 1)) q D) :=
    ⟨(AdicSystem.quotientMap_naturality X K (J ^ (n + 1)) q β.hom).symm⟩
  have h₃ : CommSq (AdicSystem.quotientMap X K (J ^ (n + 1)) q D)
      (twoIdealOriginalStageIso I f K h F (n + 1)).hom
      (twoIdealOriginalStageIso I f K h F n).hom
      ((C).map (originalStageCoherentTransition I f F n)) :=
    ⟨twoIdealOriginalStageIso_transition I f K h F n⟩
  exact (h₁.vert_comp (h₂.vert_comp h₃)).w

omit [IsNoetherianRing A] [IsAdicComplete I A] [IsProper f] in
/-- Ordinary defects of each actual reconstructed I-quotient are bounded
uniformly by K. This bound is used for bounded-candidate uniqueness. -/
theorem twoIdealReconstructionStageMap_bounds (a : G ⟶ H) (t n : ℕ)
    (hk : killedByIdealSheaf (K ^ t) (kernel a.hom))
    (hc : killedByIdealSheaf (K ^ t) (cokernel a.hom)) :
    killedByIdealSheaf (K ^ (t * 2))
        (kernel (idealSheafCoherentQuotientHom X (J ^ n) a).hom) ∧
      killedByIdealSheaf (K ^ (t * 2))
        (cokernel (idealSheafCoherentQuotientHom X (J ^ n) a).hom) := by
  let : G.obj.IsQuasicoherent := QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (G.property R j).1)
  let : H.obj.IsQuasicoherent := QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (H.property R j).1)
  exact independentQuotient_defectsKilled a.hom K (J ^ n) t hk hc

end AlgebraicGeometry.Scheme.Cohomology
