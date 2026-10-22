/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.StageAlgebraization
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.OriginalStageDiagrams
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedCandidateHomExt

/-! # Recovery of the entire original formal system from a concrete bounded triple

Actual bounded-candidate uniqueness retains both the target and the specified
formal comparison, forcing all original transitions. The conclusion is genuine
I-effectivity from an actually supplied bounded K-reconstruction, not a final
proper-existence theorem with an unproved realization assumption hidden inside.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology
private theorem recovery_completed_square {T U : Type*} [Category T] [Category U]
    (C : T ⥤ U) {A B D E : T} (f : A ⟶ B) (g : D ⟶ E)
    (e : A ⟶ D) (e' : B ⟶ E) (d : C.obj A ⟶ C.obj D) (d' : C.obj B ⟶ C.obj E)
    (he : C.map e = d) (he' : C.map e' = d')
    (h : C.map f ≫ d' = d ≫ C.map g) : C.map (f ≫ e') = C.map (e ≫ g) := by
  rw [Functor.map_comp, Functor.map_comp, he, he']
  exact h

private theorem recovery_target_square {T : Type*} [Category T]
    {A B D E P Q : T} (f : A ⟶ B) (g : D ⟶ E) (e : A ⟶ D) (e' : B ⟶ E)
    (a : D ⟶ P) (a' : E ⟶ Q) (b : A ⟶ P) (b' : B ⟶ Q) (k : P ⟶ Q)
    (he : e ≫ a = b) (he' : e' ≫ a' = b')
    (hb : f ≫ b' = b ≫ k) (ha : g ≫ a' = a ≫ k) :
    (f ≫ e') ≫ a' = (e ≫ g) ≫ a' := by
  calc
    (f ≫ e') ≫ a' = f ≫ b' := by rw [Category.assoc, he']
    _ = b ≫ k := hb
    _ = (e ≫ a) ≫ k := by rw [he]
    _ = (e ≫ g) ≫ a' := by simp only [Category.assoc, ha]

private theorem recovery_unit_square {T : Type*} [Category T] (Q : T ⥤ T)
    (η : 𝟭 T ⟶ Q) {A B : T} (f g : A ⟶ B) (h : Q.map f = Q.map g) :
    f ≫ η.app B ≫ 𝟙 (Q.obj B) = g ≫ η.app B ≫ 𝟙 (Q.obj B) := by
  simpa only [Functor.id_map, Category.comp_id] using
    (η.naturality f).trans ((congrArg (fun z => η.app A ≫ z) h).trans
      (η.naturality g).symm)

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (K : X.IdealSheafData)
  (h : ClosedThickeningCompletionEssSurj f I K)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) {G H : X.CoherentSheaf}
local notation "J" => idealThickeningIdealSheaf f I
local notation "C" => completionFunctor X K
variable (φ : F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj H) (t : ℕ)
  (hφ : AdicSystem.DefectsKilled K t φ) (a : G ⟶ H)
  (β : (completionFunctor X K).obj G ≅ twoIdealCoefficientSystem I f K h F)
  (hβ : β.hom ≫ twoIdealCoefficientMap I f K h F φ = (completionFunctor X K).map a)
  (s : ℕ) (hk : killedByIdealSheaf (K ^ s) (kernel a.hom))
  (hc : killedByIdealSheaf (K ^ s) (cokernel a.hom))
local notation "e" => twoIdealStageAlgebraizationIso I f K h F φ t hφ a β hβ s hk hc

/-- Bounded uniqueness forces naturality at every original I-index arrow. -/
theorem twoIdealStageAlgebraizationIso_naturality {m n : ℕᵒᵖ} (g : m ⟶ n) :
    (idealSheafCoherentQuotientTower X J G).map g ≫ (e n.unop).hom =
      (e m.unop).hom ≫ (originalStageCoherentDiagram I f F).map g := by
  let u := (idealSheafCoherentQuotientTower X J G).map g ≫ (e n.unop).hom
  let v := (e m.unop).hom ≫ (originalStageCoherentDiagram I f F).map g
  have he : (C).map u = (C).map v :=
    recovery_completed_square C
      ((idealSheafCoherentQuotientTower X J G).map g)
      ((originalStageCoherentDiagram I f F).map g) (e m.unop).hom (e n.unop).hom
      (twoIdealReconstructionStageIso I f K h F β m.unop).hom
      (twoIdealReconstructionStageIso I f K h F β n.unop).hom
      (twoIdealStageAlgebraizationIso_completion I f K h F φ t hφ a β hβ s hk hc m.unop)
      (twoIdealStageAlgebraizationIso_completion I f K h F φ t hφ a β hβ s hk hc n.unop)
      (twoIdealReconstructionStageIso_naturality I f K h F β g)
  apply boundedCandidate_hom_ext
    ((C).map (originalStageCoherentMap I f F φ n.unop))
    (originalStageCoherentMap I f F φ n.unop) (Iso.refl _) (by simp)
    t (hφ n.unop).1 (hφ n.unop).2 u v
  · exact recovery_target_square
      ((idealSheafCoherentQuotientTower X J G).map g)
      ((originalStageCoherentDiagram I f F).map g) (e m.unop).hom (e n.unop).hom
      (originalStageCoherentMap I f F φ m.unop) (originalStageCoherentMap I f F φ n.unop)
      (idealSheafCoherentQuotientHom X (J ^ m.unop) a)
      (idealSheafCoherentQuotientHom X (J ^ n.unop) a)
      ((idealSheafCoherentQuotientTower X J H).map g)
      (twoIdealStageAlgebraizationIso_map I f K h F φ t hφ a β hβ s hk hc m.unop)
      (twoIdealStageAlgebraizationIso_map I f K h F φ t hφ a β hβ s hk hc n.unop)
      ((coherentQuotientTowerHom J a).naturality g)
      ((originalStageCoherentDiagramMap I f F φ).naturality g)
  · intro l
    exact recovery_unit_square (idealSheafQuotientFunctor X (K ^ l))
      (idealSheafQuotientUnit X (K ^ l)) u.hom v.hom
      (congrArg (fun z => z.hom.app (op l)) he)

/-- The stage algebraizations form one isomorphism of original coherent diagrams. -/
def twoIdealRecoveryDiagramIso :
    idealSheafCoherentQuotientTower X J G ≅ originalStageCoherentDiagram I f F :=
  NatIso.ofComponents (fun n => e n.unop)
    (fun g => twoIdealStageAlgebraizationIso_naturality I f K h F φ t hφ a β hβ s hk hc g)

/-- The supplied actual bounded reconstruction algebraizes the original I-system. -/
def twoIdealRecoveryIso : (completionFunctor X J).obj G ≅ F :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerRight
    (twoIdealRecoveryDiagramIso I f K h F φ t hφ a β hβ s hk hc)
    (QuasiCoherent.finiteTypeSheavesToModules X))

end AlgebraicGeometry.Scheme.Cohomology
