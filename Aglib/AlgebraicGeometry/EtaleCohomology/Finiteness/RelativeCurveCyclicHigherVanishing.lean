/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.RelativeCurveHigherVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.EtaleCyclicTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Etale
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SurjectivePullback

/-! # Cyclic higher vanishing on proper relative curves over an integral base

One original finite étale splitting cover transports the proved roots
vanishing to the literal cyclic constant coefficient. Both comparisons use
existing étale exchange on the same pullback. No global roots coordinate,
additional geometric-fibre model, or smoothness assumption is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Above degree two the literal finite cyclic constant has zero higher image.
The integral-base premise is used only to construct the actual roots-splitting
cover; the relative curve need not be smooth or geometrically integral. -/
theorem cyclicHigherDirectImage_isZero_of_relativeCurve
    {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(S, ⊤)))
    (q : ℕ) (hq : 2 < q) :
    IsZero ((higherDirectImage f q).obj
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X)) := by
  classical
  obtain ⟨T, hTsurj, ⟨eT₀⟩⟩ :=
    GroupCohomology.Kummer.exists_finiteEtale_cyclic_trivialization S n hn hinv
  let b := T.obj.hom
  let : Surjective b := hTsurj
  let Y := pullback b f
  let p : Y ⟶ T.obj.left := pullback.fst b f
  let a : Y ⟶ X := pullback.snd b f
  let value := ConstantFinite.value (ULift.{u} (ZMod n))
  let F := ConstantFinite.coefficient (ULift.{u} (ZMod n)) X
  have hT := levelInvertible b n hinv
  have hX := levelInvertible f n hinv
  let eT : mu T.obj.left n ≅
      ConstantFinite.coefficient (ULift.{u} (ZMod n)) T.obj.left :=
    (rootsPullbackIso b n hn hinv).symm ≪≫ eT₀
  let eY : mu Y n ≅ ConstantFinite.coefficient (ULift.{u} (ZMod n)) Y :=
    (rootsPullbackIso p n hn hT).symm ≪≫ (inverseImage p).mapIso eT ≪≫
      (inverseImageConstantIso p).app value
  let : IsIso (higherBaseChangeMap f p b a pullback.condition q) :=
    higherBaseChangeMap_etale_isIso f b q
  let Eμ : (inverseImage b).obj ((higherDirectImage f q).obj (mu X n)) ≅
      (higherDirectImage p q).obj (mu Y n) :=
    asIso ((higherBaseChangeMap f p b a pullback.condition q).app (mu X n)) ≪≫
      (higherDirectImage p q).mapIso (rootsPullbackIso a n hn hX)
  have hμ := rootsHigherDirectImage_isZero_of_relativeCurve f hdim n hn hinv q hq
  have hμY : IsZero ((higherDirectImage p q).obj (mu Y n)) :=
    ((inverseImage b).map_isZero hμ).of_iso Eμ.symm
  let EF : (inverseImage b).obj ((higherDirectImage f q).obj F) ≅
      (higherDirectImage p q).obj (mu Y n) :=
    asIso ((higherBaseChangeMap f p b a pullback.condition q).app F) ≪≫
      (higherDirectImage p q).mapIso
        ((inverseImageConstantIso a).app value ≪≫ eY.symm)
  have hz : IsZero ((inverseImage b).obj ((higherDirectImage f q).obj F)) :=
    hμY.of_iso EF
  let : (inverseImage b).Faithful := Proper.Reduction.inverseImage_faithful_of_surjective b
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (inverseImage b).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp hz

end AlgebraicGeometry.Scheme.EtaleCohomology
