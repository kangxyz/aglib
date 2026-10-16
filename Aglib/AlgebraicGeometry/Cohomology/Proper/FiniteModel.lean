/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Perfect
public import Mathlib.Data.Fintype.EquivFin

/-!
# The same finite-projective model for proper coherent relatively flat coefficients

Actual proper finiteness discharges the cohomological finiteness input of
the sole finite-affine-cover model. A finite subcover of the original affine
cover, with one additional empty open, works also for the empty scheme and
the zero base ring. No projective embedding or comparison family is input.

The same actual bounded finite-projective module complex computes installed
derived direct image after native tilde, both over the original ring and
after every ring map. The coefficient on the actual fibre product is its
ordinary pullback. No Noetherianity or flatness of the new ring is assumed.
The object comparisons retain the exact-tilde derived-unit transport;
identifying a separately chosen chain-normalized comparison is a further
normalization statement.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Actual proper finiteness and relative flatness construct the sole original
finite-projective Cech model for any supplied finite affine cover. -/
theorem nonempty_finiteCechCohomologyModel_of_proper
    (R : CommRingCat.{u}) [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤) :
    Nonempty (FiniteCechCohomologyModel R ι X f U M n) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  exact nonempty_finiteCechCohomologyModel_of_finite_cohomology
    R ι X f U M n e hU hcover hflat
    (moduleCohomology_finite_of_proper R f M hM)

/-- A proper coherent relatively flat coefficient over a Noetherian ring internally supplies
an actual finite affine cover and the same native finite-projective model. The empty source
and the zero base ring require no separate premise. -/
theorem exists_finiteCechCohomologyModel_of_proper
    (R : CommRingCat.{u}) [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) :
    ∃ (n : ℕ) (U : ULift.{u} (Fin (n + 1)) → X.Opens),
      (∀ j, IsAffineOpen (U j)) ∧ iSup U = ⊤ ∧
        Nonempty (FiniteCechCohomologyModel R (ULift.{u} (Fin (n + 1))) X f U M n) := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineCover.finiteSubcover
  let n := Fintype.card C.I₀
  let V : Option C.I₀ → X.Opens := fun j => j.elim ⊥ (fun k => (C.f k).opensRange)
  let E : Option C.I₀ ≃ ULift.{u} (Fin (n + 1)) :=
    (Fintype.equivFinOfCardEq (by simp [n])).trans Equiv.ulift.symm
  let U : ULift.{u} (Fin (n + 1)) → X.Opens := V ∘ E.symm
  have hU : ∀ j, IsAffineOpen (U j) := by
    intro j
    dsimp only [U, Function.comp_def, V]
    cases E.symm j with
    | none => exact isAffineOpen_bot X
    | some k => exact isAffineOpen_opensRange (C.f k)
  have hcover : iSup U = ⊤ := by
    apply le_antisymm le_top
    calc
      ⊤ = ⨆ j, (C.f j).opensRange := C.iSup_opensRange.symm
      _ ≤ iSup U := iSup_le fun j => le_iSup_of_le (E (some j)) (by simp [U, V])
  exact ⟨n, U, hU, hcover,
    nonempty_finiteCechCohomologyModel_of_proper R f M hM hflat U n
      Equiv.ulift hU hcover⟩

local instance properModelDerivedSheaves (Z : Scheme.{u}) : HasDerivedCategory.{u + 1} Z.Modules :=
  HasDerivedCategory.standard _

local instance properModelDerivedModules (R : CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

/-- One actual bounded finite-projective module complex gives a native strict-perfect
representative of the installed proper direct image and, by literal scalar extension of
that same complex, of every ordinary pulled-coefficient direct image. -/
theorem exists_finiteProjective_derivedPushforward_model_of_proper
    (R : CommRingCat.{u}) [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) :
    ∃ (n : ℕ) (P : CochainComplex.Plus (ModuleCat.{u} R)),
      P.obj.IsStrictlyGE 0 ∧ P.obj.IsStrictlyLE (n : ℤ) ∧
        (∀ j, Module.Finite R (P.obj.X j)) ∧
        (∀ j, Module.Projective R (P.obj.X j)) ∧
        Scheme.Modules.Complex.strictPerfect (Spec R)
          ((tilde.functor R).mapCochainComplexPlus.obj P).obj ∧
        Nonempty (DerivedCategory.Plus.Q.obj ((tilde.functor R).mapCochainComplexPlus.obj P) ≅
          (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ∧
        ∀ (S : CommRingCat.{u}) (σ : R →+* S),
          let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
          let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
          let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
          let Q := (tilde.functor S).mapCochainComplexPlus.obj
            ((ModuleCat.extendScalars σ).mapCochainComplexPlus.obj P)
          Q.obj.IsStrictlyGE 0 ∧ Q.obj.IsStrictlyLE (n : ℤ) ∧
            Scheme.Modules.Complex.strictPerfect (Spec S) Q.obj ∧
            Nonempty (DerivedCategory.Plus.Q.obj Q ≅
              (Scheme.Modules.pushforward r).rightDerivedFunctorPlus.obj
                ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
                  ((Scheme.Modules.pullback p).obj M))) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper R f M hM hflat
  refine ⟨n, D.toPlus, D.lowerBound, D.upperBound, D.finite_X, D.projective_X,
    D.sheafModelPlus_strictPerfect,
    ⟨D.derivedPushforwardObjectIso hU hcover Equiv.ulift (injectiveResolution M)⟩, ?_⟩
  intro S σ
  exact ⟨D.baseChangeSheafModelPlus_lowerBound σ, D.baseChangeSheafModelPlus_upperBound σ,
    D.baseChangeSheafModelPlus_strictPerfect σ,
    ⟨D.baseChangeDerivedPushforwardObjectIso σ hU hcover Equiv.ulift hflat
      (injectiveResolution
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M))⟩⟩

end AlgebraicGeometry.Scheme.Cohomology
