/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Actual evaluation, base change, and arbitrary-base cohomology

Evaluation is the actual pullback/pushforward adjunction counit. Base change
is `Aglib.Scheme.Modules.moduleBaseChangeMap`, whose adjoint formula is proved below. Every
geometric fibre group is the actual cohomology of the pulled-back module.

LocalFreeCohomologyBaseChange retains the general derived corollary of Stacks
0B91 (36.30.4) and 0B9S (36.32.3): proper plus locally finite presentation gives
finite presentation; locally free M and flat f give relative flatness. The
perfect complex and geometric-fibre detection identify the degree-zero rank-r
locus with all of S. Its H0 is the actual pushforward, and its arbitrary-base
comparison is the constructed adjunction mate. These identifications and
geometric-fibre detection are disclosed parts of the retained corollary.

Both the base and every change of base are arbitrary schemes, including
non-Noetherian and nonreduced schemes. Neither a substitute pushforward nor a
chosen comparison is supplied. No cohomology profile specific to genus one
is assumed in the family. Sources and corrections inspected 2026-10-09.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.Relative` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

/-!
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
This module provides general scheme cohomology interfaces.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
/-- The counit from the pullback of the direct image of `M` to `M` along `f`. -/
def relativeEvaluation (M : X.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj M) ⟶ M :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M

@[reassoc] theorem relativeEvaluation_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pushforward f).map φ) ≫ relativeEvaluation
      f N =
      relativeEvaluation f M ≫ φ :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).counit.naturality φ

theorem relativeBaseChange_adjoint {T : Scheme.{u}} (g : T ⟶ S) (M : X.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f g)).homEquiv _ _).symm
      (AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap f g M) =
    (Scheme.Modules.pullbackComp (pullback.snd f g) g).hom.app _ ≫
      (Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := g)).symm).hom.app _ ≫
      (Scheme.Modules.pullbackComp (pullback.fst f g) f).inv.app _ ≫
      (Scheme.Modules.pullback (pullback.fst f g)).map (relativeEvaluation f M) :=
  Equiv.symm_apply_apply _ _

/-- Degree-`n` module cohomology of the pullback of `M` to the fibre over the field-valued point
`t`. -/
abbrev fibreCohomology (M : X.Modules) (K : Type u) [Field K]
    (t : Spec (.of K) ⟶ S) (n : ℕ) : Type (u + 1) :=
  moduleCohomology K (Over.mk (pullback.snd f t))
    ((Scheme.Modules.pullback (pullback.fst f t)).obj M) n

/-- Every algebraically closed field-valued fibre has degree-zero finrank `r` and subsingleton
positive cohomology. -/
def FibreCohomologyConcentrated (M : X.Modules) (r : ℕ) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
    Module.finrank K (fibreCohomology f M K t 0) = r ∧
      ∀ n : ℕ, 0 < n → Subsingleton (fibreCohomology f M K t n)

/-- The assertion that, for proper, flat, locally finitely presented `f` and locally free,
finitely presented `M`, geometric fibre concentration of rank `r` gives a rank-`r` direct
image and invertible canonical maps after every base change. -/
def LocalFreeCohomologyBaseChange : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S) (M : X.Modules) (r : ℕ),
    IsProper f → LocallyOfFinitePresentation f → Flat f →
    M.IsLocallyFree → M.IsFinitePresentation → FibreCohomologyConcentrated f M r →
    AlgebraicGeometry.Scheme.Modules.SheafHasRank ((Scheme.Modules.pushforward f).obj M) r ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso
        (AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap f g M)
end AlgebraicGeometry.Scheme.Cohomology

/-! Actual counit nonvanishing and its compatibility with the canonical
base-change mate. These constructions require no additional family. -/

namespace AlgebraicGeometry.Scheme.Cohomology
universe u
open Opposite
variable {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
theorem relativeEvaluation_ne_zero [Nontrivial Γ(M, ⊤)] : relativeEvaluation f M ≠ 0 := by
  intro h
  have ht := (Scheme.Modules.pullbackPushforwardAdjunction f).right_triangle_components M
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
    ((Scheme.Modules.pushforward f).obj M) ≫
      (Scheme.Modules.pushforward f).map (relativeEvaluation f M) = 𝟙 _ at ht
  rw [h, Functor.map_zero, comp_zero] at ht
  obtain ⟨m, hm⟩ := exists_ne (0 : Γ(M,⊤))
  apply hm
  exact (congrArg (fun k : (Scheme.Modules.pushforward f).obj M ⟶
    (Scheme.Modules.pushforward f).obj M ↦ k.app ⊤ m) ht).symm
end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
/-- The pullback-square identification of the two iterated pullbacks of the direct image of `M`. -/
def evaluationBaseChangeSourceIso :
    (Scheme.Modules.pullback (pullback.snd f t)).obj
      ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pushforward f).obj M)) ≅
    (Scheme.Modules.pullback (pullback.fst f t)).obj
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj M)) :=
  (Scheme.Modules.pullbackComp (pullback.snd f t) t).app _ ≪≫
    (Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := t)).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst f t) f).app _).symm

theorem evaluation_baseChange_square :
    (evaluationBaseChangeSourceIso f t M).hom ≫
      (Scheme.Modules.pullback (pullback.fst f t)).map (relativeEvaluation f M) =
    (Scheme.Modules.pullback (pullback.snd f t)).map
      (AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap f
      t M) ≫
      relativeEvaluation (pullback.snd f t) ((Scheme.Modules.pullback (pullback.fst f t)).obj M)
        := by
  exact (relativeBaseChange_adjoint f t M).symm.trans
    ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f t)).homEquiv_counit _ _ _)

theorem evaluation_pullback_ne_zero [IsIso (AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap
  f t M)]
    [Nontrivial Γ((Scheme.Modules.pullback (pullback.fst f t)).obj M, ⊤)] :
    (Scheme.Modules.pullback (pullback.fst f t)).map (relativeEvaluation f M) ≠ 0 := by
  intro h
  have he := evaluation_baseChange_square f t M
  rw [h, comp_zero] at he
  apply relativeEvaluation_ne_zero (pullback.snd f t) ((Scheme.Modules.pullback (pullback.fst f
    t)).obj M)
  apply (cancel_epi ((Scheme.Modules.pullback (pullback.snd f t)).map
    (AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap f t M))).mp
  simpa using he.symm
end AlgebraicGeometry.Scheme.Cohomology

/-! The actual pullback-square functor isomorphism also shows that nonvanishing
of a pulled adjoint forces nonvanishing of the pulled original map. No new
base-change hypothesis is used for these purely adjunction-level facts. -/

namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S)
/-- The natural identification of the two pullback composites around the canonical square for `f`
and `t`. -/
def pullbackSquareFunctorIso :
    Scheme.Modules.pullback t ⋙ Scheme.Modules.pullback (pullback.snd f t) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (pullback.fst f t) :=
  Scheme.Modules.pullbackComp (pullback.snd f t) t ≪≫
    Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := t)).symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst f t) f).symm

theorem pullbackSquare_map_zero {P Q : S.Modules} (β : P ⟶ Q)
    (h : (Scheme.Modules.pullback t).map β = 0) :
    (Scheme.Modules.pullback (pullback.fst f t)).map ((Scheme.Modules.pullback f).map β) = 0 := by
  apply (cancel_epi ((pullbackSquareFunctorIso f t).hom.app P)).mp
  rw [comp_zero]
  exact ((pullbackSquareFunctorIso f t).hom.naturality β).symm.trans (by
    change (Scheme.Modules.pullback (pullback.snd f t)).map
      ((Scheme.Modules.pullback t).map β) ≫ _ = _
    rw [h, Functor.map_zero, zero_comp])

theorem adjoint_pullback_ne_zero {P : S.Modules} {M : X.Modules}
    (θ : (Scheme.Modules.pullback f).obj P ⟶ M)
    (hθ : (Scheme.Modules.pullback (pullback.fst f t)).map θ ≠ 0) :
    (Scheme.Modules.pullback t).map ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _
      _ θ) ≠ 0 := by
  intro h
  have hz := pullbackSquare_map_zero f t _ h
  have he := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_counit _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ θ)
  rw [Equiv.symm_apply_apply] at he
  apply hθ
  rw [he, Functor.map_comp, hz, zero_comp]
end AlgebraicGeometry.Scheme.Cohomology
