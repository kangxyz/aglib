/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.LocalOnBase

/-!
# Flatness of a base change through an intermediate Cartesian square

Let `IsPullback a b p j` be a pullback square, `P = X ×_S Y`, and `M` a quasi-coherent module on
`X`. For `g' : T ⟶ Y`, the base change of `M` along `g' ≫ j` is flat over `T` exactly when the
base change of `a^* M` along `g'` is (`relativeFlat_pullback_comp_iff_of_isPullback`): both are
base changes of `M` along `g' ≫ j`, through two pullback squares, and their pulled-back modules
are identified by `Scheme.Modules.pullbackComp`.

`relativeFlat_iff_of_isPullback` compares two pullback squares along the same morphism.
`relativeFlat_pullback_snd_opensι` and `relativeFlat_pullback_snd_of_forall_opens` restate the
locality on the test scheme of `LocalOnBase` for the chosen pullbacks along restrictions to opens.

This is the form in which flatness over a test scheme `T ⟶ U ⊆ S`, for an affine open `U` of the
base of a projective family `X_S ⟶ S`, is read on the restriction `X_U ⟶ U` (used for Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Thm 4.3 (ii), over a non-affine
base).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- **Flatness of a base change through an intermediate Cartesian square.** For a pullback square
`IsPullback a b p j`, a quasi-coherent `M` on `X` and `g' : T ⟶ Y`, the pullback of `M` to
`X ×_S T` (along `g' ≫ j`) is flat over `T` if and only if the pullback of `a^* M` to `P ×_Y T` is
flat over `T`. -/
theorem relativeFlat_pullback_comp_iff_of_isPullback {X S Y P T : Scheme.{u}} {p : X ⟶ S}
    {j : Y ⟶ S} {a : P ⟶ X} {b : P ⟶ Y} (hsq : IsPullback a b p j) (M : X.Modules)
    [M.IsQuasicoherent] (g' : T ⟶ Y) :
    relativeFlat (pullback.snd p (g' ≫ j))
        ((Scheme.Modules.pullback (pullback.fst p (g' ≫ j))).obj M) ↔
      relativeFlat (pullback.snd b g')
        ((Scheme.Modules.pullback (pullback.fst b g')).obj
          ((Scheme.Modules.pullback a).obj M)) := by
  have hsq' : IsPullback (pullback.fst b g' ≫ a) (pullback.snd b g') p (g' ≫ j) :=
    (IsPullback.of_hasPullback b g').paste_horiz hsq
  have e : (Scheme.Modules.pullback (pullback.fst b g' ≫ a)).obj M ≅
      (Scheme.Modules.pullback (pullback.fst b g')).obj ((Scheme.Modules.pullback a).obj M) :=
    ((Scheme.Modules.pullbackComp (pullback.fst b g') a).app M).symm
  constructor
  · intro h
    refine relativeFlat_of_iso _ e.symm ?_
    exact relativeFlat_of_isPullback_comp (IsPullback.of_hasPullback p (g' ≫ j)) (j := 𝟙 T)
      (by rwa [Category.id_comp]) M h
  · intro h
    exact relativeFlat_of_isPullback_comp hsq' (j := 𝟙 T)
      (by rw [Category.id_comp]; exact IsPullback.of_hasPullback p (g' ≫ j)) M
      (relativeFlat_of_iso _ e h)

/-- **Flatness of a base change does not depend on the pullback square**: for two pullback squares
`IsPullback a₁ b₁ p g` and `IsPullback a₂ b₂ p g` of `p` along the same `g` and quasi-coherent
`M`, `a₁^* M` is flat over `T` through `b₁` if and only if `a₂^* M` is flat over `T` through
`b₂`. -/
theorem relativeFlat_iff_of_isPullback {X S T P₁ P₂ : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
    {a₁ : P₁ ⟶ X} {b₁ : P₁ ⟶ T} {a₂ : P₂ ⟶ X} {b₂ : P₂ ⟶ T} (h₁ : IsPullback a₁ b₁ p g)
    (h₂ : IsPullback a₂ b₂ p g) (M : X.Modules) [M.IsQuasicoherent] :
    relativeFlat b₁ ((Scheme.Modules.pullback a₁).obj M) ↔
      relativeFlat b₂ ((Scheme.Modules.pullback a₂).obj M) :=
  ⟨relativeFlat_of_isPullback_comp h₁ (j := 𝟙 T) (by rwa [Category.id_comp]) M,
    relativeFlat_of_isPullback_comp h₂ (j := 𝟙 T) (by rwa [Category.id_comp]) M⟩

/-- **Restriction of a flat base change to an open of the test scheme**: if the pullback of `M`
along `g : T ⟶ S` is flat over `T`, then so is its pullback along `V.ι ≫ g` over `V`. -/
theorem relativeFlat_pullback_snd_opensι {X S T : Scheme.{u}} (p : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] (g : T ⟶ S) (V : T.Opens)
    (h : relativeFlat (pullback.snd p g) ((Scheme.Modules.pullback (pullback.fst p g)).obj M)) :
    relativeFlat (pullback.snd p (V.ι ≫ g))
      ((Scheme.Modules.pullback (pullback.fst p (V.ι ≫ g))).obj M) :=
  relativeFlat_of_isPullback_comp (IsPullback.of_hasPullback p g)
    (IsPullback.of_hasPullback p (V.ι ≫ g)) M h

/-- **Flatness of a base change is local on the test scheme**, for open subschemes: if every
point of `T` has an open neighbourhood `V` over which the pullback of `M` along `V.ι ≫ g` is
flat, then the pullback of `M` along `g` is flat over `T`. -/
theorem relativeFlat_pullback_snd_of_forall_opens {X S T : Scheme.{u}} (p : X ⟶ S)
    (M : X.Modules) (g : T ⟶ S)
    (H : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧ relativeFlat (pullback.snd p (V.ι ≫ g))
      ((Scheme.Modules.pullback (pullback.fst p (V.ι ≫ g))).obj M)) :
    relativeFlat (pullback.snd p g) ((Scheme.Modules.pullback (pullback.fst p g)).obj M) :=
  relativeFlat_of_isPullback_of_forall_exists (IsPullback.of_hasPullback p g) M fun t => by
    obtain ⟨V, htV, hV⟩ := H t
    exact ⟨V.toScheme, V.ι, inferInstance, ⟨⟨t, htV⟩, rfl⟩, _, _, _,
      IsPullback.of_hasPullback _ _, hV⟩

end AlgebraicGeometry.Scheme.Modules
