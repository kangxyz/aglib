/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.MayerVietoris
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.Top
public import Aglib.AlgebraicGeometry.Properties.BinaryOpenInduction

/-! # Native source-cover assembly on the unchanged pulled-back charts

This assembly makes its affine and degree-zero inputs explicit. The separated
then quasi-separated binary induction is already proved independently; no
finite-cover descent or affine-overlap assumption is hidden in the interface.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
  (F : AbelianSheaf.{u, u + 1} X')

/-- Positive vanishing for the literal pulled-back source chart and original coefficient. -/
def SourceOpenPositive (U : X.Opens) : Prop :=
  ∀ q : ℕ, 0 < q → IsZero
    ((higherDirectImage (((siteBaseChange g').obj ((opensToEtale X).obj U)).hom ≫ f') q).obj
      ((inverseImage ((siteBaseChange g').obj ((opensToEtale X).obj U)).hom).obj F))

/-- Binary gluing preserves the exact original natural degree, using a degree-zero
restriction difference only in degree one. -/
theorem sourceOpenPositive_sup (U V : X.Opens)
    (hU : SourceOpenPositive g' f' F U) (hV : SourceOpenPositive g' f' F V)
    (hW : SourceOpenPositive g' f' F (U ⊓ V))
    [Epi (sourceEtaleSquareCoefficientComplex f'
      ((etaleOpenSquare U V).map (siteBaseChange g')) F).g] :
    SourceOpenPositive g' f' F (U ⊔ V) := by
  let Q := (etaleOpenSquare U V).map (siteBaseChange g')
  let : Mono (etaleOpenSquare U V).f₂₄ := etaleOpenSquare_f₂₄_mono U V
  let : Mono (etaleOpenSquare U V).f₃₄ := etaleOpenSquare_f₃₄_mono U V
  let : Mono Q.f₂₄ :=
    inferInstanceAs (Mono ((siteBaseChange g').map (etaleOpenSquare U V).f₂₄))
  let : Mono Q.f₃₄ :=
    inferInstanceAs (Mono ((siteBaseChange g').map (etaleOpenSquare U V).f₃₄))
  have hQ : Q.IsPullback := (etaleOpenSquare_isPullback U V).map (siteBaseChange g')
  have hcover : Sieve.ofTwoArrows Q.f₂₄ Q.f₃₄ ∈ X'.smallEtaleTopology Q.X₄ :=
    etaleSquare_baseChange_cover g' (etaleOpenSquare U V) (etaleOpenSquare_cover U V)
  intro q hq
  cases q with
  | zero => exact False.elim (Nat.lt_irrefl 0 hq)
  | succ q =>
    cases q with
    | zero =>
      exact higherDirectImage_etaleSquare_one_isZero f' Q hQ hcover F
        (hU 1 Nat.zero_lt_one) (hV 1 Nat.zero_lt_one)
    | succ q =>
      exact higherDirectImage_etaleSquare_succ_isZero f' Q hQ hcover F (q + 1)
        (hW (q + 1) (Nat.succ_pos _))
        (hU (q + 1 + 1) (Nat.succ_pos _)) (hV (q + 1 + 1) (Nat.succ_pos _))

/-- Source-cover descent requires only the separately supplied affine vanishing
and literal degree-zero difference epis, not a finite-cover descent premise. -/
theorem sourceOpenPositive_of_affine [QuasiSeparatedSpace X]
    (hAffine : ∀ U : X.Opens, IsAffineOpen U → SourceOpenPositive g' f' F U)
    (hEpi : ∀ U V : X.Opens, Epi (sourceEtaleSquareCoefficientComplex f'
      ((etaleOpenSquare U V).map (siteBaseChange g')) F).g)
    (U : X.Opens) (hU : IsCompact (U : Set X)) : SourceOpenPositive g' f' F U := by
  apply Scheme.of_compact_open_of_binary (SourceOpenPositive g' f' F) hAffine _ U hU
  intro V W hV hW hVW
  let : Epi (sourceEtaleSquareCoefficientComplex f'
      ((etaleOpenSquare V W).map (siteBaseChange g')) F).g := hEpi V W
  exact sourceOpenPositive_sup g' f' F V W hV hW hVW

/-- The original top chart returns exactly the unchanged higher direct image. -/
theorem higherDirectImage_positive_of_sourceOpenPositive_top
    (h : SourceOpenPositive g' f' F ⊤) (q : ℕ) (hq : 0 < q) :
    IsZero ((higherDirectImage f' q).obj F) := by
  let U := (siteBaseChange g').obj ((opensToEtale X).obj ⊤)
  let : IsIso ((opensToEtale X).obj (⊤ : X.Opens)).hom :=
    inferInstanceAs (IsIso X.topIso.hom)
  let : IsIso U.hom :=
    inferInstanceAs (IsIso (pullback.snd ((opensToEtale X).obj ⊤).hom g'))
  have hz : IsZero (((sourceEtaleImage f' U).rightDerived q).obj F) :=
    (h q hq).of_iso ((sourceEtaleImageRightDerivedIso f' U q).app F)
  exact hz.of_iso ((sourceEtaleImageRightDerivedIsoOfIso f' U q).app F).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
