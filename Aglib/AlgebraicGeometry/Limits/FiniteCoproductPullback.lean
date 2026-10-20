/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Finite coproducts commute with scheme pullbacks

General declarations extracted from R5 baseline
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; names, chosen maps and hypotheses retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.FiniteCoproductPullback` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5044cc0a98ce462a1d8b5a26708be0bd87a4d1d6425ea8c2498a1e2020cd1915`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u
universe v

namespace AlgebraicGeometry
namespace FiniteCoproductPullback
variable {I : Type v} [Finite I] (X : I → Scheme.{u}) {S Y : Scheme.{u}}
  (f : ∀ i, X i ⟶ S) (g : Y ⟶ S)

/-- Finite scheme coproducts are preserved by the actual pullback, with the
literal pointwise projections as its two maps. -/
theorem square : IsPullback
    (Limits.Sigma.map (fun i => pullback.fst (f i) g))
    (Sigma.desc (fun i => pullback.snd (f i) g)) (Sigma.desc f) g := by
  have h := (FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct X)).isPullback_of_isColimit_right
      f (Sigma.desc f) g (fun i => pullback.fst (f i) g)
      (fun i => pullback.snd (f i) g) (fun i => IsPullback.of_hasPullback (f i) g)
      (coproductIsCoproduct (fun i => pullback (f i) g))
      (fun i => by simp)
  convert! h using 1

/-- The canonical finite coproduct/pullback comparison isomorphism. -/
def iso : (∐ fun i => pullback (f i) g) ≅ pullback (Sigma.desc f) g :=
  (square X f g).isoPullback

@[reassoc, simp] theorem iso_hom_fst :
    (iso X f g).hom ≫ pullback.fst (Sigma.desc f) g =
      Limits.Sigma.map (fun i => pullback.fst (f i) g) :=
  (square X f g).isoPullback_hom_fst

@[reassoc, simp] theorem iso_hom_snd :
    (iso X f g).hom ≫ pullback.snd (Sigma.desc f) g =
      Sigma.desc (fun i => pullback.snd (f i) g) :=
  (square X f g).isoPullback_hom_snd

end FiniteCoproductPullback
end AlgebraicGeometry
