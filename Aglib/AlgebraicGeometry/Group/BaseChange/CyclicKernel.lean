/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.ScalarExtension
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricDegree
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover

/-!
# Actual field base change of cyclic coefficients and fibre degrees

The multiplicative pullback-point equivalence transports geometric
cyclicity and the cardinality of each actual morphism fibre along the
specified field-spectrum map. Universal kernel marking transport reuses
`Scheme.Group.BaseChange.kernelMarking` from `BaseChange.MarkedKernel`.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.BaseChange.CyclicKernel`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`7f0fd61a87f507be282903088acdb6d34ce9571495ad44a21f5b06c3c2634bc0`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

open AlgebraicGeometry.Scheme.OverField (Base FScheme HasGeometricDegree)
open AlgebraicGeometry.Scheme.FiniteEtale.PointedCovers

namespace AlgebraicGeometry.Scheme.Group.BaseChange

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {F K : Type u} [Field F] [Field K] (s : Base K ⟶ Base F)

/-- The coefficient is pulled back as an actual group scheme; geometric
cyclicity is transported by the actual multiplicative point-fibre equivalence. -/
theorem cyclicCoefficientBaseChange {A : Grp (FScheme F)} {n : ℕ}
    (a : CyclicCoefficient A n) :
    CyclicCoefficient ((groupSchemeBaseChange s).functor.obj A) n where
  positive := a.positive
  finite := by let := a.finite; exact inferInstanceAs (IsFinite (pullback.snd A.X.hom s))
  etale := by let := a.etale; exact inferInstanceAs (Etale (pullback.snd A.X.hom s))
  geometric_cyclic L _ _ t := by
    obtain ⟨e⟩ := a.geometric_cyclic L (t ≫ s)
    exact ⟨(pullbackFiberMulEquiv s t A).symm.trans e⟩

/-- Degree is transported using actual points of the canonical pullback,
without introducing a rank or new degree hypothesis. -/
theorem geometricDegreeBaseChange {G E : Grp (FScheme F)} (p : G ⟶ E) {n : ℕ}
    (h : HasGeometricDegree p.hom.hom n) :
    HasGeometricDegree ((groupSchemeBaseChange s).functor.map p).hom.hom n := by
  intro L _ _ t y
  let eG := pullbackFiberMulEquiv s t G
  let eE := pullbackFiberMulEquiv s t E
  let y₀ := eE.symm y
  have he (x : Over.mk (t ≫ s) ⟶ G.X) :
      x ≫ p.hom.hom = y₀ ↔ eG x ≫ ((groupSchemeBaseChange s).functor.map p).hom.hom = y := by
    rw [← pullbackFiberMulEquiv_naturality s t p x]
    exact ⟨fun hx => by rw [hx, eE.apply_symm_apply],
      fun hx => eE.injective (hx.trans (eE.apply_symm_apply y).symm)⟩
  let e : {x : Over.mk (t ≫ s) ⟶ G.X // x ≫ p.hom.hom = y₀} ≃
      {x : Over.mk t ⟶ ((groupSchemeBaseChange s).functor.obj G).X //
        x ≫ ((groupSchemeBaseChange s).functor.map p).hom.hom = y} :=
    eG.toEquiv.subtypeEquiv he
  exact (Nat.card_congr e).symm.trans (h L (t ≫ s) y₀)

end AlgebraicGeometry.Scheme.Group.BaseChange
