/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.Glue

/-!
# Consumer checks for the Picard scheme glued from the fine strata

The representability premise in its literal form, the representation of `Pic_{X/S,(fppf)}` by the
glued scheme with its universal section, the chart images and the local finite type (Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, pp. 28–30), with axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata

universe u

namespace AglibTest.PicardSchemeGlue

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  {N : ℕ} {e : ι ≃ Fin (N + 1)}

/-- The premise is the literal statement: every `Pic^{φ₀,ψ,k+1}_0` is represented on locally
Noetherian test schemes by an H-quasi-projective scheme. -/
example (hstrata : ∀ (φ₀ ψ : Polynomial ℚ) (k : ℕ),
      ∃ Q : Scheme.LocallyNoetherianOver (Spec (.of A)), IsHQuasiProjective Q.obj.hom ∧
        Nonempty ((fineCondition i N e φ₀ ψ 0
          (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q)) :
    FineStrataRepresentableByHQuasiProjective i N e :=
  hstrata

variable [GeometricallyIntegral (i ≫ toSpec A ι)]
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- The Picard scheme represents `Pic_{X/S,(fppf)}` on locally Noetherian test schemes; the section
of a morphism is the pullback of the universal section, which is the section of the identity. -/
example {T : Scheme.LocallyNoetherianOver (Spec (.of A))} (a : T ⟶ picardScheme h) :
    (picardSchemeRepresentableBy h).homEquiv a =
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op (picardUniversalSection h) ∧
      (picardSchemeRepresentableBy h).homEquiv (𝟙 _) = picardUniversalSection h :=
  ⟨picardSchemeRepresentableBy_homEquiv h a, picardSchemeRepresentableBy_homEquiv_id h⟩

/-- The chart of `⟨φ, ψ, m, k⟩` is an open immersion onto the open of
`fineCondition φ ψ m (k + 1)`, with H-quasi-projective structure morphism. -/
example (φ ψ : Polynomial ℚ) (m : ℤ) (k : ℕ) :
    IsOpenImmersion ((picardSubfunctorCover h).ιp (ULift.up (φ, ψ, m, k))).hom.left ∧
      Set.range ((picardSubfunctorCover h).ιp (ULift.up (φ, ψ, m, k))).hom.left =
        SetLike.coe ((fineCondition i N e φ ψ m (k + 1)).opens (picardUniversalSection h)) ∧
      IsHQuasiProjective (((picardSubfunctorCover h).ιp (ULift.up (φ, ψ, m, k))).hom.left ≫
        (picardScheme h).obj.hom) :=
  ⟨inferInstance, range_picardChart h _, inferInstance⟩

/-- A morphism to the Picard scheme lands in a chart exactly when it pulls the universal section
into the corresponding fine stratum. -/
example (x : ULift.{u} (Polynomial ℚ × Polynomial ℚ × ℤ × ℕ))
    {Z : Scheme.LocallyNoetherianOver (Spec (.of A))} (g : Z ⟶ picardScheme h) :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map g.hom.op (picardUniversalSection h) ∈
        (picardCoverCondition i N e x).subfunctor.obj (op Z.obj) ↔
      Set.range g.hom.left ⊆ Set.range ((picardSubfunctorCover h).ιp x).hom.left :=
  map_picardUniversalSection_mem_iff h x g

/-- The Picard scheme is locally Noetherian and locally of finite type over `Spec A`. -/
example : IsLocallyNoetherian (picardScheme h).obj.left ∧
    LocallyOfFiniteType (picardScheme h).obj.hom :=
  ⟨inferInstance, inferInstance⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms picardSchemeRepresentableBy

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRepresentableBy_homEquiv_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms picardSchemeRepresentableBy_homEquiv_id

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.range_picardChart' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms range_picardChart

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.locallyOfFiniteType_picardScheme' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms locallyOfFiniteType_picardScheme

end AglibTest.PicardSchemeGlue
