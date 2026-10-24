/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.DivisorLocus

/-!
# Consumer checks for the divisors on a fine stratum

A relative effective Cartier divisor whose Abel class lies in the fine stratum
`Pic^{φ₀,ψ,r}_m` is a point of `Div^{ψ − φ₀}_X`, and `Z = Pic^{φ₀,ψ,r}_0 ×_P Div^{ψ − φ₀}_X` is
represented by an H-quasi-projective Noetherian scheme over a Noetherian base (Kleiman, *The
Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, p. 30), also for a representation of
`Div^{ψ − φ₀}_X` given as data; with axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace Scheme.RelativePicard Scheme.RelativePicard.Strata
open Scheme.LocalRepresentability
open scoped Polynomial

universe u

namespace AglibTest.StrataDivisorLocus

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  (N : ℕ) (e : ι ≃ Fin (N + 1)) (φ₀ ψ : ℚ[X]) (r : ℕ)

/-- A relative effective Cartier divisor whose Abel class satisfies the fine condition at every
point, or whose fppf Abel class lies in the fine stratum, is a point of `Div^{ψ − φ₀}_X`. -/
example {T : Over (Spec (CommRingCat.of A))}
    {D : (pullback (i ≫ toSpec A ι) T.hom).IdealSheafData}
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι
      (pullback.snd (i ≫ toSpec A ι) T.hom)) {m : ℤ} :
    ((∀ t, (fineCondition i N e φ₀ ψ m r).Holds T (abelClass _ D hD) t) →
        IsRelativeDivisorFamily i rfl (ψ - φ₀) T.hom D) ∧
      (fppfAbelClass _ D hD ∈ (fineCondition i N e φ₀ ψ m r).subfunctor.obj (op T) →
        IsRelativeDivisorFamily i rfl (ψ - φ₀) T.hom D) :=
  ⟨isRelativeDivisorFamily_of_forall_fineCondition_holds_abelClass hD,
    isRelativeDivisorFamily_of_fppfAbelClass_mem_subfunctor_fineCondition hD⟩

/-- Over a Noetherian base, `Z = Pic^{φ₀,ψ,r}_0 ×_P Div^{ψ − φ₀}_X` is represented by an
H-quasi-projective Noetherian scheme over `Spec A`. -/
example [IsNoetherianRing A] :
    ∃ Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)),
      IsHQuasiProjective Z.obj.hom ∧ IsNoetherian Z.obj.left ∧
        Nonempty ((restrictSubfunctor (Scheme.locallyNoetherianOver _)
          ((fineCondition i N e φ₀ ψ 0 r).abelPreimage i rfl (ψ - φ₀))).toFunctor.RepresentableBy
            Z) :=
  exists_abelPreimage_fineCondition_representableBy i N e φ₀ ψ 0 r

/-- For a representation of `Div^{ψ − φ₀}_X` given as data, `Z` is the open subscheme of the
fine stratum's condition at the universal Abel class; it represents `Z` and is H-quasi-projective
when the representing scheme is. -/
example [IsNoetherianRing A] {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)
    [IsHQuasiProjective D.obj.hom] :
    Nonempty ((restrictSubfunctor (Scheme.locallyNoetherianOver _)
        ((fineCondition i N e φ₀ ψ 0 r).abelPreimage i rfl (ψ - φ₀))).toFunctor.RepresentableBy
          ((fineCondition i N e φ₀ ψ 0 r).abelPreimageOver E)) ∧
      IsHQuasiProjective ((fineCondition i N e φ₀ ψ 0 r).abelPreimageOver E).obj.hom ∧
      IsNoetherian ((fineCondition i N e φ₀ ψ 0 r).abelPreimageOver E).obj.left :=
  ⟨⟨(fineCondition i N e φ₀ ψ 0 r).abelPreimageRepresentableBy E⟩, inferInstance, inferInstance⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.isRelativeDivisorFamily_of_forall_fineCondition_holds_abelClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms isRelativeDivisorFamily_of_forall_fineCondition_holds_abelClass

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.isRelativeDivisorFamily_of_fppfAbelClass_mem_subfunctor_fineCondition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms isRelativeDivisorFamily_of_fppfAbelClass_mem_subfunctor_fineCondition

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.exists_abelPreimage_fineCondition_representableBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_abelPreimage_fineCondition_representableBy

end AglibTest.StrataDivisorLocus
