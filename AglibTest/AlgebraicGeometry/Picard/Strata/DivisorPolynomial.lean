/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Strata.DivisorPolynomial
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic

/-! Focused consumer of the Hilbert polynomial of a divisor on a stratum of the Picard functor
(Kleiman, arXiv:math/0504020v1, p. 30: "Plainly `Z` lies in `Hilb^θ_{X/S}(n)`"): the bridge between the
Euler condition of `L` and the Euler characteristics of `I_D` when `L^{-1} ≅ I_D`, the Hilbert
polynomial `ψ − φ₀` of a fibre at a point, and on a family in the shape of the fibre hypothesis of
the divisor functor `Div^θ_X`, also from the fine stratum condition, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.RelativePicard
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι)

/-- **The bridge**: for `L^{-1} ≅ I_D`, `C_{φ₀}` holds for `L` at `t` exactly when
`χ(X_t, (I_D)_t(n)) = φ₀(n)` for all `n`, and, for `D` flat, when `χ(X_t, I_{D_t}(n)) = φ₀(n)` for
the ideal of the fibre `D_t`. -/
example {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    {D : (pullback (i ≫ toSpec A ι) g).IdealSheafData}
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd (i ≫ toSpec A ι) g))
    {L : LineBundle (pullback (i ≫ toSpec A ι) g)}
    (eL : (dualLineBundle _ L).val ≅ Scheme.Hom.idealModule D.subschemeι) (φ₀ : ℚ[X]) (t : T) :
    (HasFiberDualEulerPolynomial i g φ₀ L t ↔ ∀ n : ℤ,
      (embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj
          (Scheme.Hom.idealModule D.subschemeι)) n : ℚ) = φ₀.eval (n : ℚ)) ∧
    (HasFiberDualEulerPolynomial i g φ₀ L t ↔ ∀ n : ℤ,
      (embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        (Scheme.Hom.idealModule
          (D.comap (residueFieldBaseChange (i ≫ toSpec A ι) g t)).subschemeι) n : ℚ) =
            φ₀.eval (n : ℚ)) :=
  haveI := hD.flat
  ⟨hasFiberDualEulerPolynomial_iff_of_iso i g eL φ₀ t,
    hasFiberDualEulerPolynomial_iff_idealModule_comap i g eL φ₀ t⟩

/-- **At a point**: with `C_ψ` and `C_{φ₀}` for `L^{-1} ≅ I_D` at `t`, the fibre of the image of
`D` at `t` has Hilbert polynomial `ψ − φ₀`. -/
example [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1)) {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) {D : (pullback (i ≫ toSpec A ι) g).IdealSheafData}
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd (i ≫ toSpec A ι) g))
    {L : LineBundle (pullback (i ≫ toSpec A ι) g)}
    (eL : (dualLineBundle _ L).val ≅ Scheme.Hom.idealModule D.subschemeι) {φ₀ ψ : ℚ[X]} (t : T)
    (hφ₀ : HasFiberDualEulerPolynomial i g φ₀ L t) (hψ : HasFiberStructureEulerPolynomial i g ψ t) :
    subschemeHilbertPolynomial ι (T.residueField t)
      ((D.map (immersionBaseChange i rfl g)).comap (pointMap ι g (T.fromSpecResidueField t))) =
        ψ - φ₀ :=
  haveI := hD.flat
  subschemeHilbertPolynomial_comap_pointMap_fromSpecResidueField_eq_sub i g N e D hψ
    ((hasFiberDualEulerPolynomial_iff_of_iso i g eL φ₀ t).mp hφ₀)

/-- **The fibre hypothesis of `Div^θ_X`**: for a relative effective Cartier divisor `D` with
`L^{-1} ≅ I_D`, where `L` satisfies `C_{φ₀}` and `C_ψ` holds at every point, the image of `D` is a point
of `Hilb^{ψ − φ₀}` and its fibre at every field point has Hilbert polynomial `θ = ψ − φ₀`, in the
binder shape `∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T), …` with `hi = rfl`. -/
example [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1)) {T : Scheme.{u}}
    {g : T ⟶ Spec (CommRingCat.of A)} {D : (pullback (i ≫ toSpec A ι) g).IdealSheafData}
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd (i ≫ toSpec A ι) g))
    {L : LineBundle (pullback (i ≫ toSpec A ι) g)}
    (eL : (dualLineBundle _ L).val ≅ Scheme.Hom.idealModule D.subschemeι) {φ₀ ψ : ℚ[X]}
    (hφ₀ : ∀ t, HasFiberDualEulerPolynomial i g φ₀ L t)
    (hψ : ∀ t, HasFiberStructureEulerPolynomial i g ψ t) :
    IsHilbertFamily ι (ψ - φ₀) g (D.map (immersionBaseChange i rfl g)) ∧
      ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T),
        subschemeHilbertPolynomial ι K
          ((D.map (immersionBaseChange i rfl g)).comap (pointMap ι g x)) = ψ - φ₀ :=
  haveI := hD.flat
  ⟨isHilbertFamily_map_immersionBaseChange_of_hasFiberDualEulerPolynomial i g N e eL hφ₀ hψ,
    subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_hasFiberDualEulerPolynomial i g N e eL
      hφ₀ hψ⟩

/-- **From the fine stratum condition**: if the class of `L` satisfies `fineCondition φ₀ ψ m r` at
every point of `T`, the fibre hypothesis of `Div^{ψ − φ₀}_X` holds for `D`. -/
example [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] (N : ℕ) (e : ι ≃ Fin (N + 1))
    {T : Over (Spec (CommRingCat.of A))} {D : (pullback (i ≫ toSpec A ι) T.hom).IdealSheafData}
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι
      (pullback.snd (i ≫ toSpec A ι) T.hom))
    {L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)}
    (eL : (dualLineBundle _ L).val ≅ Scheme.Hom.idealModule D.subschemeι) {φ₀ ψ : ℚ[X]} {m : ℤ}
    {r : ℕ} (h : ∀ t, (Strata.fineCondition i N e φ₀ ψ m r).Holds T (classOf _ L) t) :
    ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T.left),
      subschemeHilbertPolynomial ι K
        ((D.map (immersionBaseChange i rfl T.hom)).comap (pointMap ι T.hom x)) = ψ - φ₀ :=
  haveI := hD.flat
  Strata.subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_fineCondition_holds i N e eL h

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.hasFiberDualEulerPolynomial_iff_of_iso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hasFiberDualEulerPolynomial_iff_of_iso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.hasFiberDualEulerPolynomial_iff_idealModule_comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hasFiberDualEulerPolynomial_iff_idealModule_comap

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.subschemeHilbertPolynomial_comap_pointMap_fromSpecResidueField_eq_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms subschemeHilbertPolynomial_comap_pointMap_fromSpecResidueField_eq_sub

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isHilbertFamily_map_immersionBaseChange_of_hasFiberDualEulerPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isHilbertFamily_map_immersionBaseChange_of_hasFiberDualEulerPolynomial

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_hasFiberDualEulerPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_hasFiberDualEulerPolynomial

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_fineCondition_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Strata.subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_fineCondition_holds
