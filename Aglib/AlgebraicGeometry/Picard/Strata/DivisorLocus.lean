/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Divisor.ClosedHilbertScheme
public import Aglib.AlgebraicGeometry.Picard.Abel.Divisor
public import Aglib.AlgebraicGeometry.Picard.Strata.DivisorPolynomial

/-!
# The divisors on a fine stratum: the open subscheme `Z` of `Div^θ_X`

Let `i : X ⟶ P^N_A = ProjectiveSpace A ι` be a closed immersion with `ι ≃ Fin (N + 1)` such that
`p = i ≫ toSpec A ι` is flat, let `φ₀, ψ ∈ ℚ[X]`, `m ∈ ℤ`, `r ∈ ℕ`, and put `θ = ψ − φ₀`. Let
`C = fineCondition i N e φ₀ ψ m r` be the fibre condition of the stratum `Pic^{φ₀,ψ,r}_m`
(`Picard/Strata/Conditions`; Kleiman's `P_0^{φ0}` for `m = 0`, refined by `ψ` and `r`).

* `isRelativeDivisorFamily_of_forall_fineCondition_holds_abelClass`: a relative effective Cartier
  divisor `D ⊆ X ×_{Spec A} T` over `T` whose Abel class `−[I_D] = [𝒪(D)]` satisfies `C` at every
  point of `T` is a point of `Div^{ψ − φ₀}_X(T)`. The dual of a representative of the Abel class
  is `I_D` (`classOf_eq_abelClass_iff`, `Picard/Abel/Divisor`), so the fibre Hilbert polynomials of
  the image of `D` in `P^N_A ×_{Spec A} T` are `ψ − φ₀`
  (`Strata.subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_fineCondition_holds`,
  `Picard/Strata/DivisorPolynomial`), the fibre hypothesis of
  `IsRelativeDivisorFamily.of_isRelativeEffectiveCartier`.
  `isRelativeDivisorFamily_of_fppfAbelClass_mem_subfunctor_fineCondition` is the same statement
  when the fppf Abel class lies in `Pic^{φ₀,ψ,r}_m(T)`.
* `exists_abelPreimage_fineCondition_representableBy`: over a Noetherian ring `A`, the functor
  `Pic^{φ₀,ψ,r}_m ×_P Div^θ_X` (`C.abelPreimage i rfl θ`, `Picard/Abel/Divisor`) of the divisors
  with fibre Hilbert polynomial `θ` whose fppf Abel class lies in the stratum is represented on
  locally Noetherian test schemes by an H-quasi-projective Noetherian scheme over `Spec A`. The
  witness is the open subscheme `C.abelPreimageOver E` of the representing scheme of `Div^θ_X`
  given by `exists_locallyNoetherianRelativeDivisorFunctor_representableBy`
  (`HilbertScheme/Divisor/ClosedHilbertScheme`). For a representation `E` given as data, the same
  object, its representation, its universal Abel class and its H-quasi-projectivity are the
  declarations of `Picard/Abel/Divisor` with `C = fineCondition i N e φ₀ ψ m r`.

This is Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, p. 30: "Form the
product `P_0^{φ0} ×_P Div_{X/S}`. It is a scheme `Z`, in fact, an open subscheme of `Div_{X/S}`,
by what was proved above. Set `θ(n) := ψ(n) − φ0(n)`. Plainly `Z` lies in `Hilb^θ_{X/S}(n)`, which
is projective over `S`. Hence `Z` is quasi-projective." Here `Div_{X/S}` is replaced from the start
by `Div^θ_X`; by the first item every relative effective Cartier divisor whose Abel class lies in
the stratum is a point of `Div^θ_X`, so the replacement loses no divisor. Kleiman makes
`ψ(n) = χ(X_s, 𝒪_{X_s}(n))` constant by replacing `S` by an open and closed subset; here `ψ` is
part of the fibre condition (`baseCondition`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

namespace AlgebraicGeometry.Scheme.RelativePicard.Strata

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  {N : ℕ} {e : ι ≃ Fin (N + 1)}

/-- **A divisor on a fine stratum is a point of `Div^{ψ − φ₀}_X`** (Kleiman, arXiv:math/0504020v1,
proof of Thm 4.8, p. 30: "Plainly `Z` lies in `Hilb^θ_{X/S}(n)`"): a relative effective Cartier
divisor `D ⊆ X ×_{Spec A} T` over `T` whose Abel class satisfies `fineCondition φ₀ ψ m r` at every
point of `T` is a point of `Div^{ψ − φ₀}_X(T)`. -/
theorem isRelativeDivisorFamily_of_forall_fineCondition_holds_abelClass
    {T : Over (Spec (.of A))} {D : (pullback (i ≫ toSpec A ι) T.hom).IdealSheafData}
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd (i ≫ toSpec A ι) T.hom))
    {φ₀ ψ : ℚ[X]} {m : ℤ} {r : ℕ}
    (h : ∀ t, (fineCondition i N e φ₀ ψ m r).Holds T (abelClass (i ≫ toSpec A ι) D hD) t) :
    IsRelativeDivisorFamily i rfl (ψ - φ₀) T.hom D := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have := hD.flat
  obtain ⟨eL⟩ := nonempty_dualLineBundle_iso_idealModule_of_classOf_eq_abelClass
    (i ≫ toSpec A ι) hD (L := dualLineBundle _ hD.idealLineBundle) rfl
  exact IsRelativeDivisorFamily.of_isRelativeEffectiveCartier i rfl (ψ - φ₀) hD
    (subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_fineCondition_holds i N e eL h)

/-- **The fppf form**: a relative effective Cartier divisor `D ⊆ X ×_{Spec A} T` over `T` whose
fppf Abel class lies in `Pic^{φ₀,ψ,r}_m(T)` is a point of `Div^{ψ − φ₀}_X(T)`. -/
theorem isRelativeDivisorFamily_of_fppfAbelClass_mem_subfunctor_fineCondition
    {T : Over (Spec (.of A))} {D : (pullback (i ≫ toSpec A ι) T.hom).IdealSheafData}
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd (i ≫ toSpec A ι) T.hom))
    {φ₀ ψ : ℚ[X]} {m : ℤ} {r : ℕ}
    (h : fppfAbelClass (i ≫ toSpec A ι) D hD ∈
      (fineCondition i N e φ₀ ψ m r).subfunctor.obj (op T)) :
    IsRelativeDivisorFamily i rfl (ψ - φ₀) T.hom D :=
  isRelativeDivisorFamily_of_forall_fineCondition_holds_abelClass hD
    (((fineCondition i N e φ₀ ψ m r).app_mem_subfunctor_iff
      (abelClass (i ≫ toSpec A ι) D hD)).mp h)

variable (i N e) in
/-- **`Z = Pic^{φ₀,ψ,r}_m ×_P Div^{ψ − φ₀}_X` is an H-quasi-projective Noetherian scheme**
(Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 30, on locally Noetherian test schemes): over
a Noetherian ring `A`, the divisors with fibre Hilbert polynomial `ψ − φ₀` whose fppf Abel class
lies in `Pic^{φ₀,ψ,r}_m` are represented by an H-quasi-projective, hence Noetherian, scheme over
`Spec A`, an open subscheme of the representing scheme of `Div^{ψ − φ₀}_X`. -/
theorem exists_abelPreimage_fineCondition_representableBy [IsNoetherianRing A]
    (φ₀ ψ : ℚ[X]) (m : ℤ) (r : ℕ) :
    ∃ Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)),
      IsHQuasiProjective Z.obj.hom ∧ IsNoetherian Z.obj.left ∧
        Nonempty ((LocalRepresentability.restrictSubfunctor (Scheme.locallyNoetherianOver _)
          ((fineCondition i N e φ₀ ψ m r).abelPreimage i rfl (ψ - φ₀))).toFunctor.RepresentableBy
            Z) := by
  obtain ⟨D, hD, -, ⟨E⟩⟩ :=
    exists_locallyNoetherianRelativeDivisorFunctor_representableBy ι N e A i rfl (ψ - φ₀)
  exact ⟨(fineCondition i N e φ₀ ψ m r).abelPreimageOver E, inferInstance, inferInstance,
    ⟨(fineCondition i N e φ₀ ψ m r).abelPreimageRepresentableBy E⟩⟩

end AlgebraicGeometry.Scheme.RelativePicard.Strata
