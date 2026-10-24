/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Conditions
public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Fiber
public import Aglib.AlgebraicGeometry.HilbertScheme.ResidueField

/-!
# The Hilbert polynomial of a divisor on a stratum of the Picard functor

Let `i : X ⟶ P^N_A = ProjectiveSpace A ι` be a closed immersion with `ι ≃ Fin (N + 1)`,
`f = i ≫ toSpec A ι`, `g : T ⟶ Spec A`, and `V ⊆ X_T = X ×_{Spec A} T` a closed subscheme flat
over `T`, for example a relative effective Cartier divisor `D` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Def. 3.3, p. 22). For `t ∈ T` write `X_t = X ×_{Spec A} Spec κ(t)` and
`(I_V)_t` for the pullback of the ideal `I_V` along `X_t ⟶ X_T` (`residueFieldBaseChange`).
Let `L` be a line bundle on `X_T` with `L^{-1} ≅ I_V`; for a divisor `D` this is `O(D) ≅ L`,
since `I_D = O(−D)` (Kleiman, 3.1, p. 22), that is, `L` represents the image of `D` under the Abel
map (Def. 4.6, p. 27).

* **The bridge to the strata conditions** (`hasFiberDualEulerPolynomial_iff_of_iso`): the Euler
  condition `C_{φ₀}` of `L` at `t` (`HasFiberDualEulerPolynomial`: `χ(X_t, L_t^{-1}(n)) = φ₀(n)`,
  Kleiman (4.8.1), p. 28) holds exactly when `χ(X_t, (I_V)_t(n)) = φ₀(n)` for all `n`; for `V`
  flat, `(I_V)_t` is the ideal of the fibre `V_t ⊆ X_t`
  (`hasFiberDualEulerPolynomial_iff_idealModule_comap`).
* **At a point** (`subschemeHilbertPolynomial_comap_pointMap_fromSpecResidueField_eq_sub`): if the
  base condition `C_ψ` holds at `t` (`HasFiberStructureEulerPolynomial`: `χ(X_t, O(n)) = ψ(n)`)
  and `χ(X_t, (I_V)_t(n)) = φ₀(n)` for all `n`, the fibre at `t` of the image of `V` in
  `P^N_A ×_{Spec A} T` has Hilbert polynomial `ψ − φ₀`. This instantiates the variable-field
  statement `subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_eq_sub` of
  `HilbertScheme/Immersed/Fiber` (the sequence `0 → I_{V_t}(n) → O_{X_t}(n) → O_{V_t}(n) → 0` on
  `P^N_{κ(t)}`).
* **On a family** (`isHilbertFamily_map_immersionBaseChange_of_hasFiberDualEulerPolynomial`,
  `subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_hasFiberDualEulerPolynomial`): if `L`
  satisfies `C_{φ₀}` and `C_ψ` holds at every point of `T`, the image of `V` is a point of
  `Hilb^{ψ − φ₀}(T)`, and its fibre at every field point `x : Spec K ⟶ T` has Hilbert polynomial
  `θ = ψ − φ₀`; this is the hypothesis on the fibres of the construction of a point of the divisor
  functor `Div^θ_X` from a relative effective Cartier divisor. Field points reduce to residue fields
  by `isHilbertFamily_iff_residueField`. The fine-stratum form is
  `Strata.subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_fineCondition_holds`: it suffices
  that `[L]` satisfies `fineCondition φ₀ ψ m r` at every point.

This is Kleiman's "Set `θ(n) := ψ(n) − φ₀(n)`. Plainly `Z` lies in `Hilb^θ_{X/S}(n)`, which is
projective over `S`" (p. 30, proof of Thm 4.8), where `ψ(n) = χ(X_s, O_{X_s}(n))` is made constant
by replacing `S` by an open and closed subset; here `ψ` enters through the fibre condition
`HasFiberStructureEulerPolynomial`. Only the flatness of `V` over `T` and the isomorphism
`L^{-1} ≅ I_V` are used; the Cartier property of a divisor is what makes `I_D` a line bundle.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) {T : Scheme.{u}} (g : T ⟶ Spec (.of A))

/-! ### The bridge to the Euler condition -/

/-- **The Euler condition through an isomorphism of the dual**: if `L^{-1} ≅ M` for a module `M` on
`X_T`, then `C_{φ}` holds for `L` at `t` exactly when `χ(X_t, M_t(n)) = φ(n)` for every `n : ℤ`,
for the pullback `M_t` of `M` to the fibre `X_t`. -/
theorem hasFiberDualEulerPolynomial_iff_of_iso {L : LineBundle (pullback (i ≫ toSpec A ι) g)}
    {M : (pullback (i ≫ toSpec A ι) g).Modules} (eL : (dualLineBundle _ L).val ≅ M)
    (φ : ℚ[X]) (t : T) :
    HasFiberDualEulerPolynomial i g φ L t ↔ ∀ n : ℤ,
      (embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj M) n : ℚ) =
          φ.eval (n : ℚ) := by
  refine forall_congr' fun n => ?_
  have h : fiberDualTwistEulerChar i g L t n =
      embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj M) n :=
    embeddedFiberTwistEulerChar_congr i _
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).mapIso eL) n
  rw [h]

/-- **The Euler condition and the ideal of the fibre**: for a closed subscheme `V ⊆ X_T` flat over
`T` and a line bundle `L` with `L^{-1} ≅ I_V`, `C_{φ}` holds for `L` at `t` exactly when
`χ(X_t, I_{V_t}(n)) = φ(n)` for every `n : ℤ`, for the ideal `I_{V_t}` of the fibre `V_t ⊆ X_t`. -/
theorem hasFiberDualEulerPolynomial_iff_idealModule_comap
    {V : (pullback (i ≫ toSpec A ι) g).IdealSheafData}
    [Flat (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g)]
    {L : LineBundle (pullback (i ≫ toSpec A ι) g)}
    (eL : (dualLineBundle _ L).val ≅ Scheme.Hom.idealModule V.subschemeι) (φ : ℚ[X]) (t : T) :
    HasFiberDualEulerPolynomial i g φ L t ↔ ∀ n : ℤ,
      (embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        (Scheme.Hom.idealModule
          (V.comap (residueFieldBaseChange (i ≫ toSpec A ι) g t)).subschemeι) n : ℚ) =
            φ.eval (n : ℚ) := by
  refine (hasFiberDualEulerPolynomial_iff_of_iso i g eL φ t).trans (forall_congr' fun n => ?_)
  have h : embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj
        (Scheme.Hom.idealModule V.subschemeι)) n =
      embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        (Scheme.Hom.idealModule
          (V.comap (residueFieldBaseChange (i ≫ toSpec A ι) g t)).subschemeι) n :=
    embeddedFiberTwistEulerChar_congr i _
      (fieldPointIdealPullbackIso i g (T.fromSpecResidueField t) V) n
  rw [h]

/-! ### The Hilbert polynomial at a point -/

/-- **The Hilbert polynomial of a fibre at a point of a stratum**: for a closed immersion `i`,
`ι ≃ Fin (N + 1)`, a closed subscheme `V ⊆ X_T` flat over `T` and `t ∈ T`, if `C_ψ` holds at `t`
and `χ(X_t, (I_V)_t(n)) = φ₀(n)` for every `n`, the fibre at `t` of the image of `V` in
`P^N_A ×_{Spec A} T` has Hilbert polynomial `ψ − φ₀`. -/
theorem subschemeHilbertPolynomial_comap_pointMap_fromSpecResidueField_eq_sub
    [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
    [Flat (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g)] {ψ φ₀ : ℚ[X]} {t : T}
    (hψ : HasFiberStructureEulerPolynomial i g ψ t)
    (hφ₀ : ∀ n : ℤ,
      (embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj
          (Scheme.Hom.idealModule V.subschemeι)) n : ℚ) = φ₀.eval (n : ℚ)) :
    subschemeHilbertPolynomial ι (T.residueField t)
      ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g (T.fromSpecResidueField t))) =
        ψ - φ₀ :=
  subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_eq_sub i g
    (T.fromSpecResidueField t) V N e (fun n => (fiberStructureEulerChar_eq i g t n) ▸ hψ n) hφ₀

/-! ### Families -/

section Family

variable [IsClosedImmersion i] {V : (pullback (i ≫ toSpec A ι) g).IdealSheafData}
  [Flat (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g)]
  {L : LineBundle (pullback (i ≫ toSpec A ι) g)}

/-- **The image of `V` is a point of `Hilb^{ψ − φ₀}`**: for a closed subscheme `V ⊆ X_T` flat over
`T` and a line bundle `L` with `L^{-1} ≅ I_V`, if `L` satisfies `C_{φ₀}` and `C_ψ` holds at every
point of `T`, the image of `V` in `P^N_A ×_{Spec A} T` is flat over `T` with all fibre Hilbert
polynomials `ψ − φ₀`. -/
theorem isHilbertFamily_map_immersionBaseChange_of_hasFiberDualEulerPolynomial (N : ℕ)
    (e : ι ≃ Fin (N + 1)) (eL : (dualLineBundle _ L).val ≅ Scheme.Hom.idealModule V.subschemeι)
    {φ₀ ψ : ℚ[X]}
    (hφ₀ : ∀ t, HasFiberDualEulerPolynomial i g φ₀ L t)
    (hψ : ∀ t, HasFiberStructureEulerPolynomial i g ψ t) :
    IsHilbertFamily ι (ψ - φ₀) g (V.map (immersionBaseChange i rfl g)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  refine (isHilbertFamily_iff_residueField ι _).mpr
    ⟨flat_map_immersionBaseChange_subschemeι_comp_snd i g rfl V, fun t => ?_⟩
  exact subschemeHilbertPolynomial_comap_pointMap_fromSpecResidueField_eq_sub i g N e V (hψ t)
    ((hasFiberDualEulerPolynomial_iff_of_iso i g eL φ₀ t).mp (hφ₀ t))

/-- **The fibres of a divisor on a stratum have Hilbert polynomial `θ = ψ − φ₀`** (Kleiman,
arXiv:math/0504020v1, p. 30: "Plainly `Z` lies in `Hilb^θ_{X/S}(n)`"): for a closed subscheme
`V ⊆ X_T` flat over `T`, for example a relative effective Cartier divisor, and a line bundle `L`
with `L^{-1} ≅ I_V`, if `L` satisfies `C_{φ₀}` and `C_ψ` holds at every point of `T`, then the fibre
at every field point of the image of `V` in `P^N_A ×_{Spec A} T` has Hilbert polynomial `ψ − φ₀`. -/
theorem subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_hasFiberDualEulerPolynomial
    (N : ℕ) (e : ι ≃ Fin (N + 1))
    (eL : (dualLineBundle _ L).val ≅ Scheme.Hom.idealModule V.subschemeι) {φ₀ ψ : ℚ[X]}
    (hφ₀ : ∀ t, HasFiberDualEulerPolynomial i g φ₀ L t)
    (hψ : ∀ t, HasFiberStructureEulerPolynomial i g ψ t) :
    ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T),
      subschemeHilbertPolynomial ι K
        ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x)) = ψ - φ₀ :=
  (isHilbertFamily_map_immersionBaseChange_of_hasFiberDualEulerPolynomial i g N e eL hφ₀
    hψ).subschemeHilbertPolynomial_fiber

end Family

namespace Strata

/-- **The fibres of a divisor on a fine stratum have Hilbert polynomial `ψ − φ₀`**: for a closed
immersion `i` with `i ≫ toSpec A ι` flat, a closed subscheme `V ⊆ X_T` flat over `T` (for example a
relative effective Cartier divisor) and a line bundle `L` with `L^{-1} ≅ I_V`, if the class of `L`
satisfies `fineCondition φ₀ ψ m r` at every point of `T`, then the fibre at every field point of the
image of `V` in `P^N_A ×_{Spec A} T` has Hilbert polynomial `ψ − φ₀`. -/
theorem subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_fineCondition_holds
    [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] (N : ℕ) (e : ι ≃ Fin (N + 1))
    {T : Over (Spec (.of A))} {V : (pullback (i ≫ toSpec A ι) T.hom).IdealSheafData}
    [Flat (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) T.hom)]
    {L : LineBundle (pullback (i ≫ toSpec A ι) T.hom)}
    (eL : (dualLineBundle _ L).val ≅ Scheme.Hom.idealModule V.subschemeι) {φ₀ ψ : ℚ[X]} {m : ℤ}
    {r : ℕ} (h : ∀ t, (fineCondition i N e φ₀ ψ m r).Holds T (classOf _ L) t) :
    ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T.left),
      subschemeHilbertPolynomial ι K
        ((V.map (immersionBaseChange i rfl T.hom)).comap (pointMap ι T.hom x)) = ψ - φ₀ :=
  subschemeHilbertPolynomial_comap_pointMap_eq_sub_of_hasFiberDualEulerPolynomial i T.hom N e eL
    (fun t => ((fineCondition_holds_classOf φ₀ ψ m r T L t).mp (h t)).1)
    (fun t => ((fineCondition_holds_classOf φ₀ ψ m r T L t).mp (h t)).2.1)

end Strata

end AlgebraicGeometry.Scheme.RelativePicard
