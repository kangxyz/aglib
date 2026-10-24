/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Functor
public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Projective
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Flat
public import Aglib.AlgebraicGeometry.IdealSheaf.Comap
public import Aglib.AlgebraicGeometry.IdealSheaf.QuotientModule.Map
public import Aglib.AlgebraicGeometry.Limits.FibreProductBaseChange
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion

/-!
# Hilbert polynomials of the fibres of closed subschemes of an embedded family

Let `i : X ⟶ P^N_A = ProjectiveSpace A ι` be a morphism, `f = i ≫ toSpec A ι`, `g : T ⟶ Spec A`,
`X_T = X ×_{Spec A} T` and `i_T = immersionBaseChange i rfl g : X_T ⟶ P_T = P^N_A ×_{Spec A} T`.
For a field point `x : Spec K ⟶ T` write `X_x = X ×_{Spec A} Spec K` (`pullback f (x ≫ g)`),
`b_x = pullback.map f (x ≫ g) f g (𝟙 X) x (𝟙 _) : X_x ⟶ X_T`, and
`ι_x = embeddedFiberι i (x ≫ g) : X_x ⟶ P^N_K` for the fibre embedding of
`Cohomology/Projective/EmbeddedFibers/Projective`. For a closed subscheme `V ⊆ X_T` its fibre is
`V_x = V.comap b_x ⊆ X_x`.

* `isPullback_embeddedFiberι_pointMap`: the square of `b_x`, `ι_x`, `i_T` and
  `pointMap ι g x : P^N_K ⟶ P_T` is cartesian; no hypothesis on `i`.
* `comap_pointMap_map_immersionBaseChange`: for a preimmersion `i` and `V` closed in `P_T`, the
  fibre at `x` of the image `V.map i_T` is the image `V_x.map ι_x`
  (`Scheme.IdealSheafData.map_comap_of_isPullback`), and
  `subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange`: its Hilbert polynomial is
  the Hilbert polynomial of `ι_x* 𝒪_{V_x}` on `P^N_K` (`quotientModulePushforwardIso`).
* `eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange`: for a closed immersion
  `i` and `ι ≃ Fin (N + 1)`, the value at `n : ℤ` of this Hilbert polynomial is
  `χ(X_x, O(n)) − χ(X_x, I_{V_x}(n))`, for the ideal `I_{V_x}` of `V_x ⊆ X_x`: the sequence
  `0 → I_{V_x} → 𝒪_{X_x} → 𝒪_{V_x} → 0` stays exact on `P^N_K` under the closed pushforward,
  Hilbert polynomials are additive (`projectiveHilbertPolynomial_add_of_shortExact`), and the
  Euler characteristics on `X_x` are Hilbert functions on `P^N_K`
  (`embeddedFiberTwistEulerChar_eq_projectiveHilbertFunction`). No flatness is needed.
* For `V` flat over `T`: its image in `P_T` is flat over `T`
  (`flat_map_immersionBaseChange_subschemeι_comp_snd`); the ideal of `V_x` is the pullback
  `b_x^* I_V` (`fieldPointIdealPullbackIso`, from
  `Scheme.Hom.flatQuotient_idealPullbackMap_isIso`), so the value at `n` is
  `χ(X_x, O(n)) − χ(X_x, (b_x^* I_V)(n))`
  (`eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_of_flat`); and if
  `χ(X_x, O(n)) = ψ(n)` and `χ(X_x, (b_x^* I_V)(n)) = φ₀(n)` for every `n`, the Hilbert polynomial
  is `ψ − φ₀` (`subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_eq_sub`).

All statements are at a variable field `K`; residue fields enter by instantiation. For a relative
effective Cartier divisor `D ⊆ X_T` with `I_D ≅ L^{-1}` this is the computation behind Kleiman's
"Plainly `Z` lies in `Hilb^θ_{X/S}(n)`" (*The Picard scheme*, arXiv:math/0504020v1, proof of Thm
4.8, p. 30): the fibre `D_t` has Hilbert polynomial `θ = ψ − φ₀` when `χ(X_t, O(n)) = ψ(n)` and
`χ(X_t, L_t^{-1}(n)) = φ₀(n)`. Its consumer is `Picard/Strata/DivisorPolynomial`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Cohomology AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι)
  {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) {K : Type u} [Field K]
  (x : Spec (CommRingCat.of K) ⟶ T)

/-! ### The fibre of `X_T` at a field point inside `P^N_K` -/

/-- **The fibre of `X_T` at a field point is the base change of `i_T` along `pointMap ι g x`**: for
`x : Spec K ⟶ T`, the square formed by `b_x : X_x ⟶ X_T`, the fibre embedding `ι_x : X_x ⟶ P^N_K`,
`i_T : X_T ⟶ P_T` and `pointMap ι g x : P^N_K ⟶ P_T` is cartesian. -/
theorem isPullback_embeddedFiberι_pointMap :
    IsPullback (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _)
        (by simp) (by simp))
      (embeddedFiberι i (x ≫ g)) (immersionBaseChange i rfl g) (pointMap ι g x) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_immersionBaseChange i rfl g).flip
  · rw [pullback.lift_fst, Category.comp_id, pointMap_fst]
    exact isPullback_embeddedFiberι i (x ≫ g)
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, immersionBaseChange_fst, pointMap_fst,
        pullback.lift_fst_assoc, Category.comp_id]
      exact (embeddedFiberι_map i (x ≫ g)).symm
    · rw [Category.assoc, Category.assoc, immersionBaseChange_snd, pointMap_snd,
        embeddedFiberι_toSpec_assoc, pullback.lift_snd]

/-! ### The fibre of the image of a closed subscheme -/

section Image

variable [IsPreimmersion i] (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
  [IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i rfl g)]

/-- **The fibre of the image is the image of the fibre**: for a preimmersion `i`, a closed
subscheme `V ⊆ X_T` that is closed in `P_T` and a field point `x : Spec K ⟶ T`, the fibre at `x`
of the image of `V` in `P_T` is the image in `P^N_K` of the fibre `V_x ⊆ X_x`. -/
theorem comap_pointMap_map_immersionBaseChange :
    (V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x) =
      (V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _)
        (by simp) (by simp))).map (embeddedFiberι i (x ≫ g)) :=
  Scheme.IdealSheafData.map_comap_of_isPullback (isPullback_embeddedFiberι_pointMap i g x).flip V

omit [IsPreimmersion i] in
/-- The fibre `V_x ⊆ X_x` of a closed subscheme `V ⊆ X_T` that is closed in `P_T` is closed in
`P^N_K`. -/
theorem isClosedImmersion_comap_subschemeι_comp_embeddedFiberι :
    IsClosedImmersion ((V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X)
      x (𝟙 _) (by simp) (by simp))).subschemeι ≫ embeddedFiberι i (x ≫ g)) :=
  Scheme.IdealSheafData.isClosedImmersion_comap_subschemeι_comp_of_isPullback
    (isPullback_embeddedFiberι_pointMap i g x).flip V

/-- **The Hilbert polynomial of a fibre of the image**: it is the Hilbert polynomial on `P^N_K` of
the pushforward of the structure module of the fibre `V_x ⊆ X_x` along `ι_x : X_x ⟶ P^N_K`. -/
theorem subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange :
    subschemeHilbertPolynomial ι K
        ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x)) =
      projectiveHilbertPolynomial K ι ((Scheme.Modules.pushforward (embeddedFiberι i (x ≫ g))).obj
        (V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _)
          (by simp) (by simp))).quotientModule) := by
  have := isClosedImmersion_comap_subschemeι_comp_embeddedFiberι i g x V
  rw [comap_pointMap_map_immersionBaseChange i g x V]
  exact (projectiveHilbertPolynomial_congr K ι
    (Scheme.IdealSheafData.quotientModulePushforwardIso _ (embeddedFiberι i (x ≫ g)))).symm

end Image

/-! ### The Hilbert polynomial of a fibre as a difference of Euler characteristics -/

/-- **The Hilbert polynomial of a fibre is a difference of Euler characteristics**: for a closed
immersion `i`, `ι ≃ Fin (N + 1)`, a closed subscheme `V ⊆ X_T` and a field point
`x : Spec K ⟶ T`, the Hilbert polynomial of the fibre at `x` of the image of `V` in `P_T` takes
the value `χ(X_x, O(n)) − χ(X_x, I_{V_x}(n))` at `n`, for the ideal `I_{V_x}` of the fibre
`V_x ⊆ X_x`. -/
theorem eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange
    [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1))
    (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData) (n : ℤ) :
    (subschemeHilbertPolynomial ι K
        ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x))).eval (n : ℚ) =
      (embeddedFiberTwistEulerChar i (x ≫ g) (SheafOfModules.unit _) n : ℚ) -
        embeddedFiberTwistEulerChar i (x ≫ g)
          (Scheme.Hom.idealModule (V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g)
            (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _) (by simp) (by simp))).subschemeι) n := by
  have : Finite ι := Finite.of_equiv _ e.symm
  let W := V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _)
    (by simp) (by simp))
  have : IsLocallyNoetherian (pullback (i ≫ toSpec A ι) (x ≫ g)) :=
    LocallyOfFiniteType.isLocallyNoetherian (embeddedFiberι i (x ≫ g))
  have hO : affineLocallyFiniteType (pullback (i ≫ toSpec A ι) (x ≫ g))
      (SheafOfModules.unit (pullback (i ≫ toSpec A ι) (x ≫ g)).ringCatSheaf) :=
    Scheme.Modules.affineLocallyFiniteType_unit _
  have hI : affineLocallyFiniteType (pullback (i ≫ toSpec A ι) (x ≫ g))
      (Scheme.Hom.idealModule W.subschemeι) :=
    Scheme.Hom.affineLocallyFiniteType_idealModule _
  have hQ : affineLocallyFiniteType (pullback (i ≫ toSpec A ι) (x ≫ g)) W.quotientModule :=
    W.affineLocallyFiniteType_quotientModule
  have hO' := affineLocallyFiniteType_pushforward_embeddedFiberι i (x ≫ g) hO
  have hI' := affineLocallyFiniteType_pushforward_embeddedFiberι i (x ≫ g) hI
  have hadd := projectiveHilbertPolynomial_add_of_shortExact K ι N e _
    (Scheme.Modules.shortExact_pushforward_of_closedImmersion (embeddedFiberι i (x ≫ g))
      W.shortComplex_shortExact) hI' hO'
    (affineLocallyFiniteType_pushforward_embeddedFiberι i (x ≫ g) hQ)
  have h3 : projectiveHilbertPolynomial K ι
        ((Scheme.Modules.pushforward (embeddedFiberι i (x ≫ g))).obj W.quotientModule) =
      projectiveHilbertPolynomial K ι ((Scheme.Modules.pushforward (embeddedFiberι i (x ≫ g))).obj
          (SheafOfModules.unit (pullback (i ≫ toSpec A ι) (x ≫ g)).ringCatSheaf)) -
        projectiveHilbertPolynomial K ι ((Scheme.Modules.pushforward
          (embeddedFiberι i (x ≫ g))).obj (Scheme.Hom.idealModule W.subschemeι)) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hadd.symm
  rw [subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange i g x V, h3,
    Polynomial.eval_sub, ← projectiveHilbertFunction_eq_eval K ι N e _ hO' n,
    ← projectiveHilbertFunction_eq_eval K ι N e _ hI' n,
    ← embeddedFiberTwistEulerChar_eq_projectiveHilbertFunction i (x ≫ g) _ hO n,
    ← embeddedFiberTwistEulerChar_eq_projectiveHilbertFunction i (x ≫ g) _ hI n]

/-! ### Flat families -/

/-- **The image of a flat closed subscheme is flat**: for `i : X ⟶ P^N_A` over `Spec A`
(`hi : i ≫ toSpec A ι = πX`), a closed subscheme `V ⊆ X_T` that is closed in `P_T` and flat over
`T` has image in `P_T` flat over `T`: the image is isomorphic to `V` over `P_T`
(`Scheme.IdealSheafData.mapSubschemeIso`). -/
theorem flat_map_immersionBaseChange_subschemeι_comp_snd {πX : X ⟶ Spec (CommRingCat.of A)}
    (hi : i ≫ toSpec A ι = πX) (V : (pullback πX g).IdealSheafData)
    [IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i hi g)]
    [Flat (V.subschemeι ≫ pullback.snd πX g)] :
    Flat ((V.map (immersionBaseChange i hi g)).subschemeι ≫ pullback.snd (toSpec A ι) g) := by
  rw [← Iso.inv_hom_id_assoc (V.mapSubschemeIso (immersionBaseChange i hi g))
    (V.map (immersionBaseChange i hi g)).subschemeι,
    Scheme.IdealSheafData.mapSubschemeIso_hom_subschemeι, Category.assoc, Category.assoc,
    immersionBaseChange_snd]
  infer_instance

section Flat

variable (V : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
  [Flat (V.subschemeι ≫ pullback.snd (i ≫ toSpec A ι) g)]

/-- **The fibre of the ideal of a flat family**: for a closed subscheme `V ⊆ X_T` flat over `T` and
a field point `x : Spec K ⟶ T`, the canonical map from the pullback of `I_V` along
`b_x : X_x ⟶ X_T` to the ideal module of the fibre `V_x = V.comap b_x` is an isomorphism
(`Scheme.Hom.flatQuotient_idealPullbackMap_isIso` on the cartesian square
`Scheme.isPullback_pullbackMap_snd`). -/
theorem isIso_idealPullbackMap_fieldPoint :
    IsIso (Scheme.Hom.idealPullbackMap V.subschemeι
      (V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _)
        (by simp) (by simp))).subschemeι
      (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _)
        (by simp) (by simp))
      (Scheme.IdealSheafData.subschemeMap _ V _ (V.le_map_comap _))
      (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _)) :=
  Scheme.Hom.flatQuotient_idealPullbackMap_isIso (pullback.snd (i ≫ toSpec A ι) g) x
    (pullback.snd (i ≫ toSpec A ι) (x ≫ g)) _ V.subschemeι _ _ _
    (Scheme.isPullback_pullbackMap_snd (i ≫ toSpec A ι) g (x ≫ g) x rfl)
    (V.isPullback_subschemeMap_comap _)

/-- The isomorphism `b_x^* I_V ≅ I_{V_x}` of `isIso_idealPullbackMap_fieldPoint`. -/
def fieldPointIdealPullbackIso :
    (Scheme.Modules.pullback (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x
        (𝟙 _) (by simp) (by simp))).obj (Scheme.Hom.idealModule V.subschemeι) ≅
      Scheme.Hom.idealModule (V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g
        (𝟙 X) x (𝟙 _) (by simp) (by simp))).subschemeι :=
  haveI := isIso_idealPullbackMap_fieldPoint i g x V
  asIso (Scheme.Hom.idealPullbackMap V.subschemeι
    (V.comap (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _)
      (by simp) (by simp))).subschemeι
    (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g (𝟙 X) x (𝟙 _) (by simp) (by simp))
    (Scheme.IdealSheafData.subschemeMap _ V _ (V.le_map_comap _))
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _))

/-- **The Hilbert polynomial of a fibre of a flat family**: for a closed immersion `i`,
`ι ≃ Fin (N + 1)`, a closed subscheme `V ⊆ X_T` flat over `T` and a field point `x`, the Hilbert
polynomial of the fibre at `x` of the image of `V` in `P_T` takes the value
`χ(X_x, O(n)) − χ(X_x, (b_x^* I_V)(n))` at `n`. -/
theorem eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_of_flat
    [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1)) (n : ℤ) :
    (subschemeHilbertPolynomial ι K
        ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x))).eval (n : ℚ) =
      (embeddedFiberTwistEulerChar i (x ≫ g) (SheafOfModules.unit _) n : ℚ) -
        embeddedFiberTwistEulerChar i (x ≫ g)
          ((Scheme.Modules.pullback (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g
            (𝟙 X) x (𝟙 _) (by simp) (by simp))).obj (Scheme.Hom.idealModule V.subschemeι)) n := by
  rw [eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange i g x N e V n,
    embeddedFiberTwistEulerChar_congr i (x ≫ g) (fieldPointIdealPullbackIso i g x V) n]

/-- **The Hilbert polynomial of a fibre of a flat family is `ψ − φ₀`**: if at the field point `x`
`χ(X_x, O(n)) = ψ(n)` and `χ(X_x, (b_x^* I_V)(n)) = φ₀(n)` for every `n : ℤ`, then the fibre at
`x` of the image of `V` in `P_T` has Hilbert polynomial `ψ − φ₀`. -/
theorem subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_eq_sub
    [IsClosedImmersion i] (N : ℕ) (e : ι ≃ Fin (N + 1)) {ψ φ₀ : ℚ[X]}
    (hψ : ∀ n : ℤ,
      (embeddedFiberTwistEulerChar i (x ≫ g) (SheafOfModules.unit _) n : ℚ) = ψ.eval (n : ℚ))
    (hφ₀ : ∀ n : ℤ, (embeddedFiberTwistEulerChar i (x ≫ g)
      ((Scheme.Modules.pullback (pullback.map (i ≫ toSpec A ι) (x ≫ g) (i ≫ toSpec A ι) g
        (𝟙 X) x (𝟙 _) (by simp) (by simp))).obj (Scheme.Hom.idealModule V.subschemeι)) n : ℚ) =
          φ₀.eval (n : ℚ)) :
    subschemeHilbertPolynomial ι K
      ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x)) = ψ - φ₀ := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (n : ℚ)) Int.cast_injective
  intro n
  change (subschemeHilbertPolynomial ι K
    ((V.map (immersionBaseChange i rfl g)).comap (pointMap ι g x))).eval (n : ℚ) =
      (ψ - φ₀).eval (n : ℚ)
  rw [eval_subschemeHilbertPolynomial_comap_pointMap_map_immersionBaseChange_of_flat i g x V N e n,
    hψ n, hφ₀ n, Polynomial.eval_sub]

end Flat

end AlgebraicGeometry.ProjectiveSpace
