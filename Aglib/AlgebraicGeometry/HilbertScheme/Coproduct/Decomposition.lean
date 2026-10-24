/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.FlatteningStratum
public import Aglib.AlgebraicGeometry.IdealSheaf.GlueCoproduct
public import Aglib.AlgebraicGeometry.FlatteningStratification.FlatDecomposition

/-!
# The clopen decomposition of a flat family of closed subschemes by fibre Hilbert polynomial

Let `A` be a ring, `ι ≃ Fin (n + 1)`, `g : T ⟶ Spec A` and `V ⊆ P^n_A ×_{Spec A} T` a closed
subscheme (`V : (pullback (toSpec A ι) g).IdealSheafData`; it is proper over `T`). Write
`P_t = fiberHilbertPolynomialAt ι g 𝒪_V t` for the fibre Hilbert polynomial at `t ∈ T`, and
`T_Φ = flatteningStratum ι g n e hV Φ` for the flattening strata of `𝒪_V`
(`FlatteningStratification/Global`; `hV` is the coherence of `𝒪_V`, which holds for every `V` by
`IdealSheafData.affineLocallyFiniteType_quotientModule`).

* **Restriction** (Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1,
  p. 4: a flat family with fibre polynomial `Φ` is a point of `Quot^Φ`):
  - `ProjectiveSpace.isHilbertFamily_comap_pullbackBaseChange_of_flat`: if `V` is flat over `T`
    and `f : T' ⟶ T` has `P_{f t'} = Φ` for all `t'`, then the pullback `V_{T'}` is a point of
    `Hilb^Φ(T')`; no Noetherian hypothesis. For `f` the inclusion of the open subscheme
    `{P_t = Φ}`, this is the restriction of `V` to `T_Φ`.
  - `ProjectiveSpace.isHilbertFamily_comap_flatteningStratumι`: for locally Noetherian `T` and any
    `V`, flat or not, the restriction of `V` to the stratum `T_Φ` is a point of `Hilb^Φ(T_Φ)`
    (property (F) of Nitsure, §5, p. 26, `exists_lift_flatteningStratumι_iff_isHilbertFamily`).
* **Decomposition** (Nitsure, proof of Thm 4.3 (ii), p. 22, "the open and closed subscheme of T
  where the Hilbert polynomial is f"), for locally Noetherian `T` and `V` flat over `T`:
  - `ProjectiveSpace.isOpenImmersion_flatteningStratumι_of_flat`: every `T_Φ ⟶ T` is an open
    immersion onto `{t | P_t = Φ}`;
  - `ProjectiveSpace.isClopen_setOf_fiberHilbertPolynomialAt_quotientModule_eq_of_flat`:
    `{t | P_t = Φ}` is open and closed;
  - `ProjectiveSpace.isIso_sigmaDesc_flatteningStratumι_of_flat`: `∐_j T_{φ j} ⟶ T` is an
    isomorphism for any injective `φ : J → ℚ[X]` whose range contains every `P_t`, such as a
    finite set of polynomials containing them.
* **Fibre polynomials under base change**, for finitely many coordinates and any `V`:
  `ProjectiveSpace.fiberHilbertPolynomialAt_quotientModule_comap_baseChangeMap`: the fibre
  polynomial of the pullback of `V` along `baseChangeMap ι g g' f h` at `t'` is `P_{f t'}`
  (module form: `ProjectiveSpace.fiberHilbertPolynomialAt_pullback_baseChangeMap`).
* **The glued family over a disjoint union of bases** (`IdealSheaf/GlueCoproduct`, for
  `Z = P^n_A`): `ProjectiveSpace.pullbackSigmaι_toSpec_eq_baseChangeMap` identifies the component
  maps with the Hilbert-functor base change, and
  `ProjectiveSpace.fiberHilbertPolynomialAt_sigmaGlue_sigmaι` (with the form
  `_of_isHilbertFamily`) computes the fibre polynomial of the glued family at a point of the `j`-th
  component as that of `D j`; for points `D j ∈ Hilb^{Φ j}(H j)` it is `Φ j`, and for distinct
  `Φ j` the pullback along `a : T ⟶ ∐ H` has fibre polynomial `Φ j` exactly over `a⁻¹(H j)`
  (`ProjectiveSpace.fiberHilbertPolynomialAt_sigmaGlue_comap_eq_iff`).

Morphisms out of `T` are then assembled and compared on the strata by `flatteningDecompositionIso`
and `hom_ext_of_flatteningStratumι_of_relativeFlat` (`FlatteningStratification/FlatDecomposition`);
closed subschemes of `Z ×_S T` are compared on the pieces by
`IdealSheafData.ext_of_comap_pullbackMap_eq` (`IdealSheaf/GlueCoproduct`).

These are the decomposition and restriction steps for the finite union of Hilbert schemes in
Nitsure's proof of Thm 6.8, p. 33 ("As the parameter scheme X is noetherian and as the Hilbert
polynomial is locally constant, only finitely many polynomials Φ occur"; for quasi-compact `T`,
see `finite_range_fiberHilbertPolynomialAt`). Present consumer: the Hilbert scheme
`∐_{Φ ∈ F} Hilb^Φ` of the F16 quotient (plan task HQ10).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Cohomology

variable {A : Type u} [CommRing A] (ι : Type u) {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
  (V : (pullback (toSpec A ι) g).IdealSheafData)

/-- **A flat family with constant fibre polynomial along `f` pulls back to a point of `Hilb^Φ`**
(Nitsure, arXiv:math/0504590v1, §1, p. 4): for finitely many coordinates, if `V` is flat over `T`
and every fibre Hilbert polynomial `P_{f t'}` of `𝒪_V` at the image of a point of `T'` is `Φ`, then
`V.comap (pullbackBaseChange ι g f)` is a point of `Hilb^Φ(T')`. No Noetherian hypothesis: flatness
passes to the base change and the fibre polynomials are those at the image points
(`fiberHilbertPolynomialAt_pullbackBaseChange`). -/
theorem isHilbertFamily_comap_pullbackBaseChange_of_flat [Finite ι]
    (hflat : Flat (V.subschemeι ≫ pullback.snd (toSpec A ι) g)) {T' : Scheme.{u}} (f : T' ⟶ T)
    {Φ : ℚ[X]} (hf : ∀ t' : T', fiberHilbertPolynomialAt ι g V.quotientModule (f t') = Φ) :
    IsHilbertFamily ι Φ (f ≫ g) (V.comap (pullbackBaseChange ι g f)) := by
  have := V.quotientModule_isQuasicoherent
  refine (isHilbertFamily_comap_pullbackBaseChange_iff ι g V f Φ).mpr ⟨?_, fun t' => ?_⟩
  · exact relativeFlat_pullback_of_isPullback (isPullback_pullbackBaseChange ι g f)
      V.quotientModule ((V.relativeFlat_quotientModule_iff_flat _).mpr hflat)
  · rw [fiberHilbertPolynomialAt_pullbackBaseChange]
    exact hf t'

section Stratum

variable [IsLocallyNoetherian T] (n : ℕ) (e : ι ≃ Fin (n + 1))
  (hV : affineLocallyFiniteType (pullback (toSpec A ι) g) V.quotientModule)

/-- **The restriction of a family to a flattening stratum is a point of the Hilbert functor**
(Nitsure, arXiv:math/0504590v1, §5, property (F), p. 26, with `E = O_X`): for locally Noetherian
`T` and any closed subscheme `V ⊆ P^n_A ×_{Spec A} T`, flat or not, the pullback of `V` to the
stratum `T_Φ` is a point of `Hilb^Φ(T_Φ)`. -/
theorem isHilbertFamily_comap_flatteningStratumι (Φ : ℚ[X]) :
    IsHilbertFamily ι Φ (flatteningStratumι ι g n e hV Φ ≫ g)
      (V.comap (pullbackBaseChange ι g (flatteningStratumι ι g n e hV Φ))) :=
  (exists_lift_flatteningStratumι_iff_isHilbertFamily ι g V n e hV Φ
    (flatteningStratumι ι g n e hV Φ)).mp ⟨𝟙 _, Category.id_comp _⟩

variable {V} (hflat : Flat (V.subschemeι ≫ pullback.snd (toSpec A ι) g))

include hflat in
/-- **The strata of a flat family of closed subschemes are open immersions**: for locally
Noetherian `T` and `V` flat over `T`, every `T_Φ ⟶ T` is an open immersion onto
`{t | P_t = Φ}`. -/
theorem isOpenImmersion_flatteningStratumι_of_flat (Φ : ℚ[X]) :
    IsOpenImmersion (flatteningStratumι ι g n e hV Φ) :=
  isOpenImmersion_flatteningStratumι_of_relativeFlat ι g n e hV
    ((V.relativeFlat_quotientModule_iff_flat _).mpr hflat) Φ

include e hV hflat in
/-- **The fibre Hilbert polynomial of a flat family of closed subschemes is locally constant**
(Nitsure, arXiv:math/0504590v1, §1, p. 4, and proof of Thm 4.3 (ii), p. 22): for locally
Noetherian `T` and `V` flat over `T`, the set `{t | P_t = Φ}` is open and closed in `T`. -/
theorem isClopen_setOf_fiberHilbertPolynomialAt_quotientModule_eq_of_flat (Φ : ℚ[X]) :
    IsClopen {t | fiberHilbertPolynomialAt ι g V.quotientModule t = Φ} :=
  isClopen_setOf_fiberHilbertPolynomialAt_eq_of_relativeFlat ι g n e hV
    ((V.relativeFlat_quotientModule_iff_flat _).mpr hflat) Φ

include hflat in
/-- **Clopen decomposition of a flat family of closed subschemes by fibre Hilbert polynomial**
(Nitsure, arXiv:math/0504590v1, §1, p. 4, "Quot naturally decomposes as a co-product", and proof
of Thm 4.3 (ii), p. 22): for locally Noetherian `T`, `V ⊆ P^n_A ×_{Spec A} T` flat over `T` and an
injective `φ : J → ℚ[X]` whose range contains every fibre Hilbert polynomial of `V`, the strata
give an isomorphism `∐_j T_{φ j} ⟶ T`. -/
theorem isIso_sigmaDesc_flatteningStratumι_of_flat {J : Type*} [Small.{u} J]
    (φ : J → ℚ[X]) (hφ : Function.Injective φ)
    (hP : ∀ t, fiberHilbertPolynomialAt ι g V.quotientModule t ∈ Set.range φ) :
    IsIso (Sigma.desc fun j => flatteningStratumι ι g n e hV (φ j)) :=
  isIso_sigmaDesc_flatteningStratumι_of_relativeFlat ι g n e hV
    ((V.relativeFlat_quotientModule_iff_flat _).mpr hflat) φ hφ hP

end Stratum

section BaseChange

variable [Finite ι] {T' : Scheme.{u}} (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
  (h : f ≫ g = g')

/-- **Fibre polynomials of a base change of a module**: for finitely many coordinates, a
quasi-coherent `F` on `P^n_A ×_{Spec A} T` and `f : T' ⟶ T` over `Spec A`, the fibre Hilbert
polynomial of the pullback of `F` along `baseChangeMap ι g g' f h` at `t'` is that of `F` at
`f t'` (`fiberHilbertPolynomialAt_pullbackBaseChange`, for any structure morphism `g'`). -/
theorem fiberHilbertPolynomialAt_pullback_baseChangeMap
    (F : (pullback (toSpec A ι) g).Modules) [F.IsQuasicoherent] (t' : T') :
    fiberHilbertPolynomialAt ι g'
        ((Scheme.Modules.pullback (baseChangeMap ι g g' f h)).obj F) t' =
      fiberHilbertPolynomialAt ι g F (f t') := by
  subst h
  exact fiberHilbertPolynomialAt_pullbackBaseChange ι g F f t'

/-- **Fibre polynomials of a pulled-back family**: for finitely many coordinates, a closed
subscheme `V ⊆ P^n_A ×_{Spec A} T` (flat or not) and `f : T' ⟶ T` over `Spec A`, the fibre
Hilbert polynomial of `V.comap (baseChangeMap ι g g' f h)` at `t'` is that of `V` at `f t'`. -/
theorem fiberHilbertPolynomialAt_quotientModule_comap_baseChangeMap (t' : T') :
    fiberHilbertPolynomialAt ι g' (V.comap (baseChangeMap ι g g' f h)).quotientModule t' =
      fiberHilbertPolynomialAt ι g V.quotientModule (f t') := by
  have := V.quotientModule_isQuasicoherent
  rw [fiberHilbertPolynomialAt_congr ι g'
    (V.quotientModulePullbackIso (baseChangeMap ι g g' f h)).symm t']
  exact fiberHilbertPolynomialAt_pullback_baseChangeMap ι g' f h V.quotientModule t'

end BaseChange

section Sigma

variable {J : Type*} [Small.{u} J] {H : J → Scheme.{u}}
  (πH : ∀ j, H j ⟶ Spec (CommRingCat.of A))

/-- The component map `P^n_A ×_{Spec A} H j ⟶ P^n_A ×_{Spec A} ∐ H` of
`HilbertScheme/Coproduct/Family` is the Hilbert-functor base change along `Sigma.ι H j`. -/
theorem pullbackSigmaι_toSpec_eq_baseChangeMap (j : J) :
    Scheme.pullbackSigmaι (toSpec A ι) πH j =
      baseChangeMap ι (Sigma.desc πH) (πH j) (Sigma.ι H j) (Sigma.ι_comp_desc _ _) := by
  apply pullback.hom_ext
  · rw [Scheme.pullbackSigmaι_fst, baseChangeMap_fst]
  · rw [Scheme.pullbackSigmaι_snd, baseChangeMap_snd]

variable [Finite ι] (D : ∀ j, (pullback (toSpec A ι) (πH j)).IdealSheafData)

/-- **The fibre polynomials of the glued family**: for finitely many coordinates and families
`D j ⊆ P^n_A ×_{Spec A} H j`, the fibre Hilbert polynomial of the glued family
`sigmaGlue (toSpec A ι) πH D` at the image of `y ∈ H j` is that of `D j` at `y`. -/
theorem fiberHilbertPolynomialAt_sigmaGlue_sigmaι (j : J) (y : H j) :
    fiberHilbertPolynomialAt ι (Sigma.desc πH)
        (Scheme.IdealSheafData.sigmaGlue (toSpec A ι) πH D).quotientModule (Sigma.ι H j y) =
      fiberHilbertPolynomialAt ι (πH j) (D j).quotientModule y := by
  rw [← fiberHilbertPolynomialAt_quotientModule_comap_baseChangeMap ι _ (πH j) (Sigma.ι H j)
    (Sigma.ι_comp_desc _ _) y, ← pullbackSigmaι_toSpec_eq_baseChangeMap,
    Scheme.IdealSheafData.comap_sigmaGlue]

/-- **The glued family of Hilbert families has the given polynomial on each component**: if
`D j` is a point of `Hilb^{Φ j}(H j)` for every `j`, the fibre Hilbert polynomial of the glued
family at a point of the `j`-th component is `Φ j`. -/
theorem fiberHilbertPolynomialAt_sigmaGlue_sigmaι_of_isHilbertFamily (Φ : J → ℚ[X])
    (hD : ∀ j, IsHilbertFamily ι (Φ j) (πH j) (D j)) (j : J) (y : H j) :
    fiberHilbertPolynomialAt ι (Sigma.desc πH)
        (Scheme.IdealSheafData.sigmaGlue (toSpec A ι) πH D).quotientModule (Sigma.ι H j y) =
      Φ j :=
  (fiberHilbertPolynomialAt_sigmaGlue_sigmaι ι πH D j y).trans
    ((hD j).fiberHilbertPolynomialAt_quotientModule_eq ι y)

/-- **The pullback of the glued family along a morphism into `∐ H` detects the component**: if
`D j` is a point of `Hilb^{Φ j}(H j)` for every `j` and the `Φ j` are distinct, then for
`a : T ⟶ ∐ H` over `Spec A` the fibre Hilbert polynomial of the pullback of the glued family
along `a` is `Φ j` at `t` exactly when `a t` lies in the `j`-th component. So `a⁻¹(H j)` is the
locus `{t | P_t = Φ j}` of the pulled-back family. -/
theorem fiberHilbertPolynomialAt_sigmaGlue_comap_eq_iff (Φ : J → ℚ[X])
    (hΦ : Function.Injective Φ) (hD : ∀ j, IsHilbertFamily ι (Φ j) (πH j) (D j))
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T ⟶ ∐ H)
    (ha : a ≫ Sigma.desc πH = g) (t : T) (j : J) :
    fiberHilbertPolynomialAt ι g ((Scheme.IdealSheafData.sigmaGlue (toSpec A ι) πH D).comap
        (baseChangeMap ι (Sigma.desc πH) g a ha)).quotientModule t = Φ j ↔
      a t ∈ Set.range (Sigma.ι H j) := by
  rw [fiberHilbertPolynomialAt_quotientModule_comap_baseChangeMap]
  obtain ⟨i, y, hy⟩ := Scheme.exists_sigmaι_eq (a t)
  rw [← hy, fiberHilbertPolynomialAt_sigmaGlue_sigmaι_of_isHilbertFamily ι πH D Φ hD i y]
  constructor
  · intro h
    obtain rfl := hΦ h
    exact ⟨y, rfl⟩
  · rintro ⟨y', hy'⟩
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp ((sigmaι_eq_iff H j i y' y).mp hy')
    rfl

end Sigma

end AlgebraicGeometry.ProjectiveSpace
