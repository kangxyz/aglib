/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardScheme
public import Aglib.AlgebraicGeometry.Curves.Jacobian.RationalPoints
public import Aglib.AlgebraicGeometry.Curves.LineBundleDegree.Isomorphism
public import Aglib.AlgebraicGeometry.Curves.Picard.NormDegree.OrderFormula
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Noetherian
public import Aglib.AlgebraicGeometry.Picard.Strata.Conditions

/-!
# The Hilbert-polynomial strata of the Picard scheme of a curve are the degree strata

Let `k` be a field, `i : X ⟶ P^N_k = ProjectiveSpace k ι` a closed immersion such that `X`, as a
scheme over `k` through `p = i ≫ toSpec k ι`, is a smooth proper geometrically connected curve
(`Curve.Properties (Over.mk p)`), `g` its genus and `deg O(1)` the degree of `i^* O(1)`. Let `P`
represent `Pic_{X/k,(fppf)}` on locally Noetherian test schemes through `R`, and let the stratum of
`φ ∈ ℚ[t]` be the open and closed set of points of `P` where the universal section satisfies
Kleiman's condition (4.8.1), `χ(X_t, L_t^{-1}(n)) = φ(n)` for all `n`
(`Strata.eulerCondition`; for the Picard scheme these are `picardStratumOpens`).

* `moduleEulerChar_eq_curveDegree_add_one_sub_genus`: **Riemann–Roch** in Euler-characteristic
  form, `χ(X, L) = deg L + 1 - g` for every line bundle `L` on a curve, from
  `Curve.lineBundleRiemannRoch` and Grothendieck vanishing of `H^q` for `q ≥ 2`.
* `fiberDualTwistEulerChar_closedPoint`: at the rational point of `Spec k`, the fibre invariant
  of (4.8.1) is the Euler characteristic of `O(n) ⊗ L^{-1}` on `X ×_k k` (cohomology commutes with
  the residue-field extension, `embeddedFiberTwistDim_pullbackMap_of_eq`).
* `picardPoint_mem_opens_eulerCondition_iff_eval`: **the strata are the degree strata** (Stacks,
  Picard Schemes of Curves, Lemma 6.7, Tag 0BA0, proof, "decomposition by `χ`"): the rational
  point of `P` of a class `c` on `X` lies in the stratum of `φ` if and only if
  `φ(n) = n · deg O(1) + 1 - g - deg c` for all `n`. So the rational point of a class `c` lies in
  the stratum of `degreeStratumPolynomial i hX d = (m ↦ m · deg O(1) + 1 - g - d)` if and only if
  `deg c = d` (`picardPoint_mem_opens_eulerCondition_degreeStratumPolynomial_iff`); the sign of
  `d` reflects Kleiman's use of `L^{-1}` in (4.8.1). Points of `P` that are not of the form
  `picardPoint P R c` are not described here.
* Each of these strata is open and closed
  (`isClopen_opens_eulerCondition_degreeStratumPolynomial`), and the degree-zero stratum contains
  the unit point (`unitPoint_mem_opens_eulerCondition_degreeStratumPolynomial_zero`): with the
  previous item, these are the hypotheses on `Z` of [IdentityComponent](IdentityComponent.lean).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Cohomology AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata

namespace AlgebraicGeometry.Scheme.OverField.Curve

section RiemannRoch

variable {k : Type u} [Field k] (X : FScheme k) (hX : Properties X)

-- The module structure of `moduleCohomology` is found through the structure sheaf of `X.left`.
set_option backward.isDefEq.respectTransparency false in
/-- The dimension of `H^q(X, M)` for the structural action of `X ⟶ Spec k` is the `finrank` of
`moduleCohomology`; the two actions agree by `moduleCohomologyModuleOfHom_constants`, used here so
that the kernel does not unfold both module structures again. -/
theorem moduleCohomologyDimension_eq_finrank_moduleCohomology (M : X.left.Modules) (q : ℕ) :
    moduleCohomologyDimension X.hom M q = Module.finrank k (moduleCohomology k X M q) :=
  congrArg (fun inst => @Module.finrank k (moduleCohomology k X M q) _ _ inst)
    (moduleCohomologyModuleOfHom_constants X M q)

-- The module structure of `moduleCohomology` is found through the structure sheaf of `X.left`.
set_option backward.isDefEq.respectTransparency false in
include hX in
/-- **The cohomology of a line bundle on a curve vanishes above degree one** (Grothendieck
vanishing, `noetherianSheafCohomology_vanishing`, for the Noetherian one-dimensional `X`). -/
theorem moduleCohomologyDimension_eq_zero_of_two_le (L : LineBundle X.left) {q : ℕ}
    (hq : 2 ≤ q) : moduleCohomologyDimension X.hom L.val q = 0 := by
  have := curveProperties_isNoetherian hX
  have : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X.left L.val) q) :=
    noetherianSheafCohomology_vanishing X.left _ 1 q
      (by rw [hX.topologicalKrullDim_eq_one]; rfl) (by omega)
  rw [moduleCohomologyDimension_eq_finrank_moduleCohomology]
  exact Module.finrank_zero_of_subsingleton

-- The module structure of `moduleCohomology` is found through the structure sheaf of `X.left`.
set_option backward.isDefEq.respectTransparency false in
/-- **Riemann–Roch in Euler-characteristic form**: `χ(X, L) = deg L + 1 - g` for a line bundle `L`
on a smooth proper geometrically connected curve (`curveLineBundle_riemannRoch` with
`Curve.lineBundleRiemannRoch`, and `H^q(X, L) = 0` for `q ≥ 2`). -/
theorem moduleEulerChar_eq_curveDegree_add_one_sub_genus (L : LineBundle X.left) :
    moduleEulerChar X.hom L.val =
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX (classOf X.left L) + 1 - coherentGenus k X := by
  have hRR := curveLineBundle_riemannRoch smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension
    Picard.Degree.properCurveProductFormula lineBundleRiemannRoch X hX L
  change ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * (moduleCohomologyDimension X.hom L.val q : ℤ) = _
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 2)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      one_mul, neg_one_mul, moduleCohomologyDimension_eq_finrank_moduleCohomology]
    linarith
  · intro q hq
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hq
    have h0 := moduleCohomologyDimension_eq_zero_of_two_le X hX L (q := q) (by omega)
    simp only [h0, Nat.cast_zero, mul_zero]

end RiemannRoch

section RationalFiber

variable {k : Type u} [Field k] {ι : Type u} {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace k ι)
  [IsClosedImmersion i] {N : ℕ} (e : ι ≃ Fin (N + 1))

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances (as in
-- `familyScheme_map_fst`).
set_option backward.isDefEq.respectTransparency false in
include e in
/-- **The fibre invariant of (4.8.1) at the rational point of `Spec k`**: for a line bundle `L` on
`X ×_k k`, `χ(X_t, L_t^{-1}(n))` at the point `t` of `Spec k` is the Euler characteristic of
`O(n) ⊗ L^{-1}` on `X ×_k k`, since cohomology commutes with the extension `k → κ(t)`
(`embeddedFiberTwistDim_pullbackMap_of_eq`). -/
theorem fiberDualTwistEulerChar_closedPoint
    (L : LineBundle (pullback (i ≫ toSpec k ι) (𝟙 (Spec (.of k))))) (n : ℤ) :
    fiberDualTwistEulerChar i (𝟙 (Spec (.of k))) L (IsLocalRing.closedPoint k) n =
      moduleEulerChar (pullback.snd (i ≫ toSpec k ι) (𝟙 (Spec (.of k))))
        (pulledTwistLineBundle i (𝟙 (Spec (.of k))) n (dualLineBundle _ L)).val := by
  have : IsProper (i ≫ toSpec k ι) := isProper_comp_toSpec_of_isClosedImmersion i e
  have : (pulledTwist (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k))) ≫ i) n
      (dualLineBundle _ L).val).IsQuasicoherent :=
    lineBundle_isQuasicoherent ⟨_, isLocallyRankOne_pulledTwist _ n (dualLineBundle _ L).property⟩
  have hk : Spec.map (Spec.preimage ((Spec (.of k)).fromSpecResidueField
      (IsLocalRing.closedPoint k))) ≫ 𝟙 (Spec (.of k)) =
        (Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k) ≫ 𝟙 _ := by
    rw [Spec.map_preimage]
  have hmap : residueFieldBaseChange (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))
      (IsLocalRing.closedPoint k) =
      pullback.map (i ≫ toSpec k ι)
        ((Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k) ≫ 𝟙 _)
        (i ≫ toSpec k ι) (𝟙 _) (𝟙 Y)
        (Spec.map (Spec.preimage ((Spec (.of k)).fromSpecResidueField
          (IsLocalRing.closedPoint k)))) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [pullback.map, Spec.map_preimage]
  change embeddedFiberTwistEulerChar i
      (K := (Spec (.of k)).residueField (IsLocalRing.closedPoint k))
      ((Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k) ≫ 𝟙 _) _ n =
    embeddedFiberTwistEulerChar i (𝟙 (Spec (.of k))) (dualLineBundle _ L).val n
  rw [embeddedFiberTwistEulerChar_eq, embeddedFiberTwistEulerChar_eq]
  congr 1
  funext q
  congr 2
  refine (embeddedFiberTwistDim_congr i _
    ((Scheme.Modules.pullbackCongr hmap).app (dualLineBundle _ L).val) n q).trans ?_
  exact embeddedFiberTwistDim_pullbackMap_of_eq i (𝟙 (Spec (.of k)))
    (Spec.preimage ((Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k))) _ hk
    (dualLineBundle _ L).val n q

/-- The curve `X ×_k k` over `k`, isomorphic to `X`. -/
abbrev rationalFiber : FScheme k :=
  Over.mk (pullback.snd (i ≫ toSpec k ι) (𝟙 (Spec (.of k))))

/-- `X ×_k k ≅ X` over `k`, by the first projection. -/
def rationalFiberIso : rationalFiber i ≅ (Over.mk (i ≫ toSpec k ι) : FScheme k) :=
  Over.isoMk (asIso (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))))
    (by simp [pullback.condition])

variable (hX : Properties (Over.mk (i ≫ toSpec k ι) : FScheme k))

omit [IsClosedImmersion i] in
include hX in
/-- `X ×_k k` is a curve. -/
theorem properties_rationalFiber : Properties (rationalFiber i) :=
  curveProperties_baseChange hX k (𝟙 _)

omit [IsClosedImmersion i] in
/-- **The Hilbert polynomial of the degree-`d` stratum**, `m ↦ m · deg O(1) + 1 - g - d`, for
`O(1) = i^* O_{P^N}(1)` and `g` the genus of the curve `X`. -/
def degreeStratumPolynomial (d : ℤ) : Polynomial ℚ :=
  Polynomial.C ((curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      (Over.mk (i ≫ toSpec k ι)) hX
      (pullbackClass i (classOf _ (twistingLineBundle k ι 1))) : ℤ) : ℚ) * Polynomial.X +
    Polynomial.C (1 - (coherentGenus k (Over.mk (i ≫ toSpec k ι)) : ℚ) - d)

include e in
/-- **The fibre invariant of (4.8.1) at the rational point by Riemann–Roch**: for a line bundle
`L` on `X`, with `L_k` its pullback to `X ×_k k`,
`χ(X_t, L_t^{-1}(n)) = n · deg O(1) - deg L + 1 - g`. -/
theorem fiberDualTwistEulerChar_closedPoint_eq (L : LineBundle Y) (n : ℤ) :
    fiberDualTwistEulerChar i (𝟙 (Spec (.of k)))
        (pullbackLineBundle (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))) L)
        (IsLocalRing.closedPoint k) n =
      n * curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
          smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
          (Over.mk (i ≫ toSpec k ι)) hX
          (pullbackClass i (classOf _ (twistingLineBundle k ι 1))) -
        curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
          smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
          (Over.mk (i ≫ toSpec k ι)) hX (classOf Y L) + 1 -
        coherentGenus k (Over.mk (i ≫ toSpec k ι)) := by
  have hX' := properties_rationalFiber i hX
  have hdeg (a : PicardGroup Y) :
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
          smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
          (rationalFiber i) hX' (pullbackClass (pullback.fst (i ≫ toSpec k ι) (𝟙 _)) a) =
        curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
          smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
          (Over.mk (i ≫ toSpec k ι)) hX a :=
    curveDegree_pullback_iso smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      Picard.NormDegree.finiteMorphismNormOrder (rationalFiberIso i) hX' hX a
  have hcl : classOf (pullback (i ≫ toSpec k ι) (𝟙 (Spec (.of k))))
      (pulledTwistLineBundle i (𝟙 (Spec (.of k))) n (dualLineBundle _
        (pullbackLineBundle (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))) L))) =
      -pullbackClass (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))) (classOf Y L) +
        n • pullbackClass (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k))))
          (pullbackClass i (classOf _ (twistingLineBundle k ι 1))) := by
    rw [classOf_pulledTwistLineBundle, classOf_dual, fiberTwistClass, pullbackClass_comp,
      pullbackClass_classOf (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))) L]
  calc fiberDualTwistEulerChar i (𝟙 (Spec (.of k)))
        (pullbackLineBundle (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))) L)
        (IsLocalRing.closedPoint k) n
      = moduleEulerChar (pullback.snd (i ≫ toSpec k ι) (𝟙 (Spec (.of k))))
          (pulledTwistLineBundle i (𝟙 (Spec (.of k))) n (dualLineBundle _
            (pullbackLineBundle (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))) L))).val :=
        fiberDualTwistEulerChar_closedPoint i e _ n
    _ = curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
          smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
          (rationalFiber i) hX' (classOf (pullback (i ≫ toSpec k ι) (𝟙 (Spec (.of k))))
            (pulledTwistLineBundle i (𝟙 (Spec (.of k))) n (dualLineBundle _
              (pullbackLineBundle (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))) L)))) +
          1 - coherentGenus k (rationalFiber i) :=
        moduleEulerChar_eq_curveDegree_add_one_sub_genus (rationalFiber i) hX' _
    _ = _ := by
        rw [hcl, map_add, map_neg, map_zsmul, hdeg, hdeg, coherentGenus_iso (rationalFiberIso i),
          smul_eq_mul]
        ring

end RationalFiber

section Strata

variable {k : Type u} [Field k] {ι : Type u} {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace k ι)
  [IsClosedImmersion i] {N : ℕ} (e : ι ≃ Fin (N + 1))
  [Flat (i ≫ toSpec k ι)]
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec k ι)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **A rational point lies in a stratum exactly when its class satisfies (4.8.1) on the fibre
over the rational point**: for a line bundle `L` on `X`, the point `picardPoint P R [L]` lies in
the open of `eulerCondition φ` of the universal section if and only if the pullback of `L` to
`X ×_k k` satisfies `χ(X_t, L_t^{-1}(n)) = φ(n)` at the point `t` of `Spec k`. -/
theorem picardPoint_mem_opens_eulerCondition_iff (φ : Polynomial ℚ) (L : LineBundle Y) :
    (picardPoint (X := Over.mk (i ≫ toSpec k ι)) P R (classOf Y L)).left
        (IsLocalRing.closedPoint k) ∈
          (eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P)) ↔
      HasFiberDualEulerPolynomial i (𝟙 (Spec (.of k))) φ
        (pullbackLineBundle (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))) L)
        (IsLocalRing.closedPoint k) := by
  have h : (fppfPicardSheaf (i ≫ toSpec k ι)).obj.map
      (picardPoint (X := Over.mk (i ≫ toSpec k ι)) P R (classOf Y L)).op (R.homEquiv (𝟙 P)) =
      (quotientProjection (i ≫ toSpec k ι) ≫ toFppfPicardSheaf (i ≫ toSpec k ι)).app
        (op (𝟙_ (Over (Spec (.of k)))))
        (classOf _ (pullbackLineBundle (pullback.fst (i ≫ toSpec k ι) (𝟙 (Spec (.of k)))) L)) := by
    have h₁ := R.homEquiv_comp (ObjectProperty.homMk
      (picardPoint (X := Over.mk (i ≫ toSpec k ι)) P R (classOf Y L)) :
        locallyNoetherianRationalPoint k ⟶ P) (𝟙 P)
    have h₂ := homEquiv_picardPoint (X := Over.mk (i ≫ toSpec k ι)) P R (classOf Y L)
    rw [Category.comp_id] at h₁
    exact h₁.symm.trans h₂
  refine ((eulerCondition i N e φ).holdsAt_map
    (picardPoint (X := Over.mk (i ≫ toSpec k ι)) P R (classOf Y L)) (R.homEquiv (𝟙 P))
    (IsLocalRing.closedPoint k)).symm.trans ?_
  exact ((congrArg (fun x => (eulerCondition i N e φ).HoldsAt x (IsLocalRing.closedPoint k))
    h).to_iff).trans ((eulerCondition i N e φ).holdsAt_app_iff _ _)

include e in
/-- **The Hilbert-polynomial strata of the Picard scheme of a curve are the degree strata**
(Stacks, Picard Schemes of Curves, Lemma 6.7, Tag 0BA0, proof, "decomposition by `χ`"; Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, (4.8.1), p. 28): for a class `c` on `X`, the rational
point `picardPoint P R c` lies in the stratum of `φ` if and only if
`φ(n) = n · deg O(1) - deg c + 1 - g` for every `n`. -/
theorem picardPoint_mem_opens_eulerCondition_iff_eval
    (hX : Properties (Over.mk (i ≫ toSpec k ι) : FScheme k)) (φ : Polynomial ℚ)
    (c : PicardGroup Y) :
    (picardPoint (X := Over.mk (i ≫ toSpec k ι)) P R c).left (IsLocalRing.closedPoint k) ∈
        (eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P)) ↔
      ∀ n : ℤ, φ.eval (n : ℚ) =
        n * curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
            smoothClosedPointDimension smoothFieldDimension
            Picard.Degree.properCurveProductFormula (Over.mk (i ≫ toSpec k ι)) hX
            (pullbackClass i (classOf _ (twistingLineBundle k ι 1))) -
          curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
            smoothClosedPointDimension smoothFieldDimension
            Picard.Degree.properCurveProductFormula (Over.mk (i ≫ toSpec k ι)) hX c + 1 -
          coherentGenus k (Over.mk (i ≫ toSpec k ι)) := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep c
  refine (picardPoint_mem_opens_eulerCondition_iff i e P R φ L).trans ?_
  unfold HasFiberDualEulerPolynomial
  refine forall_congr' fun n => ?_
  rw [fiberDualTwistEulerChar_closedPoint_eq i e hX L n]
  push_cast
  exact eq_comm

/-- **The degree-`d` stratum is the stratum of `m ↦ m · deg O(1) + 1 - g - d`** (Stacks, Picard
Schemes of Curves, Lemma 6.7, Tag 0BA0, proof, "decomposition by `χ`"): the rational point of a
class `c` on `X` lies in the stratum of `degreeStratumPolynomial i hX d` if and only if
`deg c = d`. -/
theorem picardPoint_mem_opens_eulerCondition_degreeStratumPolynomial_iff
    (hX : Properties (Over.mk (i ≫ toSpec k ι) : FScheme k)) (c : PicardGroup Y) (d : ℤ) :
    (picardPoint (X := Over.mk (i ≫ toSpec k ι)) P R c).left (IsLocalRing.closedPoint k) ∈
        (eulerCondition i N e (degreeStratumPolynomial i hX d)).opens (T := P.obj)
          (R.homEquiv (𝟙 P)) ↔
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        (Over.mk (i ≫ toSpec k ι)) hX c = d := by
  refine (picardPoint_mem_opens_eulerCondition_iff_eval i e P R hX _ c).trans
    ⟨fun h => ?_, fun h n => ?_⟩
  · have h0 := h 0
    simp only [degreeStratumPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] at h0
    push_cast at h0
    have h' : ((curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        (Over.mk (i ≫ toSpec k ι)) hX c : ℤ) : ℚ) = d := by linarith
    exact_mod_cast h'
  · subst h
    simp only [degreeStratumPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    ring

/-- **The degree-`d` stratum is open and closed** (`isClopen_setOf_holdsAt_eulerCondition`). -/
theorem isClopen_opens_eulerCondition_degreeStratumPolynomial
    (hX : Properties (Over.mk (i ≫ toSpec k ι) : FScheme k)) (d : ℤ) :
    IsClopen ((eulerCondition i N e (degreeStratumPolynomial i hX d)).opens (T := P.obj)
      (R.homEquiv (𝟙 P)) : Set P.obj.left) :=
  isClopen_setOf_holdsAt_eulerCondition (i := i) (N := N) (e := e) (T := P.obj)
    (R.homEquiv (𝟙 P)) _

/-- **The unit point lies in the degree-zero stratum**: it is the rational point of the zero
class (`picardPoint_zero`). -/
theorem unitPoint_mem_opens_eulerCondition_degreeStratumPolynomial_zero
    [LocallyOfFiniteType P.obj.hom] (hX : Properties (Over.mk (i ≫ toSpec k ι) : FScheme k)) :
    (letI := picardCommGrpObj (i ≫ toSpec k ι) P R; Group.unitPoint P.obj) ∈
      (eulerCondition i N e (degreeStratumPolynomial i hX 0)).opens (T := P.obj)
        (R.homEquiv (𝟙 P)) := by
  let := picardCommGrpObj (i ≫ toSpec k ι) P R
  have hη : picardPoint (X := Over.mk (i ≫ toSpec k ι)) P R 0 = MonObj.one (X := P.obj) :=
    picardPoint_zero (X := Over.mk (i ≫ toSpec k ι)) P R
  change (MonObj.one (X := P.obj)).left (IsLocalRing.closedPoint k) ∈ _
  rw [← hη]
  exact (picardPoint_mem_opens_eulerCondition_degreeStratumPolynomial_iff i e P R hX 0 0).mpr
    (map_zero _)

end Strata

end AlgebraicGeometry.Scheme.OverField.Curve
