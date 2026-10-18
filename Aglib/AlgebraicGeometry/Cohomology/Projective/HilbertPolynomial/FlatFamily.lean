/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Fiber
public import Aglib.AlgebraicGeometry.Cohomology.Projective.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Cohomology.Projective.FlatTwist
public import Aglib.Topology.NoetherianSpace
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback

/-!
# Hilbert polynomials are locally constant in flat families

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)`, and `F` a coherent module on `P^n_A =
ProjectiveSpace A ι` that is relatively flat over `Spec A`. For a prime `s` of `A` write
`F_s = π_s^* F` on `P^n_{κ(s)}`, `π_s = ProjectiveSpace.map (algebraMap A κ(s)) ι`. Then:

* for every `m : ℤ`, `s ↦ χ(F_s(m)) = projectiveHilbertFunction κ(s) ι F_s m` is locally constant
  (`isLocallyConstant_projectiveHilbertFunction_fiber`);
* `s ↦ projectiveHilbertPolynomial κ(s) ι F_s` is locally constant
  (`isLocallyConstant_projectiveHilbertPolynomial_fiber`), hence constant when `Spec A` is
  preconnected (`projectiveHilbertPolynomial_fiber_eq_of_preconnectedSpace`); then a single
  `Φ : ℚ[X]` has `χ(F_s(m)) = Φ(m)` for every `s` and every `m : ℤ`
  (`exists_projectiveHilbertPolynomial_fiber_eq_of_preconnectedSpace`).

The first statement is the local constancy of the fibre Euler characteristic
(`isLocallyConstant_moduleFiberEulerChar_of_projectiveEmbedding`, Nitsure, *Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1, Thm 3.7 (2), p. 17; Stacks Project, Tag 0B9T)
applied to the twist `F(m)`, which is coherent and relatively flat
(`ProjectiveSpace.twistingTensor_relativeFlat`), through the identification of its fibre with
`F_s(m)` on `P^n_{κ(s)}` (`moduleFiberEulerChar_twistingTensor_toSpec`). The Hilbert polynomial
is that of the field case (Stacks, Tag 08AD). The second follows because `Spec A` is a
Noetherian space, on which any family of locally constant functions is jointly locally constant
(`TopologicalSpace.NoetherianSpace.isLocallyConstant_pi`). This is the statement "the Hilbert
polynomials are locally constant for a flat family of sheaves" in the proof of Nitsure's
Thm 4.3, (A), pp. 20–21, over an affine Noetherian base.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1))
  (F : (ProjectiveSpace A ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
  (hflat : relativeFlat (toSpec A ι) F)

include e hF hflat in
/-- **The fibre values `χ(F_s(m))` are locally constant in a flat family** (Nitsure,
arXiv:math/0504590v1, Thm 3.7 (2), p. 17, and Stacks Project, Tag 0B9T, for `F(m)` on `P^n_A`).
For every `m : ℤ`, `s ↦ χ(P^n_{κ(s)}, F_s(m))` is locally constant on `Spec A`. -/
theorem isLocallyConstant_projectiveHilbertFunction_fiber (m : ℤ) :
    IsLocallyConstant (fun s : PrimeSpectrum A =>
      projectiveHilbertFunction s.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F) m) := by
  have : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  have h := isLocallyConstant_moduleFiberEulerChar_of_projectiveEmbedding (i := 𝟙 _) e
    (Category.id_comp _) (twistingTensor_affineLocallyFiniteType A ι m F hF)
    (twistingTensor_relativeFlat _ F hflat m)
  have heq : (fun s : PrimeSpectrum A =>
      projectiveHilbertFunction s.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F) m) =
      moduleFiberEulerChar (toSpec A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) :=
    funext fun s => (moduleFiberEulerChar_twistingTensor_toSpec ι F m s).symm
  rw [heq]
  exact h

include e hF hflat in
/-- **Hilbert polynomials are locally constant in a flat family** (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3, (A), pp. 20–21, over an affine Noetherian base): the
Hilbert polynomial of the fibre `F_s` on `P^n_{κ(s)}` is a locally constant function of
`s ∈ Spec A`. -/
theorem isLocallyConstant_projectiveHilbertPolynomial_fiber :
    IsLocallyConstant (fun s : PrimeSpectrum A =>
      projectiveHilbertPolynomial s.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F)) :=
  (TopologicalSpace.NoetherianSpace.isLocallyConstant_pi
    (isLocallyConstant_projectiveHilbertFunction_fiber n e F hF hflat)).comp
      Polynomial.polynomialOnInt

include e hF hflat in
/-- Over a preconnected (for example connected) Noetherian base, all fibres of a flat family have
the same Hilbert polynomial. -/
theorem projectiveHilbertPolynomial_fiber_eq_of_preconnectedSpace
    [PreconnectedSpace (PrimeSpectrum A)] (s t : PrimeSpectrum A) :
    projectiveHilbertPolynomial s.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F) =
      projectiveHilbertPolynomial t.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A t.asIdeal.ResidueField) ι)).obj F) :=
  (isLocallyConstant_projectiveHilbertPolynomial_fiber n e F hF hflat).apply_eq_of_preconnectedSpace
    s t

include e hF hflat in
/-- **The Hilbert polynomial of a flat family over a preconnected base**: a single `Φ : ℚ[X]` is
the Hilbert polynomial of every fibre, and `χ(P^n_{κ(s)}, F_s(m)) = Φ(m)` for every `s` and every
`m : ℤ`. -/
theorem exists_projectiveHilbertPolynomial_fiber_eq_of_preconnectedSpace
    [PreconnectedSpace (PrimeSpectrum A)] :
    ∃ Φ : ℚ[X], ∀ s : PrimeSpectrum A,
      projectiveHilbertPolynomial s.asIdeal.ResidueField ι
          ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F) = Φ ∧
        ∀ m : ℤ, (projectiveHilbertFunction s.asIdeal.ResidueField ι
          ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F) m : ℚ) =
            Φ.eval (m : ℚ) := by
  have : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  obtain ⟨Φ, hΦ⟩ :=
    (isLocallyConstant_projectiveHilbertPolynomial_fiber n e F hF hflat).exists_eq_const
  refine ⟨Φ, fun s => ⟨congrFun hΦ s, fun m => ?_⟩⟩
  rw [projectiveHilbertFunction_eq_eval _ ι n e _ (affineLocallyFiniteType_pullback _ hF) m]
  exact congrArg (fun P : ℚ[X] => P.eval (m : ℚ)) (congrFun hΦ s)

end AlgebraicGeometry.Scheme.Cohomology
