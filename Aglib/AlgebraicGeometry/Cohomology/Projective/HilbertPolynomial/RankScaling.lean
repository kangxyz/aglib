/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.GenericComparison
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The top-dimensional Hilbert coefficient scales by actual locally free rank

For the original closed embedding of an integral scheme in projective
space, a vector bundle of rank r has degree-d Hilbert coefficient r times
that of the structure module when dim X is at most d. One actual local
basis at the generic point gives an isomorphism with the native free
module. The generic coefficient theorem discharges its support boundary.

Only a genuinely free module has its whole Hilbert polynomial multiplied
by the rank. The vector-bundle conclusion concerns the indicated
coefficient, not the entire polynomial or Euler characteristic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

attribute [local instance] Abelian.hasFiniteBiproducts

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u)

/-- The original binary direct sum has the sum of the two Hilbert polynomials. -/
theorem projectiveHilbertPolynomial_biprod
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (M N : (ProjectiveSpace k ι).Modules)
    (hM : affineLocallyFiniteType _ M) (hN : affineLocallyFiniteType _ N) :
    projectiveHilbertPolynomial k ι (M ⊞ N) =
      projectiveHilbertPolynomial k ι M + projectiveHilbertPolynomial k ι N := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  let a : M ⟶ M ⊞ N := biprod.inl
  have hMN : affineLocallyFiniteType (ProjectiveSpace k ι) (M ⊞ N) :=
    (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_of_isLimit_binaryFan
      (BinaryBiproduct.isLimit M N) hM hN
  have hC := (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel a hM hMN
  have hS : (ShortComplex.cokernelSequence a).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact a, mono_f := inferInstanceAs (Mono a) }
  have h := projectiveHilbertPolynomial_add_of_shortExact k ι n e _ hS hM hMN hC
  change projectiveHilbertPolynomial k ι (M ⊞ N) =
    projectiveHilbertPolynomial k ι M + projectiveHilbertPolynomial k ι (cokernel a) at h
  exact h.trans (congrArg (fun Q : ℚ[X] => projectiveHilbertPolynomial k ι M + Q)
    (projectiveHilbertPolynomial_congr k ι (cokernelBiprodInlIso (X := M) (Y := N))))

/-- A genuinely free source module has the whole rank-multiple Hilbert polynomial
after the original closed pushforward. This assertion is not made for arbitrary
finite locally free modules. -/
theorem projectiveHilbertPolynomial_pushforward_free
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {X : Scheme.{u}}
    (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j] (r : ℕ) :
    projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))) =
      (r : ℚ) • projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  let P := Scheme.Modules.pushforward j
  let J (r : ℕ) := ULift.{u} (Fin r)
  let F (r : ℕ) : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) (J r)
  let L : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}
  have hF (r : ℕ) : affineLocallyFiniteType (ProjectiveSpace k ι) (P.obj (F r)) :=
    Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward j
      (coherent_of_finiteLocallyFree (F r))
  have hL : affineLocallyFiniteType (ProjectiveSpace k ι) (P.obj L) :=
    Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward j
      (coherent_of_finiteLocallyFree L)
  have eL : L ≅ SheafOfModules.unit X.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  change projectiveHilbertPolynomial k ι (P.obj (F r)) = _
  induction r with
  | zero =>
    have hz : IsZero (F 0) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply (SheafOfModules.freeHomEquiv _).injective
      funext a
      exact Fin.elim0 a.down
    rw [projectiveHilbertPolynomial_eq_zero_of_isZero k ι (P.map_isZero hz),
      Nat.cast_zero, zero_smul]
  | succ r ih =>
    let eJ : J (r + 1) ≃ J r ⊕ PUnit.{u + 1} := Fintype.equivOfCardEq (by simp [J])
    let eF : F (r + 1) ≅ F r ⨿ L :=
      (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso eJ.toIso ≪≫
        (SheafOfModules.freeSumIso (J r) PUnit.{u + 1}).symm
    let eP : P.obj (F (r + 1)) ≅ P.obj (F r) ⊞ P.obj L :=
      P.mapIso eF ≪≫ (PreservesColimitPair.iso P (F r) L).symm ≪≫
        (biprod.isoCoprod (P.obj (F r)) (P.obj L)).symm
    rw [projectiveHilbertPolynomial_congr k ι eP,
      projectiveHilbertPolynomial_biprod k ι n e _ _ (hF r) hL,
      projectiveHilbertPolynomial_congr k ι (P.mapIso eL), ih, Nat.cast_add, Nat.cast_one,
      add_smul, one_smul]

/-- The degree-`d` coefficient of an actual rank-r vector bundle is r times
the structure-module coefficient when dim X is at most d. The native local
basis, generic open and coherent comparison are chosen inside the proof. -/
theorem coeff_projectiveHilbertPolynomial_pushforward_of_sheafHasRank
    [Infinite k] (n : ℕ) (e : ι ≃ Fin (n + 1)) {X : Scheme.{u}} [IsIntegral X]
    (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (M : X.Modules) (r : ℕ) (hr : SheafHasRank M r)
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : ℕ)) :
    (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj M)).coeff d =
      (r : ℚ) * (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit X.ringCatSheaf))).coeff d := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian j
  let : IsFiniteLocallyFree X M := hr.isFiniteLocallyFree
  have hM := coherent_of_finiteLocallyFree M
  let F : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))
  have hF : affineLocallyFiniteType X F := coherent_of_finiteLocallyFree F
  obtain ⟨q, hq, hn⟩ := hr
  let : q.IsLocallyFreeData := hq
  obtain ⟨a, ha⟩ := (Opens.coversTop_iff X q.X).mp q.coversTop |>.exists_mem (genericPoint X)
  let U : X.Opens := q.X a
  let : IsIso (q.generators a).π := hq.isIso a
  let eI : (q.generators a).I ≃ ULift.{u} (Fin r) := (hn a).some.trans Equiv.ulift.symm
  let eU : M.restrict U.ι ≅ F.restrict U.ι :=
    (restrictBasisIso M U (q.generators a)).symm ≪≫
      (SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso eI.toIso ≪≫
        (pullbackFreeIso U.ι (ULift.{u} (Fin r))).symm ≪≫
          ((restrictFunctorIsoPullback U.ι).app F).symm
  have h := coeff_projectiveHilbertPolynomial_pushforward_eq_of_restrictIso
    k ι n e j M F hM hF U ha eU d hd
  exact h.trans (by
    change (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))))).coeff d = _
    rw [projectiveHilbertPolynomial_pushforward_free k ι n e j r, Polynomial.coeff_smul,
      smul_eq_mul])

end AlgebraicGeometry.Scheme.Cohomology
