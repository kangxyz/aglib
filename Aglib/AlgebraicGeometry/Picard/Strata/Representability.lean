/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.LocalSections
public import Aglib.AlgebraicGeometry.Picard.Strata.Quotient

/-!
# The fine strata `Pic^{φ₀,ψ,k+1}_0` are represented by H-quasi-projective schemes

Let `A` be a Noetherian ring, `S = Spec A`, `i : X ⟶ P^N_A = ProjectiveSpace A ι` a closed
immersion with `ι ≃ Fin (N + 1)` such that `πX = i ≫ toSpec A ι` is flat and geometrically
integral, `φ₀, ψ ∈ ℚ[X]`, `k ∈ ℕ`, `C = fineCondition i N e φ₀ ψ 0 (k + 1)` the fibre condition of
the stratum `Pic^{φ₀,ψ,k+1}_0` of `Pic_{X/S,(fppf)}`, and `E` a representation of
`Div^{ψ − φ₀}_X` on locally Noetherian test schemes by an H-quasi-projective `D`. With
`Z = C.abelPreimageOver E`, its universal class `α_Z = C.abelPreimageFppfAbelClass E`, the
quotient `Q = (abelQuotient e k E).quotientOver` of `Z` by `R = Z ×_P Z`, the quotient morphism
`q = (abelQuotient e k E).quotientπ` and the descended class `λ = abelQuotientFppfClass e k E`
(`Aglib.AlgebraicGeometry.Picard.Strata.Quotient`):

* `Strata.abelQuotientRepresentableBy e k E`: **`Q` represents `Pic^{φ₀,ψ,k+1}_0` on locally
  Noetherian test schemes**
  (`C.locallyNoetherianSubfunctor.toFunctor.RepresentableBy (abelQuotient e k E).quotientOver`),
  through `f ↦ f^* λ` (`abelQuotientRepresentableBy_homEquiv_coe`); `q` corresponds to `α_Z`
  (`abelQuotientRepresentableBy_homEquiv_quotientπ`).
* `Strata.exists_fineCondition_representableBy`: there are an H-quasi-projective `Q` over `S`, a
  flat, surjective and proper `q : Z ⟶ Q` and `λ ∈ Pic_{X/S,(fppf)}(Q)` with `q^* λ = α_Z` such
  that `f ↦ f^* λ` is a representation of `Pic^{φ₀,ψ,k+1}_0` by `Q` on locally Noetherian test
  schemes.

These are `abelQuotientRepresentableByOfExistsLift` and
`exists_fineCondition_representableBy_of_exists_lift` with their local lifting hypothesis
discharged by the fppf-local surjectivity of the Abel map `Z ⟶ Pic^{φ₀,ψ,k+1}_0`
(`exists_lift_abelPreimageOver_of_mem_subfunctor_fineCondition`,
`Aglib.AlgebraicGeometry.Picard.Strata.LocalSections`).

This is Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, p. 30 (from "Let's
now prove the projection `α : Z → P_0^{φ0}` is a surjection of étale sheaves" to "the theorem now
results from the following general lemma"), with Lemma 4.9 (statement p. 30, proof pp. 30–31),
for the fine stratum `Pic^{φ₀,ψ,k+1}_0`, in the fppf topology and on locally Noetherian test
schemes. The differences from the source are recorded in `Picard/Strata/Quotient` and
`Picard/Strata/LocalSections`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard.Strata

open ProjectiveSpace

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : Polynomial ℚ} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} [IsHQuasiProjective D.obj.hom]
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- **`Q` represents the fine stratum `Pic^{φ₀,ψ,k+1}_0` on locally Noetherian test schemes**
(Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 30, and Lemma 4.9, pp. 30–31, fppf form):
the quotient `Q = Z / R` represents `Pic^{φ₀,ψ,k+1}_0` through `f ↦ f^* λ`
(`abelQuotientRepresentableBy_homEquiv_coe`). This is `abelQuotientRepresentableByOfExistsLift`
with the local sections of the Abel map
(`exists_lift_abelPreimageOver_of_mem_subfunctor_fineCondition`). -/
def abelQuotientRepresentableBy :
    (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy
      (abelQuotient e k E).quotientOver :=
  abelQuotientRepresentableByOfExistsLift e k E
    (exists_lift_abelPreimageOver_of_mem_subfunctor_fineCondition e k E)

/-- **The representation is `f ↦ f^* λ`.** -/
theorem abelQuotientRepresentableBy_homEquiv_coe
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (f : T ⟶ (abelQuotient e k E).quotientOver) :
    ((abelQuotientRepresentableBy e k E).homEquiv f).1 =
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map f.hom.op (abelQuotientFppfClass e k E) :=
  rfl

/-- **The quotient morphism corresponds to the Abel map**: under the representation, `q : Z ⟶ Q`
corresponds to the universal class `α_Z`, so `α : Z → Pic^{φ₀,ψ,k+1}_0` is represented by `q`. -/
theorem abelQuotientRepresentableBy_homEquiv_quotientπ :
    ((abelQuotientRepresentableBy e k E).homEquiv (abelQuotient e k E).quotientπ).1 =
      (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E :=
  fppfPicardSheaf_map_abelQuotientFppfClass e k E

/-- **The fine stratum `Pic^{φ₀,ψ,k+1}_0` is represented by an H-quasi-projective quotient of `Z`**
(Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 30, and Lemma 4.9, pp. 30–31; fppf form, on
locally Noetherian test schemes): there are an H-quasi-projective `Q` over `S`, a flat, surjective
and proper `q : Z ⟶ Q` and `λ ∈ Pic_{X/S,(fppf)}(Q)` with `q^* λ = α_Z`, such that `f ↦ f^* λ` is a
representation of `Pic^{φ₀,ψ,k+1}_0` by `Q` on locally Noetherian test schemes. -/
theorem exists_fineCondition_representableBy :
    ∃ (Q : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))
      (q : (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E ⟶ Q)
      (l : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op Q.obj))
      (rep :
        (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy
          Q),
      IsHQuasiProjective Q.obj.hom ∧ Flat q.hom.left ∧ Surjective q.hom.left ∧
        IsProper q.hom.left ∧
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map q.hom.op l =
          (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E ∧
        ∀ {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (f : T ⟶ Q),
          (rep.homEquiv f).1 = (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map f.hom.op l :=
  exists_fineCondition_representableBy_of_exists_lift e k E
    (exists_lift_abelPreimageOver_of_mem_subfunctor_fineCondition e k E)

end AlgebraicGeometry.Scheme.RelativePicard.Strata
