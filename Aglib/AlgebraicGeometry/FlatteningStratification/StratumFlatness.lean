/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Flatness

/-!
# One stratum `S_f` represents flatness with Hilbert polynomial `f`

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)`, `F` a coherent module on `P^n_A` and `N` a bound
of the fibre statements of (B) and (C) (`IsFiberBaseChangeBound F N`). For a polynomial `f` that
occurs as a fibre Hilbert polynomial, the stratum `S_f = hilbertPolynomialStratum n e F hF N f`
of Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, proof of Thm 4.3,
p. 22, represents, on locally Noetherian test schemes, the morphisms `g : T ⟶ Spec A` along which
the pullback of `F` is flat and every fibre Hilbert polynomial `P_{g t}` is `f`
(`exists_lift_hilbertPolynomialStratumι_iff_relativeFlat`). This follows from Theorem 4.3 (ii)
for `∐ S_f` (`exists_lift_hilbertPolynomialStrataι_iff`) and (i): a lift to `∐ S_f` lands in the
component of `f` exactly when the fibre Hilbert polynomials are `f`.

Consequently each stratum, not only their disjoint union, is independent of the bound `N` up to
a unique isomorphism over `Spec A` (`exists_iso_hilbertPolynomialStratum`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {ι : Type u} [IsNoetherianRing A] (n : ℕ) (e : ι ≃ Fin (n + 1))
  (F : (ProjectiveSpace A ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)

include e hF in
/-- **The universal property of one stratum in terms of flatness** (Nitsure,
arXiv:math/0504590v1, Thm 4.3 (ii), proof p. 22, for one `S_f`): for `N` a bound of the fibre
statements of (B) and (C), a polynomial `f` that occurs and a locally Noetherian `T`, a morphism
`g : T ⟶ Spec A` factors through `S_f` if and only if the pullback of `F` to
`P^n_A ×_{Spec A} T` is flat over `T` and every fibre Hilbert polynomial `P_{g t}` is `f`. -/
theorem exists_lift_hilbertPolynomialStratumι_iff_relativeFlat {N : ℕ}
    (hN : IsFiberBaseChangeBound F N) (f : Polynomial ℚ)
    (hf : f ∈ Set.range (fiberHilbertPolynomial F)) {T : Scheme.{u}} [IsLocallyNoetherian T]
    (g : T ⟶ Spec (CommRingCat.of A)) :
    (∃ h : T ⟶ hilbertPolynomialStratum n e F hF N f,
        h ≫ hilbertPolynomialStratumι n e F hF N f = g) ↔
      relativeFlat (pullback.snd (toSpec A ι) g)
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj F) ∧
        ∀ t : T, fiberHilbertPolynomial F (g t) = f := by
  let f' : Set.range (fiberHilbertPolynomial F) := ⟨f, hf⟩
  have e1 := sigmaι_hilbertPolynomialStrataι n e F hF N f'
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨relativeFlat_of_exists_lift_hilbertPolynomialStrataι n e F hF hN _
      (h ≫ Sigma.ι (fun f : Set.range (fiberHilbertPolynomial F) =>
        hilbertPolynomialStratum n e F hF N f) f') ?_, fun t => ?_⟩
    · rw [Category.assoc, e1]
    · have hmem : (h ≫ hilbertPolynomialStratumι n e F hF N f) t ∈
          Set.range (hilbertPolynomialStratumι n e F hF N f) := ⟨h t, rfl⟩
      rw [range_hilbertPolynomialStratumι n e F hF hN f hf] at hmem
      exact hmem
  · rintro ⟨hflat, hpts⟩
    obtain ⟨H, hH⟩ := exists_lift_hilbertPolynomialStrataι_of_relativeFlat n e F hF hN g hflat
    have hsub : Set.range H ⊆ Set.range (Sigma.ι (fun f : Set.range (fiberHilbertPolynomial F) =>
        hilbertPolynomialStratum n e F hF N f) f') := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨f'', y, hy⟩ := Scheme.exists_sigmaι_eq (H t)
      have hgt : g t ∈ Set.range (hilbertPolynomialStratumι n e F hF N f'') := ⟨y, by
        rw [← hH, Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply,
          sigmaι_hilbertPolynomialStrataι]⟩
      rw [range_hilbertPolynomialStratumι n e F hF hN _ f''.2] at hgt
      have hff : f'' = f' := Subtype.ext (hgt.symm.trans (hpts t))
      subst hff
      exact ⟨y, hy⟩
    refine ⟨IsOpenImmersion.lift _ H hsub, ?_⟩
    calc _ = IsOpenImmersion.lift _ H hsub ≫
          (Sigma.ι (fun f : Set.range (fiberHilbertPolynomial F) =>
            hilbertPolynomialStratum n e F hF N f) f' ≫ hilbertPolynomialStrataι n e F hF N) := by
          rw [e1]
      _ = g := by rw [← Category.assoc, IsOpenImmersion.lift_fac, hH]

include e hF in
/-- **Each stratum is independent of the bound** (compare Nitsure, arXiv:math/0504590v1,
Thm 4.3 (ii), "the subscheme `S_f` is uniquely determined"): for two bounds `N`, `N'` of the fibre
statements of (B) and (C) and a polynomial `f` that occurs, the strata `S_f` built from `N` and
from `N'` are isomorphic over `Spec A`. Both are locally Noetherian and represent the same
condition on locally Noetherian schemes
(`exists_lift_hilbertPolynomialStratumι_iff_relativeFlat`). -/
theorem exists_iso_hilbertPolynomialStratum {N N' : ℕ} (hN : IsFiberBaseChangeBound F N)
    (hN' : IsFiberBaseChangeBound F N') (f : Polynomial ℚ)
    (hf : f ∈ Set.range (fiberHilbertPolynomial F)) :
    ∃ φ : hilbertPolynomialStratum n e F hF N f ≅ hilbertPolynomialStratum n e F hF N' f,
      φ.hom ≫ hilbertPolynomialStratumι n e F hF N' f = hilbertPolynomialStratumι n e F hF N f := by
  have : IsLocallyNoetherian (hilbertPolynomialStratum n e F hF N f) :=
    LocallyOfFiniteType.isLocallyNoetherian (hilbertPolynomialStratumι n e F hF N f)
  have : IsLocallyNoetherian (hilbertPolynomialStratum n e F hF N' f) :=
    LocallyOfFiniteType.isLocallyNoetherian (hilbertPolynomialStratumι n e F hF N' f)
  obtain ⟨a, ha⟩ := (exists_lift_hilbertPolynomialStratumι_iff_relativeFlat n e F hF hN' f hf
    _).mpr ((exists_lift_hilbertPolynomialStratumι_iff_relativeFlat n e F hF hN f hf _).mp
      ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨b, hb⟩ := (exists_lift_hilbertPolynomialStratumι_iff_relativeFlat n e F hF hN f hf
    _).mpr ((exists_lift_hilbertPolynomialStratumι_iff_relativeFlat n e F hF hN' f hf _).mp
      ⟨𝟙 _, Category.id_comp _⟩)
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · rw [← cancel_mono (hilbertPolynomialStratumι n e F hF N f), Category.assoc, hb, ha,
      Category.id_comp]
  · rw [← cancel_mono (hilbertPolynomialStratumι n e F hF N' f), Category.assoc, ha, hb,
      Category.id_comp]

end AlgebraicGeometry.Scheme.Cohomology
