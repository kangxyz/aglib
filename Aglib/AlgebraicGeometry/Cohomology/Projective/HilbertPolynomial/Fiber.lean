/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Fibers.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Basic
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.FieldBaseChange
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Fibre cohomology of projective space in the coordinates of `P^n_{κ(p)}`

For a ring `A`, a module `M` on `P_A = ProjectiveSpace A ι` and a prime `p` of `A`, the fibre
cohomology dimension `moduleFiberCohomologyDimension (toSpec A ι) M q p` is computed on the native
fibre product `P_A ×_{Spec A} Spec κ(p)`, with the coefficient pulled back along the first
projection. This file identifies it with the dimension of the cohomology of
`M_p = π^* M` on the polynomial projective space `P_{κ(p)}`, where
`π = ProjectiveSpace.map (algebraMap A κ(p)) ι` (`moduleFiberCohomologyDimension_toSpec`). The
fibre Euler characteristic is then `projectiveEulerChar` (`moduleFiberEulerChar_toSpec`), and for
the twists `F(m) = O(m) ⊗ F` it is the field Hilbert function of `F_p` at `m`
(`moduleFiberEulerChar_twistingTensor_toSpec`), by the base change of the twisting sheaves
`twistingTensorPullbackIso`. No hypothesis on `A`, `ι` or `M` is used.

The transport is the general `finrank_moduleCohomology_eq_of_isIso` (in
`Cohomology/Functoriality/Modules/Isomorphism`) for a scheme isomorphism over `Spec k`,
instantiated with `ProjectiveSpace.baseChangeIso` and the coefficient comparison
`toSpecFiberCoefficientIso`. It identifies the fibre `X_s` of Nitsure, *Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1, Thm 3.7 (2), p. 17, for `X = P^n_S`, with
`P^n_{κ(s)}`, as used in the proof of Thm 4.3, (A), pp. 20–21.

The fibre Hilbert polynomial is unchanged by base change: for a ring map `φ : A →+* B` and a prime
`t` of `B` over `s = φ⁻¹ t`, the Hilbert polynomial of the fibre of `π_φ^* F` at `t` is that of
`F_s` (`projectiveHilbertPolynomial_fiber_pullback_map`). The input is the invariance of Hilbert
functions under field extension (`projectiveHilbertFunction_pullback_map`, in `FieldBaseChange`),
from the flat base change of cohomology `projectiveCohomologyDim_pullback_map`, for quasicoherent
`F` and finitely many coordinates, and on `ProjectiveSpace.map_comp_map_eq_of_comp_eq` (in
`ProjectiveSpace/BaseChange/Map`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] (ι : Type u)

/-- The pulled-back coefficient on the native fibre product, transported to `P_{κ(p)}`:
`E^* a^* M ≅ π^* M` for `E = baseChangeIso`, `a` the first projection and
`π = ProjectiveSpace.map (algebraMap A κ(p)) ι`. -/
def toSpecFiberCoefficientIso (M : (ProjectiveSpace A ι).Modules) (p : PrimeSpectrum A) :
    (Scheme.Modules.pullback (baseChangeIso (algebraMap A p.asIdeal.ResidueField) ι).hom).obj
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField))))).obj M) ≅
      (Scheme.Modules.pullback (map (algebraMap A p.asIdeal.ResidueField) ι)).obj M :=
  (Scheme.Modules.pullbackComp (baseChangeIso (algebraMap A p.asIdeal.ResidueField) ι).hom
      (pullback.fst (toSpec A ι)
        (Spec.map (CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField))))).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (baseChangeIso_hom_fst (algebraMap A p.asIdeal.ResidueField) ι)).app M

/-- **Fibre cohomology in the coordinates of `P_{κ(p)}`**: the dimension of the `q`-th
cohomology of `M` on the fibre of `P_A → Spec A` over `p` is the dimension of the `q`-th
cohomology of `π^* M` on `P_{κ(p)}`, `π = ProjectiveSpace.map (algebraMap A κ(p)) ι`. -/
theorem moduleFiberCohomologyDimension_toSpec (M : (ProjectiveSpace A ι).Modules) (q : ℕ)
    (p : PrimeSpectrum A) :
    moduleFiberCohomologyDimension (toSpec A ι) M q p =
      projectiveCohomologyDim p.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A p.asIdeal.ResidueField) ι)).obj M) q :=
  finrank_moduleCohomology_eq_of_isIso
    (baseChangeIso (algebraMap A p.asIdeal.ResidueField) ι).hom
    (pullback.snd (toSpec A ι)
      (Spec.map (CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField))))
    (toSpec p.asIdeal.ResidueField ι)
    (baseChangeIso_hom_snd (algebraMap A p.asIdeal.ResidueField) ι) _
    (toSpecFiberCoefficientIso ι M p) q

/-- The fibre Euler characteristic of `P_A → Spec A` at `p` is the Euler characteristic of
`π^* M` on `P_{κ(p)}`. -/
theorem moduleFiberEulerChar_toSpec (M : (ProjectiveSpace A ι).Modules) (p : PrimeSpectrum A) :
    moduleFiberEulerChar (toSpec A ι) M p =
      projectiveEulerChar p.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A p.asIdeal.ResidueField) ι)).obj M) := by
  unfold moduleFiberEulerChar projectiveEulerChar
  exact finsum_congr fun q => by rw [moduleFiberCohomologyDimension_toSpec ι M q p]

/-- **The fibre Euler characteristic of a twist is the fibre Hilbert function**:
`χ((P_A)_p, F(m)) = χ(P_{κ(p)}, F_p(m))` for `F_p = π^* F`, by the base change of the twisting
sheaves `twistingTensorPullbackIso`. -/
theorem moduleFiberEulerChar_twistingTensor_toSpec (F : (ProjectiveSpace A ι).Modules) (m : ℤ)
    (p : PrimeSpectrum A) :
    moduleFiberEulerChar (toSpec A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) p =
      projectiveHilbertFunction p.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap A p.asIdeal.ResidueField) ι)).obj F) m := by
  rw [moduleFiberEulerChar_toSpec]
  exact projectiveEulerChar_congr _ ι
    (twistingTensorPullbackIso (algebraMap A p.asIdeal.ResidueField) ι m F)

/-- **Fibre Hilbert polynomials are unchanged by base change**: for a ring map `φ : A →+* B`, a
quasicoherent `F` on `P_A` and a prime `t` of `B` over `s = φ⁻¹ t`, the fibre of `π_φ^* F` at
`t` and the fibre `F_s` have the same Hilbert polynomial. -/
theorem projectiveHilbertPolynomial_fiber_pullback_map {B : Type u} [CommRing B] (φ : A →+* B)
    [Finite ι] (F : (ProjectiveSpace A ι).Modules) [F.IsQuasicoherent] (t : PrimeSpectrum B) :
    projectiveHilbertPolynomial t.asIdeal.ResidueField ι
        ((Scheme.Modules.pullback (map (algebraMap B t.asIdeal.ResidueField) ι)).obj
          ((Scheme.Modules.pullback (map φ ι)).obj F)) =
      projectiveHilbertPolynomial (PrimeSpectrum.comap φ t).asIdeal.ResidueField ι
        ((Scheme.Modules.pullback
          (map (algebraMap A (PrimeSpectrum.comap φ t).asIdeal.ResidueField) ι)).obj F) := by
  let ψ := Ideal.ResidueField.map (PrimeSpectrum.comap φ t).asIdeal t.asIdeal φ rfl
  have hψ : (algebraMap B t.asIdeal.ResidueField).comp φ =
      ψ.comp (algebraMap A (PrimeSpectrum.comap φ t).asIdeal.ResidueField) :=
    RingHom.ext fun a => (Ideal.ResidueField.map_algebraMap _ _ φ rfl a).symm
  let E : (Scheme.Modules.pullback (map (algebraMap B t.asIdeal.ResidueField) ι)).obj
        ((Scheme.Modules.pullback (map φ ι)).obj F) ≅
      (Scheme.Modules.pullback (map ψ ι)).obj ((Scheme.Modules.pullback
        (map (algebraMap A (PrimeSpectrum.comap φ t).asIdeal.ResidueField) ι)).obj F) :=
    (Scheme.Modules.pullbackComp (map (algebraMap B t.asIdeal.ResidueField) ι)
      (map φ ι)).app F ≪≫
    (Scheme.Modules.pullbackCongr (map_comp_map_eq_of_comp_eq ι hψ)).app F ≪≫
    ((Scheme.Modules.pullbackComp (map ψ ι)
      (map (algebraMap A (PrimeSpectrum.comap φ t).asIdeal.ResidueField) ι)).app F).symm
  rw [projectiveHilbertPolynomial_congr _ ι E]
  unfold projectiveHilbertPolynomial
  rw [projectiveHilbertFunction_pullback_map ι ψ]

end AlgebraicGeometry.Scheme.Cohomology
