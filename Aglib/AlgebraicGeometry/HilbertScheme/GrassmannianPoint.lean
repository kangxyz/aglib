/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.QuotientDirectImage
public import Aglib.AlgebraicGeometry.HilbertScheme.Injectivity
public import Aglib.AlgebraicGeometry.Cohomology.Modules.UnitHom
public import Aglib.RingTheory.Grassmannian.Kernel
public import Aglib.RingTheory.Spectrum.Prime.FreeLocus.ResidueField

/-!
# The Grassmannian point of a flat family over an affine base

Let `B` be a Noetherian ring, `ι ≃ Fin (n + 1)` and `Z ⊆ P^n_B` a closed subscheme, flat over `B`,
whose fibers over the primes of `B` all have Hilbert polynomial `Φ`. For a natural number
`r ≥ hilbertRegularityBound n Φ`, the restriction map `H^0(P^n_B, 𝒪(r)) ⟶ H^0(P^n_B, 𝒪_Z(r))` is
surjective onto a finite projective module of constant rank `Φ(r)` (Nitsure, *Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 25). Its kernel is therefore a point of
Mathlib's Grassmannian `G(Φ(r), H^0(P^n_B, 𝒪(r)); B)` of rank-`Φ(r)` quotients
(`grassmannianPoint`), and the point determines `Z` (`eq_of_grassmannianPoint_eq`).

* `rankAtStalk_moduleCohomology_zero_eq`: if the base-change map of `H^0(P^n_B, M)` to the
  residue field `κ(p)` is an isomorphism, the rank of `H^0(P^n_B, M)` at `p` is the fiber dimension
  `moduleFiberCohomologyDimension (toSpec B ι) M 0 p`
  (`Module.rankAtStalk_eq_finrank_of_extendScalars_iso`). For `r ≥ m` the ranks of
  `H^0(𝒪_Z(r))` and `H^0(I_Z(r))` are `Φ(r)` and `C(r + n, n) - Φ(r)`
  (`rankAtStalk_moduleCohomology_quotientTwist`, `rankAtStalk_moduleCohomology_idealTwist`).
* `grassmannianPoint`: the kernel of `H^0(𝒪(r) ⊗ 𝒪) ⟶ H^0(𝒪_Z(r))`, with quotient
  `H^0(𝒪_Z(r))` (`exact_moduleCohomology_twistedShortComplex`), finite projective of rank `Φ(r)`
  at every prime (`projective_moduleCohomology_quotientTwist`,
  `moduleFiberCohomologyDimension_quotientTwist`), through `Module.Grassmannian.ofSurjective`.
* `mem_idealTwistSections_iff`: with global sections written as elements of `H^0(M)`
  (`Scheme.Cohomology.unitHomH0Equiv`), a section of `𝒪(r) ⊗ 𝒪` lies in the image of
  `H^0(I_Z(r))` exactly when it maps to zero in `H^0(𝒪_Z(r))`.
* `eq_of_grassmannianPoint_eq`: **injectivity on `Spec B`**: two such families with the same
  Grassmannian point are equal.

The identification `H^0(P^n_B, 𝒪(r)) ≅ B ⊗_A A[x]_r` is `HilbertScheme/GrassmannianFunctor`, and
the naturality in `B`, which makes the points a natural transformation to
`Module.Grassmannian.functor` on Noetherian affine test schemes, is `HilbertScheme/Naturality`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial TensorProduct

universe u v

namespace AlgebraicGeometry

namespace ProjectiveSpace

open Scheme.Cohomology

variable (ι : Type u) {B : Type u} [CommRing B]

/-- **The rank of `H^0` at a prime is the fiber dimension** when the base-change map to the
residue field is an isomorphism: for a module `M` on `P^n_B` and a prime `p` of `B`,
`rankAtStalk H^0(P^n_B, M) p = dim_{κ(p)} H^0(fiber over p, M)`. -/
theorem rankAtStalk_moduleCohomology_zero_eq (M : (ProjectiveSpace B ι).Modules)
    (p : PrimeSpectrum B)
    (hiso : IsIso (moduleCohomologyBaseChangeMap (toSpec B ι)
      (algebraMap B p.asIdeal.ResidueField) M 0)) :
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace B ι)
      ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) M 0
    ∀ [Module.Flat B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) M) 0)]
      [Module.Finite B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) M) 0)],
    Module.rankAtStalk (R := B) (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) M) 0) p =
      moduleFiberCohomologyDimension (toSpec B ι) M 0 p := fun {_ _} =>
  Module.rankAtStalk_eq_finrank_of_extendScalars_iso.{u, u + 1} p _ _
    (asIso (moduleCohomologyBaseChangeMap
    (toSpec B ι) (algebraMap B p.asIdeal.ResidueField) M 0))

/-- The `B`-module structure of `H^0(P^n_B, M)`, through the structure morphism. -/
abbrev h0Module (M : (ProjectiveSpace B ι).Modules) :
    Module B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) M) 0) :=
  moduleCohomologyModuleOfHom (ProjectiveSpace B ι)
    ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) M 0

/-- The module `H^0(P^n_B, 𝒪(r) ⊗ 𝒪)` of the twisted structure sheaf. -/
abbrev unitTwist (r : ℤ) : (ProjectiveSpace B ι).Modules :=
  (moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι r)).obj
    (SheafOfModules.unit (ProjectiveSpace B ι).ringCatSheaf)

variable [IsNoetherianRing B] (n : ℕ) (e : ι ≃ Fin (n + 1))
  (Z : (ProjectiveSpace B ι).IdealSheafData) {Φ : ℚ[X]}

/-- The restriction map `H^0(P^n_B, 𝒪(r) ⊗ 𝒪) ⟶ H^0(P^n_B, 𝒪_Z(r))`, linear over `B`. -/
abbrev restrictionH0 (r : ℤ) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    letI := h0Module ι (quotientTwist ι Z r)
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (unitTwist (B := B) ι r)) 0 →ₗ[B]
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (quotientTwist ι Z r)) 0 :=
  moduleCohomologyMapOfHom (ProjectiveSpace B ι)
    ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
    (twistedShortComplex ι Z r).g 0

include e in
/-- **The rank of `H^0(𝒪_Z(r))`**: for `Z ⊆ P^n_B` flat over `B` with all fiber Hilbert
polynomials `Φ` and a natural number `r ≥ hilbertRegularityBound n Φ`, the projective module
`H^0(P^n_B, 𝒪_Z(r))` has rank `Φ(r)` at every prime. -/
theorem rankAtStalk_moduleCohomology_quotientTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) (p : PrimeSpectrum B) :
    letI := h0Module ι (quotientTwist ι Z r)
    Module.rankAtStalk (R := B)
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (quotientTwist ι Z r)) 0) p =
        ⌊Φ.eval (r : ℚ)⌋₊ := by
  let := h0Module ι (quotientTwist ι Z r)
  have : Finite ι := Finite.of_equiv _ e.symm
  have hfin : Module.Finite B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
      (quotientTwist ι Z r)) 0) :=
    moduleCohomology_finite_of_proper B (toSpec B ι) _
      (affineLocallyFiniteType_quotientTwist ι n e Z r) 0
  have hproj := projective_moduleCohomology_quotientTwist ι n e Z hfib r hr
  have : Module.Flat B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
      (quotientTwist ι Z r)) 0) := inferInstance
  rw [rankAtStalk_moduleCohomology_zero_eq ι _ p
    (isIso_moduleCohomologyBaseChangeMap_quotientTwist ι n e Z hfib r hr 0 _),
    ← moduleFiberCohomologyDimension_quotientTwist ι n e Z hfib r hr p, Nat.floor_natCast]

include e in
/-- **The rank of `H^0(I_Z(r))`**: for `Z ⊆ P^n_B` flat over `B` with all fiber Hilbert polynomials
`Φ` and a natural number `r ≥ hilbertRegularityBound n Φ`, the projective module
`H^0(P^n_B, I_Z(r))` has rank `C(r + n, n) - Φ(r)` at every prime. -/
theorem rankAtStalk_moduleCohomology_idealTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) (p : PrimeSpectrum B) :
    letI := h0Module ι (idealTwist ι Z r)
    (Module.rankAtStalk (R := B)
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (idealTwist ι Z r)) 0) p : ℚ) =
        ((r + n).choose n : ℚ) - Φ.eval (r : ℚ) := by
  let := h0Module ι (idealTwist ι Z r)
  have : Finite ι := Finite.of_equiv _ e.symm
  have hfin : Module.Finite B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
      (idealTwist ι Z r)) 0) :=
    moduleCohomology_finite_of_proper B (toSpec B ι) _
      (affineLocallyFiniteType_idealTwist ι n e Z r) 0
  have hproj := projective_moduleCohomology_idealTwist ι n e Z hfib r hr
  have : Module.Flat B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
      (idealTwist ι Z r)) 0) := inferInstance
  rw [rankAtStalk_moduleCohomology_zero_eq ι _ p
    (isIso_moduleCohomologyBaseChangeMap_idealTwist ι n e Z hfib r hr 0 _)]
  exact moduleFiberCohomologyDimension_idealTwist ι n e Z hfib r hr p

include e in
/-- **The Grassmannian point of a flat family** (Nitsure, arXiv:math/0504590v1, §5, p. 26): for
`Z ⊆ P^n_B` flat over `B` with all fiber Hilbert polynomials `Φ` and a natural number
`r ≥ hilbertRegularityBound n Φ`, the kernel of `H^0(𝒪(r)) ⟶ H^0(𝒪_Z(r))` is a point of the
Grassmannian of rank-`Φ(r)` quotients of `H^0(P^n_B, 𝒪(r))`: the quotient is `H^0(𝒪_Z(r))`, a
finite projective `B`-module of rank `Φ(r)` at every prime. -/
def grassmannianPoint [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    Module.Grassmannian B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
      (unitTwist (B := B) ι r)) 0) ⌊Φ.eval (r : ℚ)⌋₊ :=
  letI := h0Module ι (unitTwist (B := B) ι r)
  letI := h0Module ι (quotientTwist ι Z r)
  haveI : Module.Finite B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
      (quotientTwist ι Z r)) 0) :=
    have : Finite ι := Finite.of_equiv _ e.symm
    moduleCohomology_finite_of_proper B (toSpec B ι) _
      (affineLocallyFiniteType_quotientTwist ι n e Z r) 0
  haveI := projective_moduleCohomology_quotientTwist ι n e Z hfib r hr
  Module.Grassmannian.ofSurjective (restrictionH0 ι Z r)
    (exact_moduleCohomology_twistedShortComplex ι n e Z hfib r hr).2.2
    (rankAtStalk_moduleCohomology_quotientTwist ι n e Z hfib r hr)

include e in
theorem grassmannianPoint_toSubmodule [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    letI := h0Module ι (quotientTwist ι Z r)
    (grassmannianPoint ι n e Z hfib r hr).toSubmodule = LinearMap.ker (restrictionH0 ι Z r) :=
  rfl

include e in
/-- **The sections of `I_Z(r) ⊆ 𝒪(r)` are the kernel of the restriction to `Z`**: for a flat family
and `r ≥ hilbertRegularityBound n Φ`, a global section of `𝒪(r) ⊗ 𝒪` comes from `I_Z(r)` exactly
when its image in `H^0(𝒪_Z(r))` vanishes. -/
theorem mem_idealTwistSections_iff [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) (s : 𝟙_ _ ⟶ unitTwist (B := B) ι r) :
    s ∈ idealTwistSections ι Z r ↔ restrictionH0 ι Z r (unitHomH0Equiv _ s) = 0 := by
  let α := (toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  have hex := (exact_moduleCohomology_twistedShortComplex ι n e Z hfib r hr).2.1
  have key : s ∈ idealTwistSections ι Z r ↔ unitHomH0Equiv _ s ∈
      Set.range (moduleCohomologyMapOfHom _ α (twistedShortComplex ι Z r).f 0) := by
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨unitHomH0Equiv _ t, (unitHomH0Equiv_comp α t _).symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨(unitHomH0Equiv _).symm y, (unitHomH0Equiv _).injective ?_⟩
      change unitHomH0Equiv _ ((unitHomH0Equiv _).symm y ≫ (twistedShortComplex ι Z r).f) = _
      rw [unitHomH0Equiv_comp α, Equiv.apply_symm_apply]
      exact hy
  exact key.trans (hex _).symm

include e in
/-- **Injectivity of the Grassmannian point** (Nitsure, arXiv:math/0504590v1, §5, p. 26): two
closed subschemes of `P^n_B`, flat over the Noetherian ring `B` with all fiber Hilbert polynomials
`Φ`, with the same Grassmannian point in degree `r ≥ hilbertRegularityBound n Φ`, are equal. -/
theorem eq_of_grassmannianPoint_eq (Z' : (ProjectiveSpace B ι).IdealSheafData)
    [Flat (Z.subschemeι ≫ toSpec B ι)] [Flat (Z'.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (hfib' : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z' p) = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    grassmannianPoint ι n e Z hfib r hr = grassmannianPoint ι n e Z' hfib' r hr → Z = Z' := by
  let := h0Module ι (unitTwist (B := B) ι r)
  let := h0Module ι (quotientTwist ι Z r)
  let := h0Module ι (quotientTwist ι Z' r)
  intro h
  have hker := congrArg Module.Grassmannian.toSubmodule h
  rw [grassmannianPoint_toSubmodule, grassmannianPoint_toSubmodule] at hker
  refine eq_of_idealTwistSections_eq ι n e Z Z' hfib hfib' r hr (Set.ext fun s => ?_)
  rw [mem_idealTwistSections_iff ι n e Z hfib r hr, mem_idealTwistSections_iff ι n e Z' hfib' r hr,
    ← LinearMap.mem_ker, ← LinearMap.mem_ker, hker]

end ProjectiveSpace

end AlgebraicGeometry
