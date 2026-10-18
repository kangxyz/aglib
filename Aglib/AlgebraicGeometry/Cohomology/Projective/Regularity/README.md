# Castelnuovo–Mumford regularity on polynomial projective space

`Basic` defines `Scheme.Cohomology.IsProjectiveRegular R ι F m`: the original
cohomology `Sheaf.H` of the native tensor twist `O(m - q) ⊗ F` vanishes in every
positive degree `q` (Nitsure, arXiv:math/0504590v1, §2, p. 9, before Lemma 2.1;
Stacks, Tag 08A3). The base is an arbitrary
commutative ring and `ι` an arbitrary coordinate type in the base universe.

`exists_isProjectiveRegular` proves that every coherent module on projective
`n`-space over a Noetherian ring, with a labeling `ι ≃ Fin (n + 1)`, is
`m`-regular for some integer `m`. It combines `projectiveSerreVanishing` in the
degrees `1 ≤ q ≤ n` with `projectiveCohomology_subsingleton_of_gt` above `n`.

`CoordinateGeneration` starts the routes to Lemma 2.1. Nitsure and Stacks, Tags
08A6–08A7, prove (a) and (b) by hyperplane sections over an infinite field; the routes
here are different proofs of the same statements. Their (c) step (Tag 08A8) is a large
twist plus (a), the same route as `GlobalGeneration` below. For finitely many
coordinates, `coordinateMultiplicationSum` is the sum of the coordinate
multiplications `∐ᵢ O(0) ⊗ F → O(1 + 0) ⊗ F`. The instance
`epi_coordinateMultiplicationSum` proves it is an epimorphism for every module
`F` over every commutative base. Its cokernel is killed by every coordinate, so
it is zero by the Hilbert-polynomial family's `isZero_of_coordinate_eq_zero`.
This epimorphism is the last map of the Koszul complex of the coordinates
tensored with `F`. Twist multiplication with a free target degree,
`twistingTensorMultiplyTo a d d' h s` for `h : a + d = d'`, and the commutation
`twistingTensorMultiplyTo_comm` behind `d² = 0` for the Koszul differentials live in
[FreeDegree](../../../ProjectiveSpace/Tensor/Monoidal/FreeDegree.lean), with the other
free-degree comparisons; `CoordinateGeneration` re-exports that leaf.

`Monotone` proves Nitsure, Lemma 2.1 (b) (p. 10): an `m`-regular module is
`m'`-regular for every `m' ≥ m` (Stacks, Tag 08A6, Lemma 33.35.10, states the
step `m ↦ m + 1` for coherent sheaves over a field).
`IsProjectiveRegular.of_le` works over every commutative ring, for a labeling
`ι ≃ Fin (n + 1)` and a quasicoherent module (its twists are then quasicoherent,
`twistingTensor_isQuasicoherent`); `IsProjectiveRegular.of_le_of_coherent` takes an
affine-locally finite-type module instead, again over any commutative ring. The
corollary `IsProjectiveRegular.cohomology_subsingleton_of_le` (and `_of_coherent`)
is the vanishing half of Lemma 2.1 (c): `H^i(O(r) ⊗ F) = 0` for every `r ≥ m` and
`i ≥ 1`. The proof uses neither hyperplane sections nor the Koszul
complex. The epimorphism `epi_coordinateMultiplicationSum` gives the short exact
syzygy sequence `0 → Ω G → ∐ᵢ O(0) ⊗ G → O(1 + 0) ⊗ G → 0` for every module `G`
(`coordinateSyzygy`). With `IsProjectiveRegularFrom G m k` (vanishing of
`H^q(O(m - q) ⊗ G)` for `q ≥ k`), the long exact sequence gives
`IsProjectiveRegularFrom.syzygy` (degree `k` for `G` to degree `k + 1` for `Ω G`)
and `IsProjectiveRegularFrom.succ` (`m` to `m + 1`), by a downward induction on `k`
from the coordinate-cover bound above `n`. Quasicoherence of the twists of `Ω G`
(`coordinateSyzygy_twist_isQuasicoherent`) is all that the bound needs. The
cohomology-vanishing steps along short exact sequences are the
`moduleCohomology_subsingleton_*` lemmas of
[Cohomology/Exact/Modules](../../Exact/Modules.lean).

`Koszul` constructs the Koszul complex of the coordinates for linearly ordered
finite `ι`: `koszulTerm t p = ∐_{|J| = p} O(t - p) ⊗ F`, the contractions
`koszulContraction` with signs `koszulSign`, and the differential
`koszulDifferential` with `koszulDifferential_comp : d ≫ d = 0`. The wedges
`koszulWedge` are a null-homotopy of coordinate multiplication between adjacent
twists in every positive degree (`koszul_homotopy`). Every degree equation in its
definitions and statements is one of the named lemmas `koszulDeg_contraction`,
`koszulDeg_shift`, `koszulDeg_wedge`, and every derived index set is
`koszulIndexErase` or `koszulIndexInsert`, so all occurrences of a coordinate
multiplication, transport or summand inclusion carry the same proof terms. With
inline proofs instead, the kernel unfolded the module-sheaf compositions when
comparing such terms: the leaf took about six minutes, and a restated lemma of the
exactness step took 114 s and 25 GB in the kernel. It now compiles in 6.4 s at a
peak of 2.5 GB ([performance notes](../../../../../doc/PERFORMANCE.md)).

`KoszulExact` proves that the Koszul complex is exact, for every module over
every commutative base: `epi_koszul_kernelLift` (`K_{p+2}` maps onto the kernel of
`K_{p+1} → K_p`) and `epi_koszulDifferential_zero` (`K_1 → K_0` is an
epimorphism). A coordinate is a morphism `coordinateUnitHom i : 𝟙_ ⟶ O(1)` and
multiplies by `unitMultiply`; `twistingTensorMultiply_app_eq_unitMultiply` (in
`FreeDegree`) is the bridge to `twistingTensorMultiply`, and
`isZero_of_unitMultiply_coordinate_eq_zero` the vanishing criterion. The summandwise inverse composition isomorphisms
`koszulTwistInv : K_p(t + 1) ⟶ O(1) ⊗ K_p(t)` turn `unitMultiply` into coordinate
multiplication (`unitMultiply_koszulTerm`) and commute with the differentials
(`koszulDifferential_comp_twistInv`); with `koszul_homotopy` and
`koszul_homotopy_zero` the homology is killed by every coordinate
(`epi_of_unitMultiply_factor`). The composition isomorphisms enter as
`twistMerge`/`twistMergeInv` of `FreeDegree`, with declared types in the monoidal
spelling, so spelling conversions are checked once at variable degrees. Whiskering
uses the `MonoidalPreadditive` instance of scheme modules
([Modules/Tensor/Monoidal](../../../Modules/Tensor/Monoidal/Basic.lean)); only
`moduleWhiskerLeft_zsmul` remains local, since Mathlib has no `zsmul` form.

`Surjectivity` proves Nitsure, Lemma 2.1 (a) (p. 10; Stacks, Tag 08A7, Lemma
33.35.11): for a quasicoherent `m`-regular module and `r ≥ m`, the sum of the
coordinate multiplications `Γ(∐ᵢ O(r) ⊗ F) → Γ(O(1 + r) ⊗ F)` is surjective
(`IsProjectiveRegular.surjective_coordinateMul`, any commutative base,
`ι ≃ Fin (n + 1)`; `_of_coherent` for affine-locally finite-type modules, any
base). With global sections as morphisms out of the unit,
`IsProjectiveRegular.exists_eq_sum_coordinateMul` writes every
`s : 𝟙_ ⟶ O(1 + r) ⊗ F` as `∑ᵢ tᵢ ≫ Xᵢ`. Since the `Xᵢ` are global sections of
`O(1)`, this implies Nitsure's form, surjectivity of
`H⁰(O(1)) ⊗ H⁰(O(r) ⊗ F) → H⁰(O(1 + r) ⊗ F)`. The short exact sequences of Koszul cycles at twist `r + 1`
and `r`-regularity give `H^{p+1}(ker (K_{p+1} → K_p)) = 0` by a downward induction
from above the dimension (`koszulCycles_cohomology_subsingleton`), hence
surjectivity of `K_1 → K_0` on global sections
(`koszulDifferential_zero_surjective`, through Mathlib's
`Sheaf.H.longSequence_equiv₀_exact₃`). The degrees of the Koszul terms are
transported to `r` and `1 + r` only at the level of the surjectivity statement
(`CoordinateMulSurjective.congr`).

`GlobalGeneration` proves the global-generation half of Nitsure, Lemma 2.1 (c)
(p. 10; Stacks, Tag 08A8, Lemma 33.35.12): for an affine-locally finite-type
`m`-regular module over any commutative base and `r ≥ m`, `O(r) ⊗ F` is generated by
its global sections. Lemma 2.1 (c) states exactly the conjunction of this with the
vanishing `H^i(O(r) ⊗ F) = 0` for `i ≥ 1` and `r ≥ m`, which is
`IsProjectiveRegular.cohomology_subsingleton_of_le_of_coherent` of `Monotone`; the
test states the conjunction. Global sections are morphisms `𝟙_ ⟶ M`, and
`globalSectionsEval M : ⨁_{s : 𝟙_ ⟶ M} 𝟙_ ⟶ M` is their evaluation
([Modules/Generators/GlobalSections](../../../Modules/Generators/GlobalSections.lean));
`IsProjectiveRegular.epi_globalSectionsEval` states that it is an epimorphism,
`IsProjectiveRegular.nonempty_generatingSections` packages it as Mathlib's
`SheafOfModules.GeneratingSections`, and
`IsProjectiveRegular.exists_generatingSections_isFiniteType` gives a finite
generating family, `∃ σ, σ.IsFiniteType`: `O(r) ⊗ F` is a quotient of a finite free
module. The large-twist presentation `exists_uniformNegativeTwistEpimorphism` makes
`O(N) ⊗ F` globally generated, by finitely many sections, for some `N ≥ r`
(`epi_globalSectionsEval_of_negativeTwist`,
`exists_finite_epi_sigmaDesc_of_negativeTwist`), and Lemma 2.1 (a) lets generation
descend from `O(1 + c) ⊗ F` to `O(c) ⊗ F` for `c ≥ m`
(`epi_globalSectionsEval_of_succ`, `exists_finite_epi_sigmaDesc_of_succ`):
`O(1) ◁ ev` is an epimorphism, and whiskering by a twisting sheaf reflects
epimorphisms (`epi_of_twisting_whiskerLeft`). The sources prove their (c) step the
same way, from a large twist and (a).

## Open

- Mumford's bound (Nitsure, Thm 2.3, p. 11) is not formalized.
- Nitsure's literal form of (a), surjectivity of the multiplication map on the
  tensor product `H⁰(O(1)) ⊗ H⁰(O(r) ⊗ F)`, is not stated: Aglib has no bilinear
  global-section multiplication map. The coordinate forms above imply it.
- The internal Koszul and syzygy lemmas still take the hypothesis that every twist
  is quasicoherent; the main statements take `[F.IsQuasicoherent]` or
  affine-local finite type.
