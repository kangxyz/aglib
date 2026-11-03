# Finite point-blowup resolution with explicit initial inputs

API: [exists_regular_pointBlowupChain_of_empty_singularPrefixes](FiniteResolution.lean#L37), [exists_regular_pointBlowupChain_of_initial_cones_of_complete_base](FiniteResolution.lean#L148).

Let `R` be a commutative Noetherian Nagata local domain of dimension two
with `NormalModificationH1Vanishing R`.
Let `f : X ⟶ Spec R` be proper and dominant, with `X` integral and normal
and the original `functionFieldMap f` invertible.

`exists_regular_pointBlowupChain_of_empty_singularPrefixes` takes, at every
original singular `x`, a witness `∃ n, IsEmpty (SingularPrefix X x n)`.
It constructs `g : Y ⟶ X` and `c : PointBlowupChain g` with regular
terminal `Y` and proved `c.NormalStages`. For every original open `U ⊆ X`
whose stalks are regular, the literal restriction `g ∣_ U` is an isomorphism.

The proof derives finiteness of the singular set, then uses the existing
Dershowitz–Manna well-founded relation on its singular-height multiset.
Each singular-point blowup has normal entire source by rational blowup
geometry. `PointHeight` compares heights over the centre and its complement;
`HeightMultiset` retains multiplicities and proves the strict decrease.
The recursion uses the original maps and proves normal stages at the
chain constructors. The centre misses every original regular open, and
restriction composition preserves its actual isomorphism.

`exists_regular_pointBlowupChain_of_initial_cones_of_complete_base` supplies
the empty levels from the following additional inputs:

- At each original singular stalk, a generating triple `(t,g₀,g₁)` and a
  nonzero homogeneous quadratic `q` over its original residue field, with
  the entire `CaseOne.canonicalConeMap t g` kernel equal to `Ideal.span {q}`.
- A commutative local domain `A`, complete for its maximal ideal and of
  dimension two, and a local injective `a : A →+* R` with finite
  `ResidueField.map a`. No Noetherian assumption on `A` is added.

For a selected stalk the map is exactly `(f.stalkScalar x).comp a`; the
original closed-base stalk and residue squares prove locality, injectivity
and finite residue extension there. `FiniteHeight` then constructs its
empty level. Future cones, markings and terminal regularity are not inputs
to this geometric endpoint.

The initial full cones remain supplied hypotheses. Recognizing them from
arbitrary rational or rational-Gorenstein data is a separate mathematical
obligation. `NormalizedResolution` consumes the ordinary chain's proved
normal stages and its explicit normalized terminal presentation.

Present consumers: [NormalizedResolution](NormalizedResolution.md).
