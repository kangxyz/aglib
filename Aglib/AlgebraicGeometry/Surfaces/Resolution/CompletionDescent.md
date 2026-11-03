# Descent of a prescribed normalized point-blowup chain

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.CompletionDescent`.
Source: [CompletionDescent.lean](CompletionDescent.lean).
The declarations are in `AlgebraicGeometry.Scheme.Blowup`.

Let `A` be a commutative Noetherian local domain of dimension two and
`H := AdicCompletion (maximalIdeal A) A` its literal completion.
The endpoints assume both `IsDomain H` and `IsIntegrallyClosed H`.
Write `c := LocalRing.completionSpecMap A : Spec H ⟶ Spec A`.

`exists_completionDescent_chain` takes a supplied finite
`upper : NormalizedPointBlowupChain g` for `g : Y ⟶ Spec H`.
It constructs `f : X ⟶ Spec A` and a literal lower chain of the same length.
The terminal `X` is integral, `f` is proper and dominant, and its original
function-field map is an isomorphism.
An explicit `E : Y ≅ pullback f c` satisfies both original equations:

`E.hom ≫ pullback.snd f c = g`,

`E.hom ≫ pullback.fst f c ≫ f = g ≫ c`.

`exists_completionDescent` additionally takes `RegularStalks Y` and
concludes `RegularStalks X`, with the same length and projection equations.

The public induction `descend_normalizedChain_from_model` starts from an
integral lower model `f : X ⟶ Spec A` which is proper and dominant with
invertible original function-field map, a specified
`e : Y ≅ pullback f c`, `NormalStalks Y`, and a supplied chain `g : Z ⟶ Y`.
This more general induction needs `IsDomain H`; normality is supplied on
`Y` rather than assumed on all of `Spec H`. It returns a lower chain
`h : T ⟶ X` of the prescribed length and a comparison over `h ≫ f`,
retaining its equations to both original projections.

At each step the given upper point determines its lower image through the
actual model comparison. The residue-field pullback square uses the original
residue map and proves equality of the full point ideals. Flat ordinary
blowup base change gives the ordinary comparison. Normality off the upper
centre supplies the hypothesis of the normalization comparison, which derives
finite lower normalization and hence properness. The induction retains both
projection equations before continuing. Terminal regularity descends along
the actual flat local stalk maps of the faithfully flat completion projection.

The upper chain remains an input. There is no excellence, G-ring or Nagata
hypothesis on `A`, and no complete-local resolving-chain existence or
global spreading conclusion.

The prescribed-chain descent corresponds to
[Stacks Lemma 54.11.7, tag 0BGA](https://stacks.math.columbia.edu/tag/0BGA).
Its lower comparisons are
[CompletionNormalization](../../Descent/CompletionNormalization.md) and
[CompletionPointBlowup](../../Descent/CompletionPointBlowup.md).
The present consumer is
[rationality under completion](../RationalSingularities/Completion.md),
which uses the arbitrary-terminal chain theorem.
