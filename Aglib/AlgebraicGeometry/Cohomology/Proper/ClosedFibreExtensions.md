# Correcting lifts in closed-fibre extensions

Let `A` be a commutative Noetherian normal local domain of dimension at
least two, let `X` be a scheme, and let `α : A →+* Γ(X, ⊤)` be a bijective
structural coefficient map. Write `O` for the native structure module,
`m` for the original maximal ideal, and

```lean
I := Modules.idealMultiple X α O m
Q := Modules.idealQuotient X α O m
```

The inclusion `ι : I ⟶ O` is the image inclusion of scalar evaluation.
The quotient `q : O ⟶ Q` is its actual cokernel. In particular, this
construction does not assert that tensoring `m ↪ A` is injective.

`Modules.maximalIdealMultipleHom_eq_scalar` proves that every map
`c : I ⟶ O` has the form
`ι ≫ globalScalarEndomorphism X O (α a)` for an original scalar `a : A`.
For `b ∈ m`, the canonical map `O ⟶ I` followed by `c` is an endomorphism
of `O`, hence a global section. Bijectivity of `α` identifies it with an
original scalar `t(b)`. These scalars define an `A`-linear map `m → A`.
The native maximal-ideal dual theorem gives `t(b)=a*b`. The original ideal
generators jointly detect morphisms from `I`, giving equality of sheaf
maps. No faithfulness of global sections is assumed.

`Modules.closedFibreExtension_section_of_lift` takes an actual short exact
extension

```text
0 → O --j→ E --p→ Q → 0
```

and a concrete morphism `s : O ⟶ E` with `s ≫ p = q`. Multiplication of
this lift by the ideal factors through `j`, giving `c : I ⟶ O`. Choose
the scalar `a` supplied above. The corrected map
`s - globalScalarEndomorphism X O (α a) ≫ j` annihilates `I` and therefore
descends through `q`.
Its descent is a section of the original projection `p`.

`Modules.closedFibreExtension_section_of_proper_birational_lift` supplies
bijectivity of the literal structural coefficient map

```lean
f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
```

for a proper dominant birational `f : X ⟶ Spec A` with integral source
and normal target. It retains the original function-field map. For this
map, `idealQuotientThickeningIso` in `Modules/IdealPowers/Thickening`
identifies `Q` with the pushed-forward structure module of the actual
closed fibre, preserving the quotient and geometric unit.

This is the corrected-lift step in
[Stacks Project, Lemma 54.7.6 (0AXC)](https://stacks.math.columbia.edu/tag/0AXC).
That lemma additionally obtains the lift from punctured-spectrum H1
injectivity for a normal modification of a two-dimensional normal Nagata
local domain. The present theorem assumes the concrete lift, and does not
assert that geometric injectivity, derived residue-field Hom vanishing,
Grauert–Riemenschneider vanishing, or surface resolution. It needs no
derived-unit construction or duality theorem.
