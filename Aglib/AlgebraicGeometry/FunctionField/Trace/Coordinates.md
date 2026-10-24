# Original trace-coordinate and adjugate sheaf maps

This module constructs the original trace-coordinate and adjugate sheaf
maps using `Trace/Sheaf`, `Trace/Transport` and `IntegralClosure/TraceLattice`.
It does not by itself assert the whole H¹ bound.

The namespace is
`AlgebraicGeometry.Scheme.Modules.FiniteTraceCoordinates`.

Fix commutative domains `A,B`, the original finite `A`-algebra structure on
`B`, a faithful original scalar action, and integral closedness of `A`.
Faithfulness here expresses injectivity of the original algebra map; it is
not a flatness condition. The base map is literally
`Spec.map (CommRingCat.ofHom (algebraMap A B))`.

The fixed fields are the literal `(Spec A).functionField` and
`(Spec B).functionField`, exposed through the typed abbreviation
`spectrumField`, whose domain hypothesis supplies the required irreducible
spectrum. Their extension action is the original generic-stalk
map of that base morphism. The `A`-action on the upper field is the original
composite `A → B → L`; native affine generic-stalk naturality proves the
second scalar tower. These structures are installed before any model is
introduced. `degree`, `fixedBasisElement`, `fixedDiscriminant` and
`fixedAdjugateElement` abbreviate the same fixed TraceLattice data. The last
is the original lattice adjugate expansion evaluated at `Pi.single i 1`.

Now take actual integral schemes `X,Y`, a finite dominant `π : Y ⟶ X`, normal
stalks on `X`, dominant maps `a : X ⟶ Spec A`, `b : Y ⟶ Spec B`, isomorphisms
on their original function-field maps, and the original square

`π ≫ a = b ≫ baseMap A B`.

Neither `a` nor `b` needs a properness hypothesis for this producer. There is
no local freeness or flatness assumption on `π`, no source regularity or
normality assumption on `Y`, and no dimension, local-ring, Noetherian or
Nagata hypothesis. Separability of the original `L/K` is needed only by the
monicity theorem.

Put `F = π_*O_Y` using the literal `pushforwardStructureSheaf π` and let
`P = target A B (X := X)`, the native finite biproduct of `degree A B` copies
of the original structure module `O_X`. Write `α` and `β` for the original
structural ring homomorphisms obtained from `a.appTop`, `b.appTop` and the
corresponding inverse `ΓSpecIso`.
The typed abbreviations `structureModule` and `directImageStructure` keep
these same objects in `X.Modules`; the finite biproduct is formed explicitly
in that native category.
The typed abbreviation `structureScalar` is that original ring homomorphism;
it does not replace the structural action with a chosen isomorphic action.

The public maps are:

* `generator B π b r : O_X ⟶ F`: the original structure-unit map, followed by
  pushforward of `unitMul Y (β r)`.
* `coordinate A B π hX b i : F ⟶ O_X`: pushforward multiplication by
  `β (fixedBasisElement A B i)`, followed by the original finite
  structure trace.
* `coordinates A B π hX b : F ⟶ P`: the native biproduct lift of those maps.
* `adjugateExpansion A B π b : P ⟶ F`: the native biproduct descent of the
  original generators of the fixed adjugate columns.

`coordinates_π` and `ι_adjugateExpansion` identify their actual components.
The source does not replace the biproduct by a new coordinate object or
introduce a separate trace framework.

The scalar normalization is public and independent of the extra field
hypotheses. `scalar_square A B π a b hsq` states exactly

`π.appTop.hom.comp (a.appTop.hom.comp ΓSpecA.inv.hom) =`
`(b.appTop.hom.comp ΓSpecB.inv.hom).comp (algebraMap A B)`.

It is derived from the original square by the existing structural
base-change identity. This is the equation required to identify the
cohomology action induced through `π` with restriction of the original
`B`-action; no cohomology construction is made in this file.

`trace_originalConstant` proves that the trace of `β r` is
`α (TraceLattice.fieldTrace r)`. The proof compares the original section
germs and invokes `functionFieldTrace_birational_square` on the actual
field maps of `a,b,π`. There is no trace-compatibility premise.

The two public identities are

* `adjugateExpansion_comp_coordinates`: `Ξ ≫ Φ` is
  `globalScalarEndomorphism X P (α d)`;
* `coordinates_comp_adjugateExpansion`: `Φ ≫ Ξ` is
  `globalScalarEndomorphism X F (α d)`.

Here `d = fixedDiscriminant A B` is the same base element chosen before
the model. Both identities are proved without separability. The first is
checked on native biproduct components using the actual constant-trace
equation and the lattice identity. For the second, the native
adjugate identity is checked on the fixed field basis and extended linearly
to all of `L`. Original function-field naturality and the trace
transport give the equality on every nonempty original open. The original
empty-open section property handles the remaining case.

Finally, `coordinates_mono` assumes actual separability of this original
field extension. The lattice theorem makes `d` nonzero. Dominance
of `a` and `π` makes its original pullback nonzero. Multiplication by that
section is monic on the direct image of the integral source's structure
module. Cancelling this actual scalar composite proves monicity of `Φ`.
The proof never divides by the field degree or assumes the scalar is a unit.

The geometric consumer is the separable branch of the original surface H¹
bound. The finite-domination construction, finite-pushforward cohomology
comparison and final length inequality have separate owners. No resolution,
cohomology-bound, conductor or supplied comparison data occurs as a premise
of these sheaf-map identities.
