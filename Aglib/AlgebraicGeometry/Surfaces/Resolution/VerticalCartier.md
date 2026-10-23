# Nontrivial conormal of a vertical Cartier divisor

`Scheme.VerticalCartier.conormal_not_trivial_of_vertical_cartier`
proves the conormal obstruction in
[Stacks 0AXA](https://stacks.math.columbia.edu/tag/0AXA) for the original
closed immersion and its original ideal module.

The base is a commutative Noetherian normal local domain `A` with
`ringKrullDim A = 2`. The original map `q : X → Spec A` is proper and
dominant, `X` is integral and has normal stalks, and the original
function-field map of `q` is an isomorphism. The original closed
immersion `i : Z → X` is nonempty and its actual ideal module is locally
rank one. Set-theoretic verticality is the explicit original point
identity `q (i z) = closedPoint A` for every `z : Z`.

The conclusion is exactly

```
¬ Nonempty ((Modules.pullback i).obj (Hom.idealModule i) ≅
  SheafOfModules.unit Z.ringCatSheaf)
```

There is no regularity, excellence, coefficient-field, perfectness,
rational-point, component-splitting, intersection-form or resolution
hypothesis. The Cartier scheme may be nonreduced; its integral reduced
support components may be singular over an imperfect residue field.

The construction uses the native reduced closed subscheme of each
original support component, with actual maps to the original divisor
and original closed fibre. A closed vertical point of ambient coheight
one would be isolated in the connected fibre, forcing an isomorphism
neighborhood and contradicting the base dimension. This supplies the
nonfield closed-point choices used in the original common-function
construction of [Stacks 0AX9](https://stacks.math.columbia.edu/tag/0AX9).
The base-to-stalk maps, common function and local factorizations are
retained explicitly.

Actual DVR valuations at the component generic points choose common
positive powers. The normal-domain height-one membership theorem is
applied at every height-one prime, including points outside the support
where the Cartier ideal is the unit ideal. Sheaf separation constructs
an actual global section of the original ideal power, generating at one
original component generic point.

At its isolated closed point, the radical of the original stalk ideal
is the original component-inclusion kernel. It is prime, and the chosen
nonzero component image avoids it. Height-one cancellation therefore
places the section germ in the maximal ideal times the actual ideal
power. The canonical ideal-section/stalk comparison proves that the
same pulled section is nonzero and fails to be an isomorphism.

Proper integral schemes have a field of actual global functions. Thus
a trivial line with a nonzero section cannot have that failure of
invertibility. Native ideal multiplication and tensor pullback carry
any original conormal trivialization to the forbidden trivialization
of the ideal-power restriction to the selected component.

The proof does not infer triviality on the thickened divisor from
triviality on the original divisor; it uses only restriction to the
original integral component. It neither defines a degree for singular
curves nor asserts the stronger positive-degree refinement. Construction
and termination of an initial surface resolution remain separate.
