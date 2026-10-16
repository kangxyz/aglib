# Object properties in actual abelian exact sequences

[ExactFive](ExactFive.lean) proves
`ObjectProperty.prop_middle_of_exact_five` for an exact row of five actual
objects. The four outside objects have the property; the middle one then
has it if the property is stable under isomorphisms, kernels and cokernels
of maps between known objects, and extensions. Arbitrary subobject or
quotient closure is unnecessary.

The proof uses the original middle short complex's actual cycles and
opcycles. Exactness of the adjoining rows realizes those objects as the
cokernel and kernel of maps between the known outside objects. The native
cycle/opcycle short exact sequence finishes the extension argument.
Category and morphism universe levels are independent.

The exact leaf passed with receipt `1792114596854744000-21935` in
1.8 seconds. `ExactFiveObjectPropertyConsumer.lean` passed with receipt
`1792114715029170000-23722`, retaining exactly these four closure classes.
The inspected theorem uses only the three standard axioms. Native coherent
derived homology consumes this statement without an unsupported ambient
Serre-class assumption.
