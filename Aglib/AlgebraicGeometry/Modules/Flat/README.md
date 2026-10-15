# Genuinely stalkwise-flat module sheaves

[Generators](Generators.lean) constructs actual open-free generators and their flat-stalk properties. [Locality](Locality.lean) compares open-restricted module stalks with scalar restriction along the actual stalk-ring isomorphism, giving the stated flatness transport.

[Pullback](Pullback.lean), imported as `Aglib.AlgebraicGeometry.Modules.Flat.Pullback`, treats arbitrary scheme morphisms on actual stalkwise-flat objects. An actual short exact sequence with flat quotient stays short exact under extension of scalars, and the sheaf pullback result uses those genuine stalk hypotheses. Flatness of the scheme morphism is not assumed for that flat-quotient interface.

These results feed local generators, extension-by-zero and arbitrary pullback on the appropriate flat-object exact sequences. [Flat-morphism exactness for arbitrary coefficients](../Pullback/README.md) is a separate interface. No flatness property is inferred from a module-sheaf object's name.
