# Conditional transgression to native continuous H1

[Basic](Basic.lean) uses the existing continuous H1 cocycle, coefficient-map and
quotient types. Its `Kernel` is the actual additive kernel of the supplied
continuous equivariant differential `d`, with its subspace topology and the
restricted action. For an invariant value and a supplied lift, the cocycle is
`g ↦ η (g • y - y)`. Changing lifts produces the native principal cocycle of
the positive difference `η (y - y')`.

`SourceData` supplies only the actual source cochain maps `pull₀`/`pull₁`, their
degree-zero differential square, invariant degree-zero/one images and
liftability. The additive map on source H1 is constructed from those data.
An actual chain map and supplied vanishing of the closed-source H1 give a
constructor, while invariance and that vanishing remain inputs. The source
additive groups require no topology. The acting group retains the topology
needed by the native H1 construction; continuity of group multiplication is
not added where it is unused.

[Naturality](Naturality.lean) retains the continuous group homomorphism,
relative coefficient maps, differential square, literal degree-zero/one source
squares and eta compatibility on the actual kernels. Naturality of the
constructed H1 map follows from displacement and lift independence.
[FiniteNaturality](FiniteNaturality.lean) uses literal coefficient reduction and
insertion chain maps on the existing termwise quotients. Insertion has
representative `q • x`; the cone corollaries use the existing positive
first-component projection without requiring an inverse.

These constructions do not supply the invariance, liftability, vanishing or
source-square data for a geometric, motivic or arithmetic application.
