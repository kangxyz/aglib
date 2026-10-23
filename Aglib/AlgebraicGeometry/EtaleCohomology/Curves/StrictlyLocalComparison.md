# Original strictly local finite-over-projective-line comparison

## Final theorem

The source is [StrictlyLocalComparison](StrictlyLocalComparison.lean). Import
`Aglib.AlgebraicGeometry.EtaleCohomology.Curves.StrictlyLocalComparison`.
In namespace `AlgebraicGeometry.Scheme.EtaleCohomology.Curves`, the endpoint is
`finite_projectiveLine_constantRestriction_surjective`.

For `R : Type u`, `[CommRing R]`, `[HenselianLocalRing R]`, and
`[IsSepClosed (IsLocalRing.ResidueField R)]`, take a native scheme `Y`,
`f : Y ⟶ ProjectiveLine.projectiveP1 R`, and `[IsFinite f]`. For every
`A : Type u` with `[AddCommGroup A] [Finite A]` and every `q : ℕ`, the theorem
proves surjectivity of

```lean
constantRestriction A
  (pullback.fst (f ≫ ProjectiveLine.structureMap R)
    (LocalRing.residueSpecMap R)) q
```

This is the original cohomology pullback followed by the native constant-sheaf
transport, not a replacement cohomology model. Source and target use standard
coefficient value universe `u + 1`, with independent `HasExt.{w}` on
`AbelianSheaf Y` and `HasExt.{w'}` on `AbelianSheaf (residueFiber f)`.
The closed fibre and its inclusion are the literal native categorical pullback.

There is no Noetherian, excellent, complete, flat, finite-presentation, normal, reduced,
smooth, coefficient-order invertibility or arithmetic-marking premise on the
final endpoint. It asserts all-degree **surjectivity**, not higher injectivity
or general proper base change. Existing H0/H1 bijections are reused.

## Proof architecture

1. The literal closed fibre is a proper finite-type scheme of dimension at most
   one over the separably closed residue field.
2. For a positive invertible cyclic level, degrees zero and one use the native
   existing comparison. Degree two uses the proved original Picard–Kummer
   boundary and actual henselian Picard lifting, with their original naturality
   square. In higher degrees the target vanishes by B2.
3. Residue-characteristic-primary coefficients have zero target above degree
   one by B3. Artin–Schreier is applied on the characteristic-p fibre, never
   asserted on a mixed-characteristic total scheme.
4. Genuine finite-abelian split primary decomposition and actual coefficient
   transports combine the two branches. Root trivializations are constructed,
   not assumed in the final statement.

B1 supplies the actual arbitrary-quasi-coherent etale/Zariski comparison and
Frobenius/additive naturality. B2 includes genuine Tsen/function-field theory,
original finite-coefficient dimension shifting, generic higher images, and
finite-support exhaustion. No Brauer vanishing, support acyclicity, or desired
comparison statement remains as an extra mathematical premise.
