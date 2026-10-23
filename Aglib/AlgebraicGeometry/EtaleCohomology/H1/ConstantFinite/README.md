# Finite constant coefficients over proper henselian local bases

The declarations use the actual coefficient
`(constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u+1}).obj
(AddCommGrpCat.of (ULift.{u+1} A))` for a finite additive commutative group
`A : Type u`. Its finite local trivialization uses the identity chart, and its
representing group object uses the literal finite coproduct of identity covers.

For any henselian local ring `R` and proper `p : X ⟶ Spec R`, write
`i := pullback.fst p (LocalRing.residueSpecMap R)` for the original
closed-residue fibre arrow. The original pullback maps are bijective:

| Map | Original cohomology object |
| --- | --- |
| `properHenselian_pullbackSections_bijective` | Global sections of the actual constant sheaf, after the canonical `inverseImageConstantIso`. |
| `properHenselian_pullbackH0_bijective` | Original `Sheaf.H` in degree zero, with its canonical constant-inverse-image comparison. |
| `properHenselian_pullbackH1_bijective` | Original `H1Etale`, after the same coefficient comparison. |

Section bijectivity needs no Ext hypothesis. H0 and H1 keep separate explicit
source and target `HasExt` universes at value universe `u+1`. No order
invertibility, Noetherian, finite-presentation, excellence, completion,
flatness, residue-field-closure, marking, Galois-category, or
fundamental-group premise is required. The proof uses the native proper
henselian finite-etale base-change equivalence internally; it is discharged
in the endpoint and is not a theorem premise.

The H1 proof represents each original class by an actual finite-etale scheme
with its actual torsor action. It descends the action and its difference maps,
proves the torsor laws on finite universal products and then on every
scheme-valued test object, and proves carrier surjectivity separately. The
native torsor class comparison yields surjectivity of the original H1 map;
finite-etale fullness supplies injectivity.

The same construction gives H1 bijectivity for every actual finite locally
constant abelian sheaf, without an order-invertibility condition. The H0 owner
also supplies original sections bijectivity for every such sheaf. These are
bounded finite-coefficient results, not arbitrary-sheaf proper base change.
