# Inertia extension on the literal affine normalization

[Basic](Basic.lean) imports the new lower
[`Algebra.FiniteEtale.InertiaTorsor`](../../../RingTheory/FiniteEtale/InertiaTorsor.lean)
constructors. The lower leaf owns the five algebra-valued fixed-point, H1, and
identified-class endpoints. It reuses the frozen coefficient-inertia,
every-embedding normalization, and algebraic torsor-extension proofs.

The scheme interface belongs to `Scheme.FiniteEtale.InertiaTorsor`.
`structureMap` is exactly `Spec.map (algebraMap R B)`, and `affine` is its native
`Over` object. `cover` uses the existing `Scheme.FiniteEtale` type. In particular,
`normalizationCover` has total scheme `Spec (integralClosure R A)` and the
original structural map. Finite etaleness follows from the actual class's
inertia restriction, and surjectivity follows from the derived faithful
flatness. `normalizationGenericPoint` restricts the original algebra point to
that same integral closure.

`specTransporterPair` is the actual pullback pair of first projection and
coaction. Its equality with the coordinate transporter and its isomorphism
property are proved. `normalization_generic_square` is the contravariant Spec
image of the fixed canonical original-algebra square. The tensor carriers,
coordinate maps, and arrow directions are retained.

For a supplied `HopfAlgebra R H` and `Coalgebra.IsCocomm R H`, Mathlib's
`hopfSpec` gives `coefficientGroup` on the actual `Spec H`. The algebraic coaction
and transporter construct the existing `CategoryTheory.TorsorAction`.
`schemeTorsorAction` and `normalizationSchemeAction` quantify over every
scheme-valued test object; the test object need not be affine or reduced.
`schemeTorsorAction_comp_actionMap` identifies evaluation of its actual action
morphism. The coefficient Hopf structure and cocommutativity remain explicit
inputs, and local nonemptiness is supplied separately by the proved cover
surjectivity.

In `Basic`, the original torsor data, coefficient coordinates and their equations,
chosen point, class vanishing, and any external `hclass` equality remain inputs. The
arbitrary-residue route keeps its DVR, fraction-field, Galois/closure, and
prime/lies-over hypotheses. It first derives fixedness of every original
embedding from the common fixed point and coefficient inertia.

The native global
[`GenericNormalization`](../GenericFiniteEtale/README.md) implementation remains
the owner of relative normalization over general bases. This affine interface
uses the literal integral-closure model and its canonical generic map; it
introduces no alternative normalization carrier or global gluing claim.
Regular-surface gluing and proper-Henselian comparison remain separate.

[AffineAlgebraization](AffineAlgebraization.lean) constructs the actual algebra
coaction and bijective transporter from an affine categorical torsor action.
[FieldRealization](FieldRealization.lean) realizes a finite continuous cocycle
as an actual finite-etale field algebra and point under its Hopf, coefficient,
Galois-category and fibre-functor hypotheses. [OriginalRepresentation](OriginalRepresentation.lean)
specializes this to the literal generic Hopf algebra `K tensor_R H`, with its
structural scalar tower and the original `genericClass` equality.

[SheafClass](SheafClass.lean), [GenericPullback](GenericPullback.lean) and
[ClassExtension](ClassExtension.lean) identify the normalization's actual sheaf
Ext-H1 class and its generic pullback. `modelToGaloisH1` is the original
three-factor composite: generic H1 pullback, the native coefficient comparison,
and identity-coefficient Galois restriction. The proof preserves both independent
Ext universes and proves injection for arbitrary model classes.

[UnramifiedExtension](UnramifiedExtension.lean) combines realization and that
injection: every original class with zero restriction to the same selected
prime's inertia has a unique model Ext-H1 preimage. This local DVR theorem
retains the displayed Hopf/coordinate, GC/FF, Stacks03AJ/03RV, positive
annihilator and invertibility premises. The generic torsor and its point are
constructed in this final endpoint. No unrestricted coefficient-Hopf
representability or global arithmetic endpoint follows.

The source basis is R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
The basic scheme construction comes from `SpecTorsor`, `SpecPullbackTorsor`
and `H1SchemeTorsor:53–350`; the new sheaf, pullback and extension leaves continue
its later source cuts. Each companion guide records the exact source identity
and retained conditions.
