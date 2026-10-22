# Closed projective field points from the full original coefficient span

Let `β : A →+* κ`, where `A` is a commutative ring and `κ` is a field. The
scalar action is the original `Module.compHom κ β`, explicitly bound in each
span hypothesis. An existing span proof for this same action is accepted
directly. Let the finite original
coefficient family `a : I → κ` satisfy

```text
Submodule.span A (Set.range a) = ⊤.
```

The namespace
`AlgebraicGeometry.ProjectiveSpace.FromSections.FieldSpan` retains the literal
section maps

```text
family a j = unitMul (Spec (.of κ)) ((ΓSpecIso (.of κ)).inv.hom (a j)).
```

`isClosedImmersion_of_span β a ha` derives the actual free-map epimorphism and
proves that the literal original map

```text
mapOfFiniteFamily (Spec.map (CommRingCat.ofHom β))
  (SheafOfModules.unit (Spec (.of κ)).ringCatSheaf)
  (unit_rankOne (Spec (.of κ))) (family a)
```

is a closed immersion. The companion
`isClosedImmersion_mapOfFiniteFamily` accepts an already installed epimorphism
witness for this same family. Proof irrelevance identifies its rank-one and
epimorphism witnesses with any existing witnesses for the same literal map.
No coordinate index or section map is replaced.

`exists_nonzero` derives a nonzero original coordinate from the supplied span.
`family_epi_of_nonzero` uses that coordinate's actual unit-multiplication
isomorphism, and `family_epi_of_span` supplies generation without an extra
premise. `coefficient_finite` derives finiteness of the original ring map `β`
from the same full finite span.

The proof normalizes one actual global frame by the chosen original nonzero
coefficient. Every native coordinate ratio is the corresponding original
coefficient divided by that coefficient. Multiplication by this nonzero
scalar preserves the full original `A`-linear span, so the actual chart ring
map is onto `κ` and onto its original global section ring. The native chart
map is therefore a closed immersion into the selected coordinate chart.
The full projective map is a preimmersion. Finiteness of `β` and the original
structural triangle make that same map proper, and its closed image then
makes it a closed immersion into the original projective space.

There is no Noetherian, characteristic, separately assumed finite extension,
algebraic-closedness, or base-field premise. Finiteness of the original index,
the actual field structure on `κ`, and the original full span are the only
additional inputs. An existing `IsField κ` witness may be installed as a field
structure retaining the original commutative ring before applying the theorem.

## Exact comparison with an original field-valued chart

The additive chart-comparison interface has no full-span or finite-ring-map
premise. For the original `β : A →+* κ`, original coordinate index `I`, and
original `φ : coordinateRing A I i₀ →+* κ`,
`mapOfFiniteFamily_eq_chart_of_ratios β a i₀ hi₀ φ hβ hratio` proves that the
literal `mapOfFiniteFamily` attached to the same `family a` equals

```text
Spec.map (CommRingCat.ofHom φ) ≫
  Proj.awayι (MvPolynomial.homogeneousSubmodule I A) (MvPolynomial.X i₀)
    (MvPolynomial.isHomogeneous_X A i₀) Nat.zero_lt_one.
```

The inputs are the actual original nonzero coordinate `hi₀ : a i₀ ≠ 0`, the
coefficient square `hβ : ∀ r, φ (coordinateRingCoefficient A I i₀ r) = β r`,
and the actual equations
`hratio : ∀ j, φ (coordinateRatio A I i₀ j) = a j * (a i₀)⁻¹`.
The theorem derives the original family epimorphism from `hi₀`.

The normalized wrapper `mapOfFiniteFamily_eq_chart_of_values β a i₀ φ hβ ha`
instead takes `ha : ∀ j, a j = φ (coordinateRatio A I i₀ j)`.
It derives `a i₀ = 1`, nonvanishing and generation internally. Both endpoints
retain the literal family, original index and original ring homomorphisms.
They require only the field structure and the finite index needed by the
existing native constructor, with the same universe bounds as that API.

The proof reuses the original actual one-frame map and its coefficient and
ratio calculations. Native polynomial coordinates show its chart ring map is
the original `φ`, and the original ΓSpec unit identities identify the actual
scheme morphisms. The desired morphism equality is a conclusion. No second
homogeneous-point model, chart-family oracle, finite-extension, Noetherian,
flatness or characteristic premise is introduced.

For two original quotient rows in a generic field, the actual numerator and
nonzero-denominator equations can verify each row's ratios against the same
original `φ`. Applying the first endpoint twice then compares the two actual
maps. The original closed-immersion theorem and its full-span hypotheses are
unchanged.
