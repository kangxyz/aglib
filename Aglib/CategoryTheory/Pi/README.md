# Abelian categories of dependent families

[Abelian](Abelian.lean), imported as `Aglib.CategoryTheory.Pi.Abelian`, equips
Mathlib's actual dependent product category with pointwise preadditive, limit,
colimit and abelian structures. `CategoryTheory.Pi.shortExact_pi_of` detects a
short exact complex by its actual coordinate evaluations. Index, object and hom
universes remain independent.

[FiniteSupport](FiniteSupport.lean) defines `CategoryTheory.Pi.finiteObjectSupport`
using the finite set of coordinates whose objects are nonzero. This property is
a Serre class in a dependent family of abelian categories. Its actual full
subcategory is `FiniteCategoryFamily`; `finiteCategoryEvaluation` is the exact
coordinate functor for the standard abelian exact structures.

The original finite-support module-family construction delegates to this same
property in [FiniteLengthFamilies](../../Algebra/Category/ModuleCat/FiniteLengthFamilies.lean).
Adding coordinatewise finite length retains the actual ring actions. No residue
field replacement or semisimplicity condition is used.
