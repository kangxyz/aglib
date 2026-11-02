# AS coefficient native-unit repair 3

The closed AS3-only run `remote-dfdf9beaed40462ea787b2c0d19165f2` identified one real boundary in input `f71d888b`: association rewriting rechecked an eagerly changed target that mixed the native constant-sheaf object head with the `sheafify` presheaf head. The mathematical ring calculation was not implicated.

Following the current PERFORMANCE conversion-boundary and shared-constructor methods, this repair keeps the actual constant presheaf P0 and selected original additive sheaf A0 fully typed. It proves the whole original residue-presheaf-map composed with original AS.hom is zero, using the same map_pow/ZMod.pow_card/sub_self calculation. It transports that proved identity with the native sheafificationAdjunction HomEquiv naturality-right-symm law, and uses the native unit's composition with zero plus Equiv injectivity for the zero transpose. All HomEquiv values have the literal presheafToSheaf.obj source head. There is no eager carrier change, association rewrite, extra realization or desired-law premise.

All source before the final proof, including its statement and every original map/value/unit construction, is byte-identical. The two fixed Scheme wrappers remain at 5be6/d2a7. No transparency flag, linter suppression, mathematical assumption, model, world change or probe was introduced. Exact failed input, repaired output, delta and closed-run/source provenance are preserved here; earlier versions remain fixed.

READY/HOLD, uncompiled by this author. The root's retry remains exactly the same lower leaf and two already-refactored wrappers plus necessary dependencies, with no untouched AS consumer. Other owned native paths, Git/index, registry, README and network were held.
