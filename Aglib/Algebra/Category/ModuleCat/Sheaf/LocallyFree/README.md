# Local bases on arbitrary ringed sites

[Pushforward](Pushforward.lean) defines `SheafOfModules.pushforwardLocalBasis` and preserves its actual basis and finite-type witnesses under the displayed compatible site-functor, invertible ring-map and supplied unit-isomorphism hypotheses. It uses the single [presentation pushforward](../Quasicoherent/Pushforward.lean) and keeps the cover and generator index types.

[Locality](Locality.lean) supplies `SheafOfModules.finiteLocalBasis_of_sheafIso` and `finiteLocalBasis_bind`: actual finite local bases transport across a sheaf isomorphism and compose over a specified cover. Base/over/double-over sheafification assumptions and the exact CoversTop witness are retained. These are arbitrary-site statements; scheme open restriction and finite-local-freeness detection remain scheme consumers.
