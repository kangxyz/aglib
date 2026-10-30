# Ext coefficient comparisons

[CoefficientSquare](CoefficientSquare.lean) supplies postcomposition and
coefficient-square calculations for the same selected composite functor and
source arrow. Its comparison keeps four independent category and Ext worlds.

[OriginalComparison](OriginalComparison.lean) supplies the shared original-source
comparison interface used by the finite-image and pullback adapters.
[TransferConsequences](TransferConsequences.lean) is the companion for the
original Ext transfer consequences. These interfaces retain their selected
source maps and explicit category and Ext worlds.
