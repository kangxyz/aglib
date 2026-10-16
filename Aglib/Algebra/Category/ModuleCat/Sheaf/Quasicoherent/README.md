# Presentation pushforward on arbitrary sites

[Pushforward](Pushforward.lean), imported as `Aglib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Pushforward`, owns `SheafOfModules.localBasisPushforward_preservesColimits` and `finitePresentation_pushforward_of_isLeftAdjoint`. The site functor is continuous, cocontinuous and a left adjoint; the actual structure-ring morphism is invertible and the unit comparison is supplied. Over-site continuity, pullbacks, sheafification and local-bijectivity hypotheses are those in each statement. The actual finite generator and relation index types are unchanged.

The [presentation helpers](../Presentation.lean) are lower inputs. [Local-basis pushforward](../LocallyFree/Pushforward.lean) and scheme finite-presentation restriction consume the same construction.
