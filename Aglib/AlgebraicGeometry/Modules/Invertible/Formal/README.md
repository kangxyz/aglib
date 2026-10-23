# Formal and henselian lifting of line bundles

| Source family | Reusable interface |
| --- | --- |
| [Square-zero lifting](../SquareZero/README.md) | Actual affine, two-affine and closed-immersion line-bundle lifts across intrinsic square-zero thickenings. |
| [Formal system](System.lean) | Actual compatible bundles give a native coherent adic system when `X` is locally Noetherian. The bundle data themselves require no Noetherianity or assumed adicity. |
| [Rank one and effectivity](Algebraization/Effectivity.lean) | Proper GET algebraizes the actual system; the Fitting-ideal criterion proves the resulting coherent module locally rank one. |
| [Complete-base restriction](ProperPicard.lean) | Actual bundle lifting and original Picard surjectivity for Noetherian `R`, `IsAdicComplete I R`, proper `f`, and an actual affine binary cover. |
| [Completion](Completion.lean) | An actual completed bundle with the prescribed original ideal-fibre comparison over a Noetherian coefficient ring. |
| [Henselian lifting](Henselian/General.lean) | For any henselian local ring and proper `f` with an actual affine binary cover, lifts a line bundle from the residue fibre and proves surjectivity of the original Picard pullback. No Noetherian, flatness, excellence, finite-presentation or separably-closed-residue hypothesis is required. |
| [Projective-line successors](ProjectiveLine.lean) | Square-zero lifting on every original positive ideal-power successor. The final finite-over-projective-line Picard theorem is in [Henselian/General](Henselian/General.lean). |

The field-geometric and characteristic-zero-DVR-geometric henselization
endpoints use their respective actual arithmetic models. General henselian
lifting uses fixed-base proper finite-presentation approximation. Intermediate
arithmetic and proper-limit leaves keep their stated hypotheses; the general
result is assembled in `Henselian/General.lean`.
