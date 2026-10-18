# Finite-extension Milnor norms

`Basic` defines `MilnorK.finiteExtensionNorm k E n` on the original finite
field extension using a primitive-element presentation. It proves independence
from every actual polynomial presentation. `Tower` proves transitivity on the
original groups; `BaseChange`, `ProductBaseChange` and `DVR` retain their actual
scalar squares, complete branch sums and residue maps.

The general extension interfaces require `CharZero k`, algebra structures and
finite-dimensional hypotheses. Tower and branch theorems retain the displayed
scalar-tower and residue conditions. These results supply neither a motivic
comparison nor an arbitrary-characteristic extension of the same assertions.
