# Whole normal-open H1 effacement over a selected coefficient field

The native baseline frontend for
`GenericH1NormalWholeOpenEffacement` took 2130 seconds. The retained frontend
took 274 seconds. Both used the pinned Lean 4.34.1 and Mathlib inputs, four
threads and a 12,800 MiB Lean cap. The local import comparison checked
3948 dependency source files byte for byte, together
with the three package pin and configuration files. The public theorem type
is textually unchanged. The runs occurred in separate prepared workspaces.
The recorded improvement is for this frontend.

The proof over a selected coefficient field keeps its field and algebra
instances as variables until the inner witnesses have been produced. The
normal-open stage consumes the original zero proof at its original arrow
along with an equality of arrows. It transports the dependent cohomology
type within the stage proof. This keeps the concrete existential assembler
from having to elaborate a second native zero statement. It retains the
original fields, cover, point and pullback maps.

The bounded explicit-motive and single-application probes timed out after
390 and 400 seconds respectively. A probe at the selected field boundary
passed with the exact original public statement in 320.22 seconds. These
probes do not identify a unique kernel conversion cause. The production
frontend is reported separately from the probes and from downstream builds.

[Measured runs and input comparison](evidence/MEASUREMENTS.json) and
[content hashes](evidence/SHA256.json) index the exact supporting sources,
compiler records and logs.
