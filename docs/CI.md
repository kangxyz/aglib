# Native local and hosted checks

Local `bash scripts/check.sh` delegates to the shared native CLI. The public
workflow uses ordinary Lake commands described in [the workflow guide](../.github/LEAN_CI.md).
Both use production build, in-package Test, native `mk_all`, text style,
production lint and the pinned upstream production axiom auditor. Local source
layout, placeholders and source-option guards remain available in that entry.
The [development guide](DEVELOPMENT.md#local-verification-and-ci) owns commands.

Lake decides native artifact applicability from source/import/options/toolchain
inputs. Matching successful checks can be reused against their actual command,
checker and input boundary; a changed executor alone is not fresh proof evidence
or a reason to discard unchanged checks. Partial compilation remains useful
after a later check fails. These facts do not certify arbitrary cache producers.

The retired Python CI protocol's GitHub ancestor admission, workflow/recipe hash
allowlists, per-phase receipts and frozen native requests are not part of local
checking. Old evidence retains its historical source and predicate. The upstream
auditor uses defining-module roots and the approved three-axiom policy, relying
on successful compilation; it is not the retired checked-environment/control
auditor and does not inherit those receipts by relabelling.

Hosted Build, Test and publication remain governed by the existing public YAML.
Local migration does not dispatch workflows, publish caches, update pins or add
kernel replay, separate clients or another mathematical acceptance stage.
Independent mathematical review, source correspondence and writing acceptance
retain their governing requirements.
