# v6: private scope and typed identity repair

Applied only to the owned `AssociatedBundle.lean`, from SHA-256
`844a9cc1d6615ee5ef6bdb54afbf1f76eae68f5bc8adbab6112162555be58a0d`
to `1ce133bfe3604320c20dc0693bdb7e2b4b47c7d85d4b37e8950d71eae1c53e58`.
HEAD and input-hash guards passed. Further native writes are held for the
principal's compilation. No compiler invocation was made by this worker.

The partial native 1504 diagnostics reported an inaccessible private
`ChartComposition` after its namespace scope ended, and invalid field notation
for an untyped identity arrow. The unchanged private equation definition and
its cancellation theorem now occupy the same active `Construction` scope as
their consumers. Their existing universe parameters are declared in that scope;
no public universe or signature changes. The three identity-arrow occurrences
in `hid` now carry the literal type `V.unop ⟶ V.unop`, as in the existing
`site_id_left` statement. The proof still invokes the original `pullHom_id`.

The whole-equation representation, three mathematical identities and final
cancellation are unchanged. The complete source suffix after
`sectionFamily_natural` is byte-identical to the input. The invalid relation
head in 1504 prevents interpreting its later timeout and type mismatches as a
clean performance result. Ordinary native AssociatedBundle and PowerDescent
compilation remains pending.
