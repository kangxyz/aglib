# Least empty levels of the original finite prefixes

The existing native Konig projection theorem applies to the literal prefix
truncations. Finite original parent fibres and the absence of a compatible
sequence imply an empty level. No replacement tree, path, or branching model
is introduced.

The height is the least empty level, rather than a chosen upper bound.
Level zero is always nonempty, so height is positive. Original truncation makes
all later levels empty, and the same reroot/prepend construction gives an empty
level for each actual child and strictly smaller child height.

The geometric proofs of finite fibres and absence of infinite singular paths
remain separate required inputs. These combinatorial laws do not establish
surface resolution or serialize independent branches into a global chain.

## Verification

Exact source 9d1fd2380553d298eb4e77bb6e2c537cf446c7c90bf5e69e8925bfb7a6bae1ae
passed its own native check in graph 69 (2.0 seconds, normal caps). The
geometric finite-fibre and no-compatible-sequence inputs remain explicit.
