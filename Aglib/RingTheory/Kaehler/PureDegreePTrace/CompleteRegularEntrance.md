# The original complete regular surface entrance

Source: [CompleteRegularEntrance.lean](CompleteRegularEntrance.lean).

`exists_integralTraceEntrance_of_complete_regular_dim_two` starts with an
actual maximal-adically complete regular local ring R of characteristic p
and dimension two, original fraction field K, and original purely inseparable
prime-degree field extension L/K. The scalar maps and original finrank
equality remain unchanged. The ring and fields retain independent universes.

Regular-local domain and normality, characteristic of K and the residue
field, finite-dimensionality of L/K, and finiteness of the literal
`integralClosure R L` are derived. The last uses the existing complete normal
surface purely inseparable finiteness theorem on original R/K/L; no finite
Cohen subring replaces R and no Nagata or finite-normalization premise is added.

The proof calls each accepted supplier once:

1. actual formal coordinates e over the original residue field, retaining the
   canonical coefficient-section, parameter and residue equations;
2. an original nonbase b, nonzero denominator m, integral root z=m*b,
   original coefficient a with z^p=a, and the same-root field presentation h;
3. one finite expanded coefficient-series base E[[X,Y]] and one integral
   differential basis bR, with integral da nonzero and its original-K
   consequences. Positive cardinality is retained as hn:r=n+1. The SAME
   selected basis receives the canonical index transport
   `bR.reindex (finCongr hn)`; native `Basis.reindex_apply` identifies its
   vectors at the inverse index. There is no second basis choice or
   orientation permutation.

The literal map phi from E[[X,Y]] to R is coefficient inclusion followed by
p-expansion and the same e. The output includes both Module.Finite for this
action and RingHom.FiniteType of phi. Its action on K is original R-to-K
after phi; its action on L is original R-to-L after phi. The third scalar
tower follows from the original R/K/L tower. The coefficient field alone is
not used as the finite-type base.

The same h, bR, integral nonzero da and original hdegree feed existing
`Cokernel.of_basis`, producing HasNonzeroCokernelAnnihilator for the literal
`integralClosureTraceTranspose`. Its source is the raw exterior module of
the actual normalization and its coefficient is the actual double dual of
the raw exterior module over R. The existing `.exists_smul_mem_range` then
supplies one fixed nonzero scalar; this leaf duplicates neither that argument
nor a scalar chooser.

The normalization is not asserted globally monogenic. No perfectness, finite
absolute p-rank, arbitrary field section, or differential-rank oracle is an
input. Scheme theory is not imported here: native HasRingHomProperty.Spec_iff
turns the literal phi.FiniteType output into LocallyOfFiniteType of Spec.map
phi at the geometric consumer. That is a genuine finite-type conclusion,
not finiteness of differentials standing in for finite type.
