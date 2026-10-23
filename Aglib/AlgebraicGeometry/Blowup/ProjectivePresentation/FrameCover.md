# Affine source frames subordinate to affine target charts

`Blowup.ProjectivePresentation.exists_affine_frame_cover` takes an arbitrary
scheme morphism `f : W → X`, the fixed actual source module `D`, and its
`IsLocallyRankOne W D` proof. It returns:

- A native `W.AffineOpenCover` named `𝒰`, with concrete coordinate rings
  `𝒰.X i` and actual open immersions `𝒰.f i : Spec (𝒰.X i) → W`.
- An affine target open `V i` for every source chart, with its actual open
  immersion `(V i).property.fromSpec : Spec Γ(X, V i) → X`.
- A ring map `φ i : Γ(X, V i) → 𝒰.X i` and the actual triangle
  `Spec.map (φ i) ≫ (V i).property.fromSpec = 𝒰.f i ≫ f`.
- A native frame from `(Modules.pullback (𝒰.f i)).obj D` to the structure
  module on `Spec (𝒰.X i)`.

At a source point, the construction chooses an affine target neighborhood
of its image and a trivializing neighborhood of `D`. It then chooses an
affine source neighborhood inside their intersection. The resulting chart
ring is the actual source section ring, and `φ i` is the original `f.appLE`
map. The frame is transported through the native over-site/restriction,
affine-chart, and pullback-composition comparisons.

The cover retains the same source module, so it applies directly when `D`
is the fixed pulled negative twist in a projective presentation. The caller
can use the full original ideal on the affine target chart and its tensor
pullback along `φ i`. No ideal, quotient, generating row, row-compatibility
condition, or chart-map comparison is an input to this construction.

No compactness, Noetherianity, separatedness, flatness, projectivity, or
finiteness hypothesis is used. A finite subcover can be selected separately
when actual compactness is supplied. Proper gluing over a further base and
the original affine row/Proj-map equality remain separate obligations.
