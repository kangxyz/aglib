/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.Affine
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.OpenMap
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction

/-!
# The original Serre comparison for affine-open coefficients

The actual scheme-isomorphism restriction maps transport the standard affine
result to every supplied affine polynomial model. The original open-pushforward
square then proves bijectivity for an arbitrary quasicoherent module pushed
forward from an affine open. Every nonnegative degree uses the same original
normalized trace and coefficient counits.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The actual normalized comparison on any supplied polynomial model over a spectrum. -/
theorem relativeProjectiveSerreMap_bijective_spec
    (R : Type u) [CommRing R] (ι : Type u) {A : CommRingCat.{u}} [IsNoetherianRing A]
    {X : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Spec A)
    (f : Spec A ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec A).Modules) [N.IsQuasicoherent]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (r : ℕ) :
    Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e N M r) := by
  let E := affinePullbackIso ι a p f h
  let H : IsPullback E.inv (toSpec A ι) p (𝟙 (Spec A)) :=
    RelativeProjectiveTrace.affineModelSquare (A := A) R ι a p f h
  apply (relativeProjectiveSerreMap_bijective_iff_of_isIso p E.inv (toSpec A ι)
    (𝟙 (Spec A)) H R ι a f h n e N M r).mpr
  exact relativeProjectiveSerreMap_bijective_standardAffine R ι (E.inv ≫ a)
    ((𝟙 (Spec A)) ≫ f) (H.paste_horiz h) n e (N.restrict (𝟙 (Spec A)))
    (M.restrict E.inv) (affineLocallyFiniteType_restrict E.inv hM) r

/-- The same original comparison on an arbitrary affine locally Noetherian base. -/
theorem relativeProjectiveSerreMap_bijective_affine
    (R : Type u) [CommRing R] (ι : Type u) {X Y : Scheme.{u}}
    (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y) (f : Y ⟶ Spec (.of R))
    (h : IsPullback a p (toSpec R ι) f) [Y.IsSeparated] [IsAffine Y] [IsLocallyNoetherian Y]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (r : ℕ) :
    Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e N M r) := by
  let A : CommRingCat.{u} := Γ(Y, ⊤)
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian
    ⟨⊤, isAffineOpen_top Y⟩
  let j := Y.isoSpec.inv
  let i := pullback.snd j p
  let q := pullback.fst j p
  let H := (IsPullback.of_hasPullback j p).flip
  apply (relativeProjectiveSerreMap_bijective_iff_of_isIso p i q j H R ι a f h
    n e N M r).mpr
  exact relativeProjectiveSerreMap_bijective_spec R ι (i ≫ a) q (j ≫ f)
    (H.paste_horiz h) n e (N.restrict j) (M.restrict i)
    (affineLocallyFiniteType_restrict i hM) r

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
  [Y.IsSeparated] [IsNoetherian Y]

/-- The literal original Serre map is bijective for every quasicoherent coefficient
pushed forward from an affine open, in every nonnegative Ext degree. -/
theorem relativeProjectiveSerreMap_openPushforward_bijective
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {U : Scheme.{u}} [IsAffine U]
    (j : U ⟶ Y) [IsOpenImmersion j] (L : U.Modules) [L.IsQuasicoherent]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (r : ℕ) :
    letI : ((Scheme.Modules.pushforward j).obj L).IsQuasicoherent :=
      quasicoherent_pushforward_open j L
    Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e
      ((Scheme.Modules.pushforward j).obj L) M r) := by
  let : U.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
  let : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  let : IsAffineHom (j ≫ terminal.from Y) := by
    rw [terminal.comp_from]
    infer_instance
  let : IsAffineHom j := IsAffineHom.of_comp j (terminal.from Y)
  let : ((Scheme.Modules.pushforward j).obj L).IsQuasicoherent :=
    quasicoherent_pushforward_open j L
  let i := pullback.snd j p
  let q := pullback.fst j p
  let H := (IsPullback.of_hasPullback j p).flip
  let : IsFiniteLocallyFree X
      (moduleExteriorPower X (Differentials.relativeDifferentialSheaf p) n) :=
    relativeProjectiveDifferentialTop_finiteLocallyFree R ι a p f h n e
  let : ((relativeTopDifferentialCoefficientsFunctor q n).obj L).IsQuasicoherent :=
    relativeProjectiveDifferentialCoefficients_isQuasicoherent R ι (i ≫ a) q (j ≫ f)
      (H.paste_horiz h) n e L
  let A := relativeOpenSourceRestriction p j n L M r
  let B := relativeOpenTargetRestriction p i q j H L M (n : ℤ) (r : ℤ)
  let Φ := relativeProjectiveSerreMapPlus p R ι a f h n e
    ((Scheme.Modules.pushforward j).obj L) M r
  let Ψ := relativeProjectiveSerreMapPlus q R ι (i ≫ a) (j ≫ f) (H.paste_horiz h)
    n e L (M.restrict i) r
  have heq : B ∘ Φ = Ψ ∘ A := by
    funext x
    exact (relativeProjectiveSerreMapPlus_openPushforward R ι a p f h n e j L M r x).symm
  have hA := relativeOpenSourceRestriction_bijective p j n L M r
  have hB := relativeOpenTargetRestriction_bijective p i q j H L M (n : ℤ) (r : ℤ)
  have hΨ : Function.Bijective Ψ :=
    (relativeProjectiveSerreMapPlus_bijective_iff q R ι (i ≫ a) (j ≫ f) (H.paste_horiz h)
      n e L (M.restrict i) r).mpr
      (relativeProjectiveSerreMap_bijective_affine R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h)
        n e L (M.restrict i) (affineLocallyFiniteType_restrict i hM) r)
  have hb := hΨ.comp hA
  rw [← heq] at hb
  exact (relativeProjectiveSerreMapPlus_bijective_iff p R ι a f h n e
    ((Scheme.Modules.pushforward j).obj L) M r).mp
    ((Function.Bijective.of_comp_iff' hB Φ).mp hb)

end AlgebraicGeometry.Scheme.Cohomology
