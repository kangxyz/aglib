/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Tangent.DualNumbers
public import Aglib.AlgebraicGeometry.Picard.Tangent.Points

/-! Focused consumer of the tangent space at the unit of a functor represented on locally
Noetherian test schemes (Kleiman, arXiv:math/0504020v1, proof of Thm 5.11, (5.11.1)–(5.11.3),
pp. 42–43): `ker(F(L[ε]) → F(L))` is `Hom_k(𝔪/𝔪², L)` additively and `L`-linearly, with
scalar multiplication `F(µ_a)` and `finrank_L = finrank_k (𝔪/𝔪²)`; axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory Opposite IsLocalRing AlgebraicGeometry Scheme

universe w u

variable {k : Type u} [Field k] (F : (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})
  {P : LocallyNoetherianOver (Spec (.of k))}
  (e : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ F ⋙
    CategoryTheory.forget AddCommGrpCat.{w}).RepresentableBy P)
  (L : Type u) [Field L] [Algebra k L]

/-- The stalk at the unit point is a `k`-algebra, with residue map the unit section. -/
example : unitStalk e →ₐ[k] k := unitResidue e

/-- Step 1: the tangent kernel is the set of `L[ε]`-points reducing to the unit section. -/
example : tangentKernel F L ≃
    {f : locallyNoetherianSpecOver k (DualNumber L) ⟶ P //
      locallyNoetherianSpecOverMap (TrivSqZeroExt.fstHom k L L) ≫ f =
        locallyNoetherianSpecOverMap (Algebra.ofId k L) ≫ unitSection e} :=
  squareZeroKernelEquivPoints e L L

/-- Step 2: such points are the local `k`-algebra maps `𝒪_{P,x₀} → L[ε]` reducing to the
residue map. -/
example : {φ : unitStalk e →ₐ[k] DualNumber L //
      (TrivSqZeroExt.fstHom k L L).comp φ = (Algebra.ofId k L).comp (unitResidue e)} ≃
    {f : locallyNoetherianSpecOver k (DualNumber L) ⟶ P //
      locallyNoetherianSpecOverMap (TrivSqZeroExt.fstHom k L L) ≫ f =
        locallyNoetherianSpecOverMap (Algebra.ofId k L) ≫ unitSection e} :=
  squareZeroLiftEquivPoints e L L

/-- Step 3: the tangent kernel is the set of `k`-derivations `𝒪_{P,x₀} → L`, with `𝒪_{P,x₀}`
acting on `L` through the residue map. -/
example :
    letI := moduleViaAlgHom (unitResidue e) L L
    letI := isScalarTower_moduleViaAlgHom (unitResidue e) L L
    tangentKernel F L ≃ Derivation k (unitStalk e) L :=
  squareZeroKernelEquivDerivation e L L

/-- The tangent kernel is `Hom_k(𝔪/𝔪², L)` as an additive group. -/
example : tangentKernel F L ≃+ (CotangentSpace (unitStalk e) →ₗ[k] L) := tangentKernelEquiv e L

example (t t' : tangentKernel F L) :
    tangentKernelEquiv e L (t + t') = tangentKernelEquiv e L t + tangentKernelEquiv e L t' :=
  map_add _ t t'

/-- The scaling `µ_a : ε ↦ a ε` is scalar multiplication by `a`. -/
example (a : L) (t : tangentKernel F L) :
    tangentKernelEquiv e L (squareZeroKernelMap F (a • LinearMap.id) t) =
      a • tangentKernelEquiv e L t :=
  tangentKernelEquiv_scale e L a t

/-- The `L`-module structure acts through `F(µ_a)`, independently of `e`. -/
example (a : L) (t : tangentKernel F L) :
    letI := tangentKernelModule e L
    a • t = squareZeroKernelMap F (a • LinearMap.id) t :=
  rfl

example :
    letI := tangentKernelModule e L
    tangentKernel F L ≃ₗ[L] (CotangentSpace (unitStalk e) →ₗ[k] L) :=
  tangentKernelLinearEquiv e L

/-- The rank formula over every field `L` over `k`. -/
example :
    letI := tangentKernelModule e L
    Module.finrank L (tangentKernel F L) = Module.finrank k (CotangentSpace (unitStalk e)) :=
  finrank_tangentKernel e L

/-- Over `k` itself the tangent kernel is a finite-dimensional `k`-vector space. -/
example :
    letI := tangentKernelModule e k
    Module.Finite k (tangentKernel F k) :=
  finite_tangentKernel e k

/-- The kernel over `L[ε, ε'] = L ⊕ L²`. -/
example :
    letI := squareZeroKernelModule e L (L × L)
    Module.finrank L (squareZeroKernel F L (L × L)) =
      Module.finrank k (CotangentSpace (unitStalk e)) * Module.finrank L (L × L) :=
  finrank_squareZeroKernel e L (L × L)

/-- For `L = k` the test objects are those of `Picard/Tangent/DualNumbers`: `Spec k[ε]` over
`Spec k` through `dualMap k`, with the closed point `closedPoint k`. -/
example : specOver k (DualNumber k) = Over.mk (Scheme.DualNumbers.dualMap k) := rfl

example : (specOverMap (TrivSqZeroExt.fstHom k k k)).left = Scheme.DualNumbers.closedPoint k := rfl

/--
info: 'AlgebraicGeometry.Scheme.tangentKernelEquiv' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tangentKernelEquiv

/--
info: 'AlgebraicGeometry.Scheme.squareZeroKernelEquiv_add' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms squareZeroKernelEquiv_add

/--
info: 'AlgebraicGeometry.Scheme.tangentKernelEquiv_scale' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tangentKernelEquiv_scale

/--
info: 'AlgebraicGeometry.Scheme.tangentKernelLinearEquiv' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tangentKernelLinearEquiv

/--
info: 'AlgebraicGeometry.Scheme.finrank_tangentKernel' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finrank_tangentKernel

/--
info: 'AlgebraicGeometry.Scheme.squareZeroLiftEquivPoints' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms squareZeroLiftEquivPoints
