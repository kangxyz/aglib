/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Aglib.AlgebraicGeometry.Stalk.SpecLocalRing
public import Aglib.RingTheory.LocalRing.SquareZeroLift
public import Aglib.RingTheory.TrivSqZeroExt
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Tangent vectors at the unit of a represented functor

Let `k` be a field and `F : (Over (Spec k))ᵒᵖ ⥤ AddCommGrpCat` a functor whose restriction to
locally Noetherian test schemes is represented by `P` (`e`). Let `e₀ : Spec k ⟶ P` represent
`0 ∈ F(k)` (`unitSection`), `x₀ ∈ P` its point (`unitPoint`), `O = 𝒪_{P, x₀}` (`unitStalk`),
a `k`-algebra through the structure map (`unitStalkAlgebra`), with maximal ideal `𝔪` and
residue map `O → k` the stalk map of `e₀` (`unitResidue`), so the residue field is `k`.

For a field `L` over `k` and a finite-dimensional `L`-module `M`, let `L ⊕ M = TrivSqZeroExt L M`
(`L[ε] = L ⊕ L`) and `ρ : Spec L ⟶ Spec (L ⊕ M)` the closed point. The kernel of
`F(ρ) : F(L ⊕ M) → F(L)` (`squareZeroKernel F L M`, and `tangentKernel F L` for `M = L`) is
identified with `Hom_k(𝔪/𝔪², M)` (`squareZeroKernelEquiv`):

1. `t ↦ e⁻¹ t` identifies the kernel with the morphisms `f : Spec (L ⊕ M) ⟶ P` over `k` with
   `ρ ≫ f = (Spec L → Spec k) ≫ e₀` (`squareZeroKernelEquivPoints`);
2. such morphisms are `Spec φ ≫ (Spec O → P)` for a unique local `k`-algebra map `φ : O → L ⊕ M`
   reducing to the residue map (`squareZeroLiftEquivPoints`), by Mathlib's
   `SpecToEquivOfLocalRing`;
3. and 4. these `φ` are the lifts `a ↦ (ψ a, θ [a - ψ a])` of `θ : 𝔪/𝔪² →ₗ[k] M`
   (`IsLocalRing.trivSqZeroExtLiftEquiv`), where `ψ` is the residue map. The second coordinate
   of a lift is the `k`-derivation `θ ∘ [· - ψ ·]` (`IsLocalRing.cotangentDerivation`), and
   derivations into modules killed by `𝔪` are the cotangent maps
   (`IsLocalRing.derivationEquivCotangentSpace`), since the residue field is `k`.

The identification is natural for `L`-linear maps `g : M → M'` acting through
`TrivSqZeroExt.map g` (`squareZeroKernelEquiv_map`). With `g = a • id` on `M = L` this is the
scaling `µ_a : ε ↦ a ε` (`tangentKernelEquiv_scale`, Kleiman's scalar structure, p. 42). With the
linear maps between `M` and `M × M` it gives additivity (`squareZeroKernelEquiv_add`), so
`squareZeroKernelAddEquiv` and `tangentKernelEquiv` are additive. This replaces Kleiman's σ/π
argument (pp. 42–43) by one that uses only the group structures of `F(L ⊕ M)` and
`F(L ⊕ M²)` (for `M = L`, of `F(L[ε])` and `F(L[ε, ε'])`, `L[ε, ε'] = L ⊕ L²`) and the
additivity of `F` on morphisms, and no group scheme. The `L`-module structure
`a • t = F(µ_a) t` (`squareZeroKernelModule`, `tangentKernelModule`) makes the identification
`L`-linear (`squareZeroKernelLinearEquiv`). The kernel is finite-dimensional, since `P` is
locally Noetherian: `finrank_L ker = finrank_k (𝔪/𝔪²)` for `M = L` (`finrank_tangentKernel`),
and `finrank_k (𝔪/𝔪²) · finrank_L M` in general (`finrank_squareZeroKernel`).

Source: Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 5.11, (5.11.1)–(5.11.3),
pp. 42–43, where `L = k`, `P` is a `k`-scheme locally of finite type and `e₀` a rational point.
Here `L` is any field over `k`, `F` is any functor of abelian groups whose restriction to locally
Noetherian test schemes (`Scheme.LocallyNoetherianOver`) is represented, and no group scheme and
no finite-type hypothesis on `P` is used: the stalks of the locally Noetherian `P` are Noetherian.
Kleiman's addition `α = P(σ) π⁻¹` uses that `π` is bijective; the proof here evaluates `F(σ)`
at `F(ι₁) m + F(ι₂) n` instead, for the two inclusions `ι₁, ι₂ : L ⊕ M → L ⊕ M²`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing

universe w u

namespace AlgebraicGeometry.Scheme

section SpecOver

variable (k : Type u) [CommRing k]

/-- `Spec A` as a scheme over `Spec k`, for a `k`-algebra `A`. -/
abbrev specOver (A : Type u) [CommRing A] [Algebra k A] : Over (Spec (.of k)) :=
  Over.mk (Spec.algebraMap k A)

variable {k}

/-- `Spec f` over `Spec k`, for a `k`-algebra map `f : A →ₐ[k] B`. -/
def specOverMap {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) : specOver k B ⟶ specOver k A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (Spec.map_algHom_algebraMap f)

@[simp]
theorem specOverMap_left {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) : (specOverMap f).left = Spec.map (CommRingCat.ofHom f.toRingHom) :=
  rfl

theorem specOverMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra k A]
    [Algebra k B] [Algebra k C] (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    specOverMap (g.comp f) = specOverMap g ≫ specOverMap f := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specOverMap_left, specOverMap_left, specOverMap_left, ← Spec.map_comp]
  rfl

variable (k) in
/-- `Spec A` as a locally Noetherian test scheme over `Spec k`, for a Noetherian `k`-algebra. -/
abbrev locallyNoetherianSpecOver (A : Type u) [CommRing A] [Algebra k A] [IsNoetherianRing A] :
    LocallyNoetherianOver (Spec (.of k)) :=
  ⟨specOver k A, inferInstanceAs (IsLocallyNoetherian (Spec (.of A)))⟩

/-- `Spec f` between locally Noetherian test schemes over `Spec k`. -/
abbrev locallyNoetherianSpecOverMap {A B : Type u} [CommRing A] [CommRing B] [Algebra k A]
    [Algebra k B] [IsNoetherianRing A] [IsNoetherianRing B] (f : A →ₐ[k] B) :
    locallyNoetherianSpecOver k B ⟶ locallyNoetherianSpecOver k A :=
  ObjectProperty.homMk (specOverMap f)

end SpecOver

section TangentKernel

variable {k : Type u} [Field k] (F : (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})
variable {P : LocallyNoetherianOver (Spec (.of k))}
  (e : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ F ⋙
    CategoryTheory.forget AddCommGrpCat.{w}).RepresentableBy P)
variable (L : Type u) [Field L] [Algebra k L]
variable (M : Type u) [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M] [IsCentralScalar L M]
  [Module k M] [IsScalarTower k L M]
variable {M' : Type u} [AddCommGroup M'] [Module L M'] [Module Lᵐᵒᵖ M'] [IsCentralScalar L M']
  [Module k M'] [IsScalarTower k L M']

/-- The kernel of `F(L ⊕ M) → F(L)`, induced by the closed point `Spec L ⟶ Spec (L ⊕ M)`. -/
def squareZeroKernel : AddSubgroup (F.obj (op (specOver k (TrivSqZeroExt L M)))) :=
  (F.map (specOverMap (TrivSqZeroExt.fstHom k L M)).op).hom.ker

/-- The tangent kernel `ker(F(L[ε]) → F(L))`. -/
abbrev tangentKernel : AddSubgroup (F.obj (op (specOver k (DualNumber L)))) :=
  squareZeroKernel F L L

variable {L M}

theorem fstHom_comp_map_restrictScalars (g : M →ₗ[L] M') :
    (TrivSqZeroExt.fstHom k L M').comp ((TrivSqZeroExt.map g).restrictScalars k) =
      TrivSqZeroExt.fstHom k L M :=
  AlgHom.ext fun x => TrivSqZeroExt.fst_map g x

/-- The map of kernels induced by an `L`-linear map `g : M → M'`, through
`TrivSqZeroExt.map g : L ⊕ M → L ⊕ M'`. -/
def squareZeroKernelMap (g : M →ₗ[L] M') : squareZeroKernel F L M →+ squareZeroKernel F L M' where
  toFun t := ⟨(F.map (specOverMap ((TrivSqZeroExt.map g).restrictScalars k)).op).hom t.1, by
    have h : specOverMap (TrivSqZeroExt.fstHom k L M') ≫
        specOverMap ((TrivSqZeroExt.map g).restrictScalars k) =
          specOverMap (TrivSqZeroExt.fstHom k L M) := by
      rw [← specOverMap_comp, fstHom_comp_map_restrictScalars]
    refine AddMonoidHom.mem_ker.mpr ?_
    rw [← AddMonoidHom.comp_apply, ← AddCommGrpCat.hom_comp, ← F.map_comp, ← op_comp, h]
    exact AddMonoidHom.mem_ker.mp t.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' t t' := Subtype.ext (map_add _ _ _)

@[simp]
theorem coe_squareZeroKernelMap (g : M →ₗ[L] M') (t : squareZeroKernel F L M) :
    (squareZeroKernelMap F g t : F.obj (op (specOver k (TrivSqZeroExt L M')))) =
      (F.map (specOverMap ((TrivSqZeroExt.map g).restrictScalars k)).op).hom t :=
  rfl

variable {F}

/-- The unit section `e₀ : Spec k ⟶ P`, the morphism representing `0 ∈ F(k)`. -/
def unitSection : locallyNoetherianSpecOver k k ⟶ P :=
  e.homEquiv.symm (0 : F.obj (op (specOver k k)))

/-- The unit point `x₀ ∈ P`, the image of the point of `Spec k` under the unit section. -/
abbrev unitPoint : P.obj.left :=
  (unitSection e).hom.left (closedPoint (CommRingCat.of k))

/-- The local ring `𝒪_{P, x₀}` of `P` at the unit point. -/
abbrev unitStalk : CommRingCat.{u} :=
  P.obj.left.presheaf.stalk (unitPoint e)

/-- The `k`-algebra structure of `𝒪_{P, x₀}`, from the structure map `P ⟶ Spec k`. -/
instance unitStalkAlgebra : Algebra k (unitStalk e) :=
  (P.obj.hom.stalkScalar (unitPoint e)).toAlgebra

/-- The residue map `𝒪_{P, x₀} → k`: the stalk map of the unit section. Its kernel is the maximal
ideal, so the residue field at `x₀` is `k`. -/
def unitResidue : unitStalk e →ₐ[k] k where
  toRingHom := (stalkClosedPointTo (unitSection e).hom.left).hom
  commutes' c := by
    have h1 := Spec_stalkClosedPointTo_fromSpecStalk (unitSection e).hom.left
    have h2 : (unitSection e).hom.left ≫ P.obj.hom = Spec.algebraMap k k :=
      Over.w (unitSection e).hom
    have h3 : Spec.map (CommRingCat.ofHom (P.obj.hom.stalkScalar (unitPoint e)) ≫
        stalkClosedPointTo (unitSection e).hom.left) =
          Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
      rw [Spec.map_comp, ← fromSpecStalk_comp_eq_spec_map_stalkScalar, ← Category.assoc, h1, h2]
    exact congrArg (fun φ => φ.hom c) (Spec.map_injective h3)

theorem unitResidue_toRingHom :
    (unitResidue e).toRingHom = (stalkClosedPointTo (unitSection e).hom.left).hom :=
  rfl

/-- `RepresentableBy.homEquiv_comp`, with the transition map written as the homomorphism
`F(q)`. -/
theorem homEquiv_comp_apply {T T' : LocallyNoetherianOver (Spec (.of k))} (q : T ⟶ T')
    (g : T' ⟶ P) : e.homEquiv (q ≫ g) = (F.map q.hom.op).hom (e.homEquiv g) :=
  e.homEquiv_comp q g

theorem homEquiv_comp_homEquiv_symm {T T' : LocallyNoetherianOver (Spec (.of k))} (q : T ⟶ T')
    (x : F.obj (op T'.obj)) : e.homEquiv (q ≫ e.homEquiv.symm x) = (F.map q.hom.op).hom x :=
  (homEquiv_comp_apply e q (e.homEquiv.symm x)).trans
    (congrArg (F.map q.hom.op).hom (e.homEquiv.apply_symm_apply x))

/-- `e` sends every morphism to `Spec k` followed by the unit section to `0`. -/
theorem homEquiv_comp_unitSection (T : LocallyNoetherianOver (Spec (.of k)))
    (q : T ⟶ locallyNoetherianSpecOver k k) :
    e.homEquiv (q ≫ unitSection e) = (0 : F.obj (op T.obj)) := by
  rw [homEquiv_comp_apply e, unitSection, Equiv.apply_symm_apply]
  exact map_zero (F.map q.hom.op).hom

variable (L M) [Module.Finite L M]

/-- The `L ⊕ M`-point `Spec φ ≫ (Spec 𝒪_{P,x₀} → P)` of `P` defined by a `k`-algebra map
`φ : 𝒪_{P, x₀} → L ⊕ M`. -/
def squareZeroPoint (φ : unitStalk e →ₐ[k] TrivSqZeroExt L M) :
    locallyNoetherianSpecOver k (TrivSqZeroExt L M) ⟶ P :=
  ObjectProperty.homMk (Over.homMk
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P.obj.left.fromSpecStalk (unitPoint e)) (by
      rw [Category.assoc, fromSpecStalk_comp_eq_spec_map_stalkScalar]
      exact Spec.map_algHom_algebraMap φ))

theorem squareZeroPoint_hom_left (φ : unitStalk e →ₐ[k] TrivSqZeroExt L M) :
    (squareZeroPoint e L M φ).hom.left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P.obj.left.fromSpecStalk (unitPoint e) :=
  rfl

variable {L M}

/-- A point defined by a lift of the residue map reduces to the unit section. -/
theorem closedPoint_comp_squareZeroPoint {φ : unitStalk e →ₐ[k] TrivSqZeroExt L M}
    (hφ : (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp (unitResidue e)) :
    locallyNoetherianSpecOverMap (TrivSqZeroExt.fstHom k L M) ≫ squareZeroPoint e L M φ =
      locallyNoetherianSpecOverMap (Algebra.ofId k L) ≫ unitSection e := by
  have h : CommRingCat.ofHom φ.toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom k L M).toRingHom =
        stalkClosedPointTo (unitSection e).hom.left ≫
          CommRingCat.ofHom (Algebra.ofId k L).toRingHom := by
    ext a
    exact AlgHom.congr_fun hφ a
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k L M).toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P.obj.left.fromSpecStalk (unitPoint e) =
    Spec.map (CommRingCat.ofHom (Algebra.ofId k L).toRingHom) ≫ (unitSection e).hom.left
  rw [← Spec_stalkClosedPointTo_fromSpecStalk (unitSection e).hom.left, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc, h]

/-- Composing a point with `Spec` of a `k`-algebra map `h` composes the algebra maps. -/
theorem locallyNoetherianSpecOverMap_comp_squareZeroPoint [Module.Finite L M']
    (h : TrivSqZeroExt L M →ₐ[k] TrivSqZeroExt L M') (φ : unitStalk e →ₐ[k] TrivSqZeroExt L M) :
    locallyNoetherianSpecOverMap h ≫ squareZeroPoint e L M φ =
      squareZeroPoint e L M' (h.comp φ) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom h.toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P.obj.left.fromSpecStalk (unitPoint e) =
    Spec.map (CommRingCat.ofHom (h.comp φ).toRingHom) ≫ P.obj.left.fromSpecStalk (unitPoint e)
  rw [← Spec.map_comp_assoc]
  rfl

theorem squareZeroPoint_injective {φ φ' : unitStalk e →ₐ[k] TrivSqZeroExt L M}
    (hφ : (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp (unitResidue e))
    (hφ' : (TrivSqZeroExt.fstHom k L M).comp φ' = (Algebra.ofId k L).comp (unitResidue e))
    (h : squareZeroPoint e L M φ = squareZeroPoint e L M φ') : φ = φ' := by
  have hl : IsLocalHom (CommRingCat.ofHom φ.toRingHom).hom :=
    ⟨(isLocalHom_of_fstHom_comp_eq hφ).map_nonunit⟩
  have hl' : IsLocalHom (CommRingCat.ofHom φ'.toRingHom).hom :=
    ⟨(isLocalHom_of_fstHom_comp_eq hφ').map_nonunit⟩
  have h' := congrArg (fun f => f.hom.left) h
  simp only [squareZeroPoint_hom_left] at h'
  have := spec_map_comp_fromSpecStalk_injective h'
  exact AlgHom.ext fun a => congrArg (fun f => f.hom a) this

/-- Every point reducing to the unit section comes from a lift of the residue map. -/
theorem exists_squareZeroPoint (f : locallyNoetherianSpecOver k (TrivSqZeroExt L M) ⟶ P)
    (hf : locallyNoetherianSpecOverMap (TrivSqZeroExt.fstHom k L M) ≫ f =
      locallyNoetherianSpecOverMap (Algebra.ofId k L) ≫ unitSection e) :
    ∃ φ : unitStalk e →ₐ[k] TrivSqZeroExt L M,
      (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp (unitResidue e) ∧
        squareZeroPoint e L M φ = f := by
  have hf' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k L M).toRingHom) ≫ f.hom.left =
      Spec.map (CommRingCat.ofHom (Algebra.ofId k L).toRingHom) ≫ (unitSection e).hom.left :=
    congrArg (fun g => g.hom.left) hf
  have : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom k L M).toRingHom).hom :=
    ⟨fun _ ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  have h1 : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k L M).toRingHom))
      (closedPoint (CommRingCat.of L)) = closedPoint (CommRingCat.of (TrivSqZeroExt L M)) :=
    Spec_closedPoint
  have h2 : (Spec.map (CommRingCat.ofHom (Algebra.ofId k L).toRingHom))
      (closedPoint (CommRingCat.of L)) = closedPoint (CommRingCat.of k) :=
    Spec_closedPoint
  have hx : f.hom.left (closedPoint (CommRingCat.of (TrivSqZeroExt L M))) = unitPoint e :=
    calc f.hom.left (closedPoint (CommRingCat.of (TrivSqZeroExt L M)))
        = f.hom.left ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k L M).toRingHom))
            (closedPoint (CommRingCat.of L))) := by rw [h1]
      _ = (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k L M).toRingHom) ≫ f.hom.left)
            (closedPoint (CommRingCat.of L)) := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom (Algebra.ofId k L).toRingHom) ≫ (unitSection e).hom.left)
            (closedPoint (CommRingCat.of L)) := by rw [hf']
      _ = (unitSection e).hom.left ((Spec.map (CommRingCat.ofHom (Algebra.ofId k L).toRingHom))
            (closedPoint (CommRingCat.of L))) := Scheme.Hom.comp_apply _ _ _
      _ = unitPoint e := by rw [h2]
  obtain ⟨φ, hφloc, hφ⟩ := exists_spec_map_comp_fromSpecStalk f.hom.left hx
  have hk : CommRingCat.ofHom (P.obj.hom.stalkScalar (unitPoint e)) ≫ φ =
      CommRingCat.ofHom (algebraMap k (TrivSqZeroExt L M)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← fromSpecStalk_comp_eq_spec_map_stalkScalar, ← Category.assoc, hφ]
    exact Over.w f.hom
  let φₐ : unitStalk e →ₐ[k] TrivSqZeroExt L M :=
    { φ.hom with commutes' := fun c => congrArg (fun g => g.hom c) hk }
  have hred : (TrivSqZeroExt.fstHom k L M).comp φₐ = (Algebra.ofId k L).comp (unitResidue e) := by
    have hloc₁ : IsLocalHom (φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom k L M).toRingHom).hom :=
      inferInstanceAs (IsLocalHom ((TrivSqZeroExt.fstHom k L M).toRingHom.comp φ.hom))
    have hloc₂ : IsLocalHom (stalkClosedPointTo (unitSection e).hom.left ≫
        CommRingCat.ofHom (Algebra.ofId k L).toRingHom).hom :=
      inferInstanceAs (IsLocalHom ((Algebra.ofId k L).toRingHom.comp
        (stalkClosedPointTo (unitSection e).hom.left).hom))
    have heq := spec_map_comp_fromSpecStalk_injective (x := unitPoint e)
      (φ := φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom k L M).toRingHom)
      (φ' := stalkClosedPointTo (unitSection e).hom.left ≫
        CommRingCat.ofHom (Algebra.ofId k L).toRingHom) (by
          rw [Spec.map_comp_assoc, hφ, hf', Spec.map_comp_assoc,
            Spec_stalkClosedPointTo_fromSpecStalk])
    exact AlgHom.ext fun a => congrArg (fun g => g.hom a) heq
  refine ⟨φₐ, hred, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hφ

variable (L M)

/-- **Step 1** (Kleiman (5.11.2)). `e` identifies the kernel of `F(L ⊕ M) → F(L)` with the
points `f : Spec (L ⊕ M) ⟶ P` over `k` reducing to the unit section:
`ρ ≫ f = (Spec L → Spec k) ≫ e₀`. -/
def squareZeroKernelEquivPoints :
    squareZeroKernel F L M ≃
      {f : locallyNoetherianSpecOver k (TrivSqZeroExt L M) ⟶ P //
        locallyNoetherianSpecOverMap (TrivSqZeroExt.fstHom k L M) ≫ f =
          locallyNoetherianSpecOverMap (Algebra.ofId k L) ≫ unitSection e} where
  toFun t := ⟨e.homEquiv.symm t.1, by
    apply e.homEquiv.injective
    rw [homEquiv_comp_homEquiv_symm e, homEquiv_comp_unitSection e]
    have h2 := AddMonoidHom.mem_ker.mp t.2
    exact h2⟩
  invFun f := ⟨e.homEquiv f.1, by
    refine AddMonoidHom.mem_ker.mpr ?_
    have h := homEquiv_comp_apply e (locallyNoetherianSpecOverMap (TrivSqZeroExt.fstHom k L M))
      f.1
    rw [f.2, homEquiv_comp_unitSection] at h
    exact h.symm⟩
  left_inv t := Subtype.ext
    ((e.homEquiv (X := locallyNoetherianSpecOver k (TrivSqZeroExt L M))).apply_symm_apply t.1)
  right_inv f := Subtype.ext (e.homEquiv.symm_apply_apply f.1)

theorem coe_squareZeroKernelEquivPoints_symm_apply
    (f : {f : locallyNoetherianSpecOver k (TrivSqZeroExt L M) ⟶ P //
      locallyNoetherianSpecOverMap (TrivSqZeroExt.fstHom k L M) ≫ f =
        locallyNoetherianSpecOverMap (Algebra.ofId k L) ≫ unitSection e}) :
    ((squareZeroKernelEquivPoints e L M).symm f : F.obj (op (specOver k (TrivSqZeroExt L M)))) =
      e.homEquiv f.1 :=
  rfl

/-- **Step 2** (Kleiman (5.11.1)). The points reducing to the unit section are the
`Spec φ ≫ (Spec 𝒪_{P,x₀} → P)` for the `k`-algebra maps `φ : 𝒪_{P,x₀} → L ⊕ M` reducing to the
residue map; such `φ` are local. This is Mathlib's `SpecToEquivOfLocalRing` at `x₀`. -/
def squareZeroLiftEquivPoints :
    {φ : unitStalk e →ₐ[k] TrivSqZeroExt L M //
      (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp (unitResidue e)} ≃
      {f : locallyNoetherianSpecOver k (TrivSqZeroExt L M) ⟶ P //
        locallyNoetherianSpecOverMap (TrivSqZeroExt.fstHom k L M) ≫ f =
          locallyNoetherianSpecOverMap (Algebra.ofId k L) ≫ unitSection e} :=
  Equiv.ofBijective
    (fun φ => ⟨squareZeroPoint e L M φ.1, closedPoint_comp_squareZeroPoint e φ.2⟩)
    ⟨fun φ φ' h => Subtype.ext (squareZeroPoint_injective e φ.2 φ'.2 (congrArg Subtype.val h)),
      fun f => by
        obtain ⟨φ, hred, hφ⟩ := exists_squareZeroPoint e f.1 f.2
        exact ⟨⟨φ, hred⟩, Subtype.ext hφ⟩⟩

theorem coe_squareZeroLiftEquivPoints_apply
    (φ : {φ : unitStalk e →ₐ[k] TrivSqZeroExt L M //
      (TrivSqZeroExt.fstHom k L M).comp φ = (Algebra.ofId k L).comp (unitResidue e)}) :
    (squareZeroLiftEquivPoints e L M φ).1 = squareZeroPoint e L M φ.1 :=
  rfl

/-- The element of the kernel defined by `θ : 𝔪/𝔪² →ₗ[k] M`: the class of the point of the lift
`a ↦ (ψ a, θ [a - ψ a])`. -/
def squareZeroKernelOfCotangent (θ : CotangentSpace (unitStalk e) →ₗ[k] M) :
    squareZeroKernel F L M :=
  ⟨e.homEquiv (squareZeroPoint e L M (trivSqZeroExtLift (unitResidue e) θ)), by
    refine AddMonoidHom.mem_ker.mpr ?_
    have h := homEquiv_comp_apply e (locallyNoetherianSpecOverMap (TrivSqZeroExt.fstHom k L M))
      (squareZeroPoint e L M (trivSqZeroExtLift (unitResidue e) θ))
    rw [closedPoint_comp_squareZeroPoint e (fstHom_comp_trivSqZeroExtLift _ θ),
      homEquiv_comp_unitSection] at h
    exact h.symm⟩

theorem squareZeroKernelOfCotangent_eq (θ : CotangentSpace (unitStalk e) →ₗ[k] M) :
    squareZeroKernelOfCotangent e L M θ =
      (squareZeroKernelEquivPoints e L M).symm (squareZeroLiftEquivPoints e L M
        ((trivSqZeroExtLiftEquiv (unitResidue e) L M).symm θ)) := by
  refine Subtype.ext ?_
  rw [coe_squareZeroKernelEquivPoints_symm_apply, coe_squareZeroLiftEquivPoints_apply,
    trivSqZeroExtLiftEquiv_symm_apply_coe]
  rfl

theorem squareZeroKernelOfCotangent_bijective :
    Function.Bijective (squareZeroKernelOfCotangent e L M) := by
  have h : squareZeroKernelOfCotangent e L M =
      ⇑(((squareZeroKernelEquivPoints e L M).trans (squareZeroLiftEquivPoints e L M).symm).trans
        (trivSqZeroExtLiftEquiv (unitResidue e) L M)).symm := by
    funext θ
    rw [squareZeroKernelOfCotangent_eq, Equiv.symm_trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_symm]
  rw [h]
  exact Equiv.bijective _

/-- **Kleiman (5.11.1)–(5.11.2).** The kernel of `F(L ⊕ M) → F(L)` is `Hom_k(𝔪/𝔪², M)`, for the
cotangent space `𝔪/𝔪²` of `P` at the unit point: step 1 (`squareZeroKernelEquivPoints`), step 2
(`squareZeroLiftEquivPoints`) and steps 3–4 (`IsLocalRing.trivSqZeroExtLiftEquiv`), see
`squareZeroKernelEquiv_eq_trans`. -/
def squareZeroKernelEquiv :
    squareZeroKernel F L M ≃ (CotangentSpace (unitStalk e) →ₗ[k] M) :=
  (Equiv.ofBijective _ (squareZeroKernelOfCotangent_bijective e L M)).symm

theorem squareZeroKernelEquiv_symm_apply (θ : CotangentSpace (unitStalk e) →ₗ[k] M) :
    (squareZeroKernelEquiv e L M).symm θ = squareZeroKernelOfCotangent e L M θ :=
  rfl

/-- The identification is the composite of the bijections of steps 1–4. -/
theorem squareZeroKernelEquiv_eq_trans :
    squareZeroKernelEquiv e L M =
      ((squareZeroKernelEquivPoints e L M).trans (squareZeroLiftEquivPoints e L M).symm).trans
        (trivSqZeroExtLiftEquiv (unitResidue e) L M) := by
  have h : (squareZeroKernelEquiv e L M).symm =
      (((squareZeroKernelEquivPoints e L M).trans (squareZeroLiftEquivPoints e L M).symm).trans
        (trivSqZeroExtLiftEquiv (unitResidue e) L M)).symm := by
    ext θ : 1
    rw [squareZeroKernelEquiv_symm_apply, squareZeroKernelOfCotangent_eq, Equiv.symm_trans_apply,
      Equiv.symm_trans_apply, Equiv.symm_symm]
  simpa only [Equiv.symm_symm] using congrArg Equiv.symm h

/-- **Step 3** (Kleiman, proof of Thm 5.11, p. 42). The kernel of `F(L ⊕ M) → F(L)` is the set of
`k`-derivations `𝒪_{P,x₀} → M`, with `𝒪_{P,x₀}` acting on `M` through the residue map: a kernel
element corresponds to the derivation `a ↦ (φ a).snd` of its lift `φ`. -/
def squareZeroKernelEquivDerivation :
    letI := moduleViaAlgHom (unitResidue e) L M
    letI := isScalarTower_moduleViaAlgHom (unitResidue e) L M
    squareZeroKernel F L M ≃ Derivation k (unitStalk e) M :=
  letI := moduleViaAlgHom (unitResidue e) L M
  letI := isScalarTower_moduleViaAlgHom (unitResidue e) L M
  ((squareZeroKernelEquivPoints e L M).trans (squareZeroLiftEquivPoints e L M).symm).trans
    (trivSqZeroExtLiftEquivDerivation (unitResidue e) L M)

variable {L M}

/-- Naturality of the identification in `M`, for the inverse map. -/
theorem squareZeroKernelMap_squareZeroKernelEquiv_symm [Module.Finite L M'] (g : M →ₗ[L] M')
    (θ : CotangentSpace (unitStalk e) →ₗ[k] M) :
    squareZeroKernelMap F g ((squareZeroKernelEquiv e L M).symm θ) =
      (squareZeroKernelEquiv e L M').symm ((g.restrictScalars k).comp θ) := by
  refine Subtype.ext ?_
  change (F.map (specOverMap ((TrivSqZeroExt.map g).restrictScalars k)).op).hom
      (e.homEquiv (squareZeroPoint e L M (trivSqZeroExtLift (unitResidue e) θ))) =
    e.homEquiv (squareZeroPoint e L M' (trivSqZeroExtLift (unitResidue e)
      ((g.restrictScalars k).comp θ)))
  rw [← map_comp_trivSqZeroExtLift, ← locallyNoetherianSpecOverMap_comp_squareZeroPoint,
    homEquiv_comp_apply]
  rfl

/-- **Naturality in `M`.** For an `L`-linear `g : M → M'`, the map of kernels induced by
`TrivSqZeroExt.map g` corresponds to composition with `g`. -/
theorem squareZeroKernelEquiv_map [Module.Finite L M'] (g : M →ₗ[L] M')
    (t : squareZeroKernel F L M) :
    squareZeroKernelEquiv e L M' (squareZeroKernelMap F g t) =
      (g.restrictScalars k).comp (squareZeroKernelEquiv e L M t) := by
  rw [← Equiv.eq_symm_apply, ← squareZeroKernelMap_squareZeroKernelEquiv_symm,
    Equiv.symm_apply_apply]

theorem squareZeroKernelEquiv_zero : squareZeroKernelEquiv e L M 0 = 0 := by
  rw [← Equiv.eq_symm_apply]
  refine Subtype.ext ?_
  change (0 : F.obj (op (specOver k (TrivSqZeroExt L M)))) =
    e.homEquiv (squareZeroPoint e L M (trivSqZeroExtLift (unitResidue e) 0))
  have h : trivSqZeroExtLift (unitResidue e) (0 : CotangentSpace (unitStalk e) →ₗ[k] M) =
      (Algebra.ofId k (TrivSqZeroExt L M)).comp (unitResidue e) :=
    AlgHom.ext fun a => TrivSqZeroExt.ext rfl rfl
  have hp : squareZeroPoint e L M ((Algebra.ofId k (TrivSqZeroExt L M)).comp (unitResidue e)) =
      locallyNoetherianSpecOverMap (Algebra.ofId k (TrivSqZeroExt L M)) ≫ unitSection e := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom
        ((Algebra.ofId k (TrivSqZeroExt L M)).comp (unitResidue e)).toRingHom) ≫
        P.obj.left.fromSpecStalk (unitPoint e) =
      Spec.map (CommRingCat.ofHom (Algebra.ofId k (TrivSqZeroExt L M)).toRingHom) ≫
        (unitSection e).hom.left
    rw [← Spec_stalkClosedPointTo_fromSpecStalk (unitSection e).hom.left, ← Spec.map_comp_assoc]
    rfl
  rw [h, hp, homEquiv_comp_unitSection]

include e in
/-- The relations among the maps of kernels follow from the naturality of the identification. -/
theorem squareZeroKernelMap_comp_apply {M'' : Type u} [AddCommGroup M''] [Module L M'']
    [Module Lᵐᵒᵖ M''] [IsCentralScalar L M''] [Module k M''] [IsScalarTower k L M'']
    [Module.Finite L M'] [Module.Finite L M''] (g : M →ₗ[L] M') (g' : M' →ₗ[L] M'')
    (t : squareZeroKernel F L M) :
    squareZeroKernelMap F g' (squareZeroKernelMap F g t) = squareZeroKernelMap F (g' ∘ₗ g) t := by
  apply (squareZeroKernelEquiv e L M'').injective
  rw [squareZeroKernelEquiv_map e, squareZeroKernelEquiv_map e, squareZeroKernelEquiv_map e]
  rfl

include e in
theorem squareZeroKernelMap_id_apply (t : squareZeroKernel F L M) :
    squareZeroKernelMap F LinearMap.id t = t := by
  apply (squareZeroKernelEquiv e L M).injective
  rw [squareZeroKernelEquiv_map e]
  rfl

include e in
theorem squareZeroKernelMap_zero_apply [Module.Finite L M'] (t : squareZeroKernel F L M) :
    squareZeroKernelMap F (0 : M →ₗ[L] M') t = 0 := by
  apply (squareZeroKernelEquiv e L M').injective
  rw [squareZeroKernelEquiv_map e, squareZeroKernelEquiv_zero e]
  rfl

/-- **Additivity (Kleiman, p. 43).** With `L ⊕ (M × M)` and the maps induced by
`inl, inr : M → M × M` and `fst, snd, fst + snd : M × M → M`, the group structure of
`F(L ⊕ (M × M))` makes the identification additive. -/
theorem squareZeroKernelEquiv_add (t t' : squareZeroKernel F L M) :
    squareZeroKernelEquiv e L M (t + t') =
      squareZeroKernelEquiv e L M t + squareZeroKernelEquiv e L M t' := by
  let T : squareZeroKernel F L (M × M) :=
    squareZeroKernelMap F (LinearMap.inl L M M) t + squareZeroKernelMap F (LinearMap.inr L M M) t'
  have hsum : squareZeroKernelMap F (LinearMap.fst L M M + LinearMap.snd L M M) T = t + t' := by
    simp only [T, map_add, squareZeroKernelMap_comp_apply e]
    rw [show (LinearMap.fst L M M + LinearMap.snd L M M) ∘ₗ LinearMap.inl L M M =
        LinearMap.id from LinearMap.ext fun x => by simp,
      show (LinearMap.fst L M M + LinearMap.snd L M M) ∘ₗ LinearMap.inr L M M =
        LinearMap.id from LinearMap.ext fun x => by simp,
      squareZeroKernelMap_id_apply e, squareZeroKernelMap_id_apply e]
  have hfst : squareZeroKernelMap F (LinearMap.fst L M M) T = t := by
    simp only [T, map_add, squareZeroKernelMap_comp_apply e]
    rw [show LinearMap.fst L M M ∘ₗ LinearMap.inl L M M = LinearMap.id from
        LinearMap.fst_comp_inl L M M,
      show LinearMap.fst L M M ∘ₗ LinearMap.inr L M M = 0 from LinearMap.fst_comp_inr L M M,
      squareZeroKernelMap_id_apply e, squareZeroKernelMap_zero_apply e, add_zero]
  have hsnd : squareZeroKernelMap F (LinearMap.snd L M M) T = t' := by
    simp only [T, map_add, squareZeroKernelMap_comp_apply e]
    rw [show LinearMap.snd L M M ∘ₗ LinearMap.inl L M M = 0 from LinearMap.snd_comp_inl L M M,
      show LinearMap.snd L M M ∘ₗ LinearMap.inr L M M = LinearMap.id from
        LinearMap.snd_comp_inr L M M,
      squareZeroKernelMap_id_apply e, squareZeroKernelMap_zero_apply e, zero_add]
  rw [← hsum, squareZeroKernelEquiv_map e, ← hfst, ← hsnd, squareZeroKernelEquiv_map e,
    squareZeroKernelEquiv_map e]
  rfl

variable (L M)

/-- The identification of the kernel with `Hom_k(𝔪/𝔪², M)`, as an additive isomorphism. -/
def squareZeroKernelAddEquiv :
    squareZeroKernel F L M ≃+ (CotangentSpace (unitStalk e) →ₗ[k] M) :=
  { squareZeroKernelEquiv e L M with map_add' := squareZeroKernelEquiv_add e }

theorem squareZeroKernelAddEquiv_apply (t : squareZeroKernel F L M) :
    squareZeroKernelAddEquiv e L M t = squareZeroKernelEquiv e L M t :=
  rfl

variable (F) in
/-- The scalar action `a • t = F(µ_a) t` on the kernel, with `µ_a = TrivSqZeroExt.map (a • id)`. -/
abbrev squareZeroKernelSMul : SMul L (squareZeroKernel F L M) :=
  ⟨fun a t => squareZeroKernelMap F (a • LinearMap.id) t⟩

theorem squareZeroKernelEquiv_smul (a : L) (t : squareZeroKernel F L M) :
    squareZeroKernelEquiv e L M (squareZeroKernelMap F (a • LinearMap.id) t) =
      a • squareZeroKernelEquiv e L M t := by
  rw [squareZeroKernelEquiv_map e]
  rfl

/-- The `L`-module structure on the kernel with `a • t = F(µ_a) t`. Its scalar action does not
depend on `e`; the module axioms are transported along `squareZeroKernelAddEquiv`. -/
abbrev squareZeroKernelModule : Module L (squareZeroKernel F L M) :=
  letI := squareZeroKernelSMul F L M
  Function.Injective.module L (squareZeroKernelAddEquiv e L M).toAddMonoidHom
    (squareZeroKernelAddEquiv e L M).injective (squareZeroKernelEquiv_smul e L M)

theorem squareZeroKernelModule_smul_def (a : L) (t : squareZeroKernel F L M) :
    letI := squareZeroKernelModule e L M
    a • t = squareZeroKernelMap F (a • LinearMap.id) t :=
  rfl

/-- **Kleiman (5.11.2)–(5.11.3).** The identification of the kernel with `Hom_k(𝔪/𝔪², M)` is
`L`-linear for the scalar action `a • t = F(µ_a) t`. -/
def squareZeroKernelLinearEquiv :
    letI := squareZeroKernelModule e L M
    squareZeroKernel F L M ≃ₗ[L] (CotangentSpace (unitStalk e) →ₗ[k] M) :=
  letI := squareZeroKernelModule e L M
  { squareZeroKernelAddEquiv e L M with map_smul' := squareZeroKernelEquiv_smul e L M }

theorem finite_squareZeroKernel :
    letI := squareZeroKernelModule e L M
    Module.Finite L (squareZeroKernel F L M) := by
  let := squareZeroKernelModule e L M
  have := finite_cotangentSpace_of_algHom (unitResidue e)
  exact Module.Finite.equiv (squareZeroKernelLinearEquiv e L M).symm

/-- **Rank formula.** `finrank_L ker(F(L ⊕ M) → F(L)) = finrank_k (𝔪/𝔪²) · finrank_L M`. -/
theorem finrank_squareZeroKernel :
    letI := squareZeroKernelModule e L M
    Module.finrank L (squareZeroKernel F L M) =
      Module.finrank k (CotangentSpace (unitStalk e)) * Module.finrank L M := by
  let := squareZeroKernelModule e L M
  have := finite_cotangentSpace_of_algHom (unitResidue e)
  rw [(squareZeroKernelLinearEquiv e L M).finrank_eq, Module.finrank_linearMap]

/-! ### The tangent kernel `ker(F(L[ε]) → F(L))` -/

/-- **Kleiman (5.11.1)–(5.11.3).** The tangent kernel `ker(F(L[ε]) → F(L))` is
`Hom_k(𝔪/𝔪², L)`, additively. -/
abbrev tangentKernelEquiv : tangentKernel F L ≃+ (CotangentSpace (unitStalk e) →ₗ[k] L) :=
  squareZeroKernelAddEquiv e L L

/-- The scaling `µ_a : ε ↦ a ε` acts on the tangent kernel as scalar multiplication by `a`. -/
theorem tangentKernelEquiv_scale (a : L) (t : tangentKernel F L) :
    tangentKernelEquiv e L (squareZeroKernelMap F (a • LinearMap.id) t) =
      a • tangentKernelEquiv e L t :=
  squareZeroKernelEquiv_smul e L L a t

/-- The `L`-vector space structure on the tangent kernel with `a • t = F(µ_a) t`. -/
abbrev tangentKernelModule : Module L (tangentKernel F L) :=
  squareZeroKernelModule e L L

/-- The tangent kernel is `Hom_k(𝔪/𝔪², L)` as an `L`-vector space. -/
abbrev tangentKernelLinearEquiv :
    letI := tangentKernelModule e L
    tangentKernel F L ≃ₗ[L] (CotangentSpace (unitStalk e) →ₗ[k] L) :=
  squareZeroKernelLinearEquiv e L L

theorem finite_tangentKernel :
    letI := tangentKernelModule e L
    Module.Finite L (tangentKernel F L) :=
  finite_squareZeroKernel e L L

/-- **Rank formula.** `finrank_L ker(F(L[ε]) → F(L)) = finrank_k (𝔪/𝔪²)`, the embedding
dimension of `P` at the unit point. -/
theorem finrank_tangentKernel :
    letI := tangentKernelModule e L
    Module.finrank L (tangentKernel F L) = Module.finrank k (CotangentSpace (unitStalk e)) := by
  rw [finrank_squareZeroKernel e L L, Module.finrank_self, mul_one]

end TangentKernel

end AlgebraicGeometry.Scheme
