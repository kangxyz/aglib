/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.KernelMap
public import Aglib.AlgebraicGeometry.Picard.Tangent.Points

/-!
# Tangent kernels over a field and over a field extension in the dual-number test objects

Let `k` be a field and `F : (Over (Spec k))ᵒᵖ ⥤ AddCommGrpCat` any functor. For a field `L` over
`k`, the tangent kernel `ker(F(L[ε]) → F(L))` of `Picard/Tangent/Points` (`tangentKernel F L`) is
formed with the test objects `specOver k L[ε]` and `specOver k L` and the closed point
`specOverMap (TrivSqZeroExt.fstHom k L L)`; its scalars are `a • t = F(µ_a) t` for
`µ_a = TrivSqZeroExt.map (a • id)` (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of
Thm 5.11, p. 42, after (5.11.1)). `Picard/Tangent/Comparison` uses instead the `L`-schemes
`Over.mk (dualMap L)` and `Over.mk (𝟙 (Spec L))`, the closed point `DualNumbers.closedPointOver L`
and the scaling `DualNumbers.scaleOver L a`. This file compares the two presentations.

* Over `k` itself: `specOver k k[ε]` is `Over.mk (dualMap k)` by definition, but `specOver k k`
  is `Spec k` over itself through `Spec (algebraMap k k)`, which is the identity only through
  `Spec.map_id` (`specOverSelfIso`). Hence `tangentKernel F k = ker F(closedPointOver k)`
  (`tangentKernel_eq_ker_closedPointOver`), and `µ_a` is `scaleOver k a`
  (`specOverMap_map_smul_id_eq_scaleOver`, from `DualNumbers.scaleRingHom_eq_restrictScalars_map`).
  For a representation `e` on locally Noetherian test schemes, an additive map
  `v : V →+ ker F(closedPointOver k)` with `v (a • c) = F(scaleOver k a) (v c)` is a `k`-linear
  map `V →ₗ[k] tangentKernel F k` for `tangentKernelModule e k` (`linearMapToTangentKernel`).
* Over a field extension `K/k`, with `g := Spec (algebraMap k K) : Spec K ⟶ Spec k`: the
  `k`-schemes `specOver k K[ε]` and `specOver k K` are the `K`-schemes `Spec K[ε]` and `Spec K`
  viewed over `Spec k` through `Over.map g` (`specOverDualNumberIso`, `specOverFieldIso`, with
  identity underlying morphisms), compatibly with the closed points and the scalings. Hence `F`
  identifies the kernel of `F(Over.map g (closedPointOver K))` with `tangentKernel F K`
  (`kerClosedPointOverAddEquivTangentKernel`), carrying `F(Over.map g (scaleOver K a))` to
  `F(µ_a)` (`map_scaleOver_specOverDualNumberIso`). For a functor `G` on `K`-schemes with an
  equivalence `E` from the kernel of `G(closedPointOver K)` to that of
  `F(Over.map g (closedPointOver K))` compatible with the scalings, an additive map `v` into the
  kernel of `G(closedPointOver K)`, linear for `G(scaleOver K a)`, gives a `K`-linear map
  `V →ₗ[K] tangentKernel F K` for `tangentKernelModule e K`
  (`linearMapToTangentKernelOfFieldExtension`), bijective if `v` is; then
  `linearEquivTangentKernelOfFieldExtension : tangentKernel F K ≃ₗ[K] V` is its inverse.

No hypothesis on `F` is used. The current consumer is `Picard/Tangent/StructureCohomology`,
which applies both items to `F = Pic_{X/k,(fppf)}`, with `G = Pic_{X_K/K,(fppf)}` and `E` the
base change of the Picard sheaf (Kleiman, Ex. 4.4, p. 27, and Answer 4.4, p. 65).

The comparisons go through the isomorphisms `specOverSelfIso` and `specOverDualNumberIso` and
through `AddEquiv.addSubgroupCongr`, never through a definitional identification of the two
`Over` objects or of the two kernels: such identifications are not definitional
(`Spec (algebraMap k k)` is the identity only through `Spec.map_id`), and asking the kernel to
check them is very expensive.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe w u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (F : (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w})
variable {P : LocallyNoetherianOver (Spec (.of k))}
  (e : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ F ⋙
    CategoryTheory.forget AddCommGrpCat.{w}).RepresentableBy P)

section Self

variable (k) in
/-- `Spec (algebraMap k k)` is the identity of `Spec k`. -/
theorem spec_map_algebraMap_self :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) :=
  (congrArg Spec.map (show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from
    rfl)).trans (Spec.map_id _)

-- The underlying isomorphism is typed at `Spec k`, not at the `left` of either object, so that
-- checking it does not compare the two objects of `Over (Spec k)`.
variable (k) in
/-- `Spec k` over itself through `Spec (algebraMap k k)` (`specOver k k`) is `Spec k` over itself
through the identity, by the identity morphism. -/
def specOverSelfIso : specOver k k ≅ Over.mk (𝟙 (Spec (.of k))) :=
  Over.isoMk (Iso.refl (Spec (.of k)))
    ((Category.comp_id _).trans (spec_map_algebraMap_self k).symm)

@[simp]
theorem specOverSelfIso_hom_left : (specOverSelfIso k).hom.left = 𝟙 (Spec (.of k)) :=
  rfl

/-- The closed point `Spec k ⟶ Spec k[ε]` of `Picard/Tangent/Points` is `closedPointOver k` after
`specOverSelfIso k`. -/
theorem specOverMap_fstHom_eq_specOverSelfIso_hom_comp_closedPointOver :
    specOverMap (TrivSqZeroExt.fstHom k k k) =
      (specOverSelfIso k).hom ≫ DualNumbers.closedPointOver k :=
  Over.OverMorphism.ext (Category.id_comp _).symm

/-- **The tangent kernel over `k` in the dual-number test objects**: the kernel of
`F(k[ε]) → F(k)` of `Picard/Tangent/Points` is the kernel of `F(closedPointOver k)`. -/
theorem tangentKernel_eq_ker_closedPointOver :
    tangentKernel F k = (F.map (DualNumbers.closedPointOver k).op).hom.ker := by
  have hinj : Function.Injective (F.map (specOverSelfIso k).hom.op).hom :=
    (F.mapIso (specOverSelfIso k).op).addCommGroupIsoToAddEquiv.injective
  have h : F.map (specOverMap (TrivSqZeroExt.fstHom k k k)).op =
      F.map (DualNumbers.closedPointOver k).op ≫ F.map (specOverSelfIso k).hom.op := by
    rw [specOverMap_fstHom_eq_specOverSelfIso_hom_comp_closedPointOver, op_comp, F.map_comp]
  ext t
  change (F.map (specOverMap (TrivSqZeroExt.fstHom k k k)).op).hom t = 0 ↔
    (F.map (DualNumbers.closedPointOver k).op).hom t = 0
  rw [h, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
  exact (injective_iff_map_eq_zero' _).mp hinj _

/-- The scaling `µ_a = TrivSqZeroExt.map (a • id)` of `Picard/Tangent/Points` is
`DualNumbers.scaleOver k a`. -/
theorem specOverMap_map_smul_id_eq_scaleOver (a : k) :
    specOverMap ((TrivSqZeroExt.map (a • LinearMap.id : k →ₗ[k] k)).restrictScalars k) =
      DualNumbers.scaleOver k a :=
  Over.OverMorphism.ext (congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (DualNumbers.scaleRingHom_eq_restrictScalars_map k a).symm)

/-- The scalar action of `tangentKernelModule e L` on values: `a • t` is `F(µ_a) t` for
`µ_a = TrivSqZeroExt.map (a • id)`. -/
theorem coe_smul_tangentKernel (L : Type u) [Field L] [Algebra k L] (a : L)
    (t : tangentKernel F L) :
    letI := tangentKernelModule e L
    ((a • t : tangentKernel F L) : F.obj (op (specOver k (TrivSqZeroExt L L)))) =
      (F.map (specOverMap
        ((TrivSqZeroExt.map (a • LinearMap.id : L →ₗ[L] L)).restrictScalars k)).op).hom t :=
  rfl

/-- Over `k`, the scalar action of `tangentKernelModule e k` on values is `F(scaleOver k a)`. -/
theorem coe_smul_tangentKernel_eq_map_scaleOver (a : k) (t : tangentKernel F k) :
    letI := tangentKernelModule e k
    ((a • t : tangentKernel F k) : F.obj (op (specOver k (TrivSqZeroExt k k)))) =
      (F.map (DualNumbers.scaleOver k a).op).hom t := by
  rw [coe_smul_tangentKernel F e k a t, specOverMap_map_smul_id_eq_scaleOver]

variable {V : Type*} [AddCommGroup V] [Module k V]
  (v : V →+ (F.map (DualNumbers.closedPointOver k).op).hom.ker)
  (hv : ∀ (a : k) (c : V), (v (a • c) : F.obj (op (Over.mk (DualNumbers.dualMap k)))) =
    (F.map (DualNumbers.scaleOver k a).op).hom (v c))

/-- **A `k`-linear map into the tangent kernel**: an additive map `v` into the kernel of
`F(closedPointOver k)` with `v (a • c) = F(scaleOver k a) (v c)`, viewed in `tangentKernel F k`
(through `tangentKernel_eq_ker_closedPointOver`), is `k`-linear for `a • t = F(µ_a) t`. -/
def linearMapToTangentKernel :
    letI := tangentKernelModule e k
    V →ₗ[k] tangentKernel F k :=
  letI := tangentKernelModule e k
  { (AddEquiv.addSubgroupCongr (tangentKernel_eq_ker_closedPointOver F).symm).toAddMonoidHom.comp
      v with
    map_smul' := fun a c => Subtype.ext (by
      change ((AddEquiv.addSubgroupCongr (tangentKernel_eq_ker_closedPointOver F).symm
          (v (a • c)) : tangentKernel F k) : F.obj (op (specOver k (TrivSqZeroExt k k)))) =
        ((a • AddEquiv.addSubgroupCongr (tangentKernel_eq_ker_closedPointOver F).symm (v c) :
          tangentKernel F k) : F.obj (op (specOver k (TrivSqZeroExt k k))))
      rw [AddEquiv.addSubgroupCongr_apply, coe_smul_tangentKernel_eq_map_scaleOver,
        AddEquiv.addSubgroupCongr_apply]
      exact hv a c) }

/-- The value of `linearMapToTangentKernel` is the value of `v`. -/
theorem coe_linearMapToTangentKernel_apply (c : V) :
    (linearMapToTangentKernel F e v hv c : F.obj (op (specOver k (TrivSqZeroExt k k)))) =
      (v c : F.obj (op (Over.mk (DualNumbers.dualMap k)))) :=
  AddEquiv.addSubgroupCongr_apply (tangentKernel_eq_ker_closedPointOver F).symm (v c)

theorem linearMapToTangentKernel_injective (hinj : Function.Injective v) :
    Function.Injective (linearMapToTangentKernel F e v hv) :=
  (AddEquiv.addSubgroupCongr (tangentKernel_eq_ker_closedPointOver F).symm).injective.comp hinj

end Self

section FieldExtension

variable (K : Type u) [Field K] [Algebra k K]

variable (k) in
/-- `Spec (k → K[ε])` is `Spec (K → K[ε])` followed by `Spec (k → K)`. -/
theorem dualMap_comp_spec_map_algebraMap :
    DualNumbers.dualMap K ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt K K))) :=
  (Spec.map_comp _ _).symm.trans
    (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun _ => rfl)))

variable (k) in
/-- `Spec K[ε]` over `Spec k` (`specOver k K[ε]`) is the `K`-scheme `Spec K[ε]` viewed over
`Spec k` through `Spec K ⟶ Spec k`, by the identity morphism. -/
def specOverDualNumberIso :
    specOver k (TrivSqZeroExt K K) ≅
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
        (Over.mk (DualNumbers.dualMap K)) :=
  Over.isoMk (Iso.refl (Spec (.of (TrivSqZeroExt K K))))
    ((Category.id_comp _).trans (dualMap_comp_spec_map_algebraMap k K))

variable (k) in
/-- `Spec K` over `Spec k` (`specOver k K`) is the `K`-scheme `Spec K` viewed over `Spec k` through
`Spec K ⟶ Spec k`, by the identity morphism. -/
def specOverFieldIso :
    specOver k K ≅
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
        (Over.mk (𝟙 (Spec (.of K)))) :=
  Over.isoMk (Iso.refl (Spec (.of K))) ((Category.id_comp _).trans (Category.id_comp _))

variable (k) in
@[simp]
theorem specOverDualNumberIso_hom_left :
    (specOverDualNumberIso k K).hom.left = 𝟙 (Spec (.of (TrivSqZeroExt K K))) :=
  rfl

variable (k) in
@[simp]
theorem specOverFieldIso_hom_left : (specOverFieldIso k K).hom.left = 𝟙 (Spec (.of K)) :=
  rfl

variable {K}

/-- The closed points correspond: `ρ : Spec K ⟶ Spec K[ε]` of `Picard/Tangent/Points` is
`closedPointOver K` viewed over `Spec k`. -/
theorem specOverMap_fstHom_comp_specOverDualNumberIso_hom :
    specOverMap (TrivSqZeroExt.fstHom k K K) ≫ (specOverDualNumberIso k K).hom =
      (specOverFieldIso k K).hom ≫
        (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
          (DualNumbers.closedPointOver K) :=
  Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The scalings correspond: `µ_a = TrivSqZeroExt.map (a • id)` of `Picard/Tangent/Points` is
`scaleOver K a` viewed over `Spec k`. -/
theorem specOverMap_map_smul_id_comp_specOverDualNumberIso_hom (a : K) :
    specOverMap ((TrivSqZeroExt.map (a • LinearMap.id : K →ₗ[K] K)).restrictScalars k) ≫
        (specOverDualNumberIso k K).hom =
      (specOverDualNumberIso k K).hom ≫
        (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
          (DualNumbers.scaleOver K a) :=
  Over.OverMorphism.ext ((Category.comp_id _).trans
    ((congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (DualNumbers.scaleRingHom_eq_map K a).symm).trans (Category.id_comp _).symm))

variable (K)

/-- **The tangent kernel over a field extension `K/k`** in the dual-number test objects over `K`:
for `g : Spec K ⟶ Spec k`, `F(specOverDualNumberIso k K)` identifies the kernel of
`F(Spec K[ε]) → F(Spec K)`, for the `K`-schemes `Spec K[ε]` and `Spec K` viewed over `Spec k`
(`Over.map g`), with the tangent kernel `ker(F(K[ε]) → F(K))` of `Picard/Tangent/Points`. -/
def kerClosedPointOverAddEquivTangentKernel :
    (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
      (DualNumbers.closedPointOver K)).op).hom.ker ≃+ tangentKernel F K :=
  AddMonoidHom.kerAddEquivOfComm
    (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
      (DualNumbers.closedPointOver K)).op).hom
    (F.map (specOverMap (TrivSqZeroExt.fstHom k K K)).op).hom
    (F.mapIso (specOverDualNumberIso k K).op).addCommGroupIsoToAddEquiv
    (F.map (specOverFieldIso k K).hom.op).hom
    (F.mapIso (specOverFieldIso k K).op).addCommGroupIsoToAddEquiv.injective
    (fun y => by
      have h : F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
            (DualNumbers.closedPointOver K)).op ≫ F.map (specOverFieldIso k K).hom.op =
          F.map (specOverDualNumberIso k K).hom.op ≫
            F.map (specOverMap (TrivSqZeroExt.fstHom k K K)).op := by
        rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp,
          specOverMap_fstHom_comp_specOverDualNumberIso_hom]
      exact congrArg (fun φ => φ.hom y) h)

theorem coe_kerClosedPointOverAddEquivTangentKernel_apply
    (y : (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
      (DualNumbers.closedPointOver K)).op).hom.ker) :
    (kerClosedPointOverAddEquivTangentKernel F K y :
        F.obj (op (specOver k (TrivSqZeroExt K K)))) =
      (F.map (specOverDualNumberIso k K).hom.op).hom y :=
  rfl

variable {K}

/-- `F(specOverDualNumberIso k K)` carries `F` of the scaling `scaleOver K a`, viewed over `Spec k`,
to `F(µ_a)` for `µ_a = TrivSqZeroExt.map (a • id)`. -/
theorem map_scaleOver_specOverDualNumberIso (a : K)
    (y : F.obj (op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
      (Over.mk (DualNumbers.dualMap K))))) :
    (F.map (specOverDualNumberIso k K).hom.op).hom
        ((F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
          (DualNumbers.scaleOver K a)).op).hom y) =
      (F.map (specOverMap
          ((TrivSqZeroExt.map (a • LinearMap.id : K →ₗ[K] K)).restrictScalars k)).op).hom
        ((F.map (specOverDualNumberIso k K).hom.op).hom y) := by
  have h : F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
        (DualNumbers.scaleOver K a)).op ≫ F.map (specOverDualNumberIso k K).hom.op =
      F.map (specOverDualNumberIso k K).hom.op ≫
        F.map (specOverMap
          ((TrivSqZeroExt.map (a • LinearMap.id : K →ₗ[K] K)).restrictScalars k)).op := by
    rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp,
      specOverMap_map_smul_id_comp_specOverDualNumberIso_hom]
  exact congrArg (fun φ => φ.hom y) h

variable {F} (G : (Over (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{w})
  (E : (G.map (DualNumbers.closedPointOver K).op).hom.ker ≃+
    (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
      (DualNumbers.closedPointOver K)).op).hom.ker)
  (hE : ∀ (a : K) (y y' : (G.map (DualNumbers.closedPointOver K).op).hom.ker),
    (y' : G.obj (op (Over.mk (DualNumbers.dualMap K)))) =
        (G.map (DualNumbers.scaleOver K a).op).hom y →
      (E y' : F.obj (op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
          (Over.mk (DualNumbers.dualMap K))))) =
        (F.map ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
          (DualNumbers.scaleOver K a)).op).hom (E y))
  {V : Type*} [AddCommGroup V] [Module K V]
  (v : V →+ (G.map (DualNumbers.closedPointOver K).op).hom.ker)
  (hv : ∀ (a : K) (c : V), (v (a • c) : G.obj (op (Over.mk (DualNumbers.dualMap K)))) =
    (G.map (DualNumbers.scaleOver K a).op).hom (v c))

/-- **A `K`-linear map into the tangent kernel over a field extension**: let `G` be a functor on
`K`-schemes with an additive equivalence `E` from the kernel of `G(closedPointOver K)` to the
kernel of `F(closedPointOver K)` viewed over `Spec k`, compatible with the scalings (for example
the base change of a Picard sheaf). An additive map `v` into the kernel of `G(closedPointOver K)`
with `v (a • c) = G(scaleOver K a) (v c)`, followed by `E` and
`kerClosedPointOverAddEquivTangentKernel`, is `K`-linear for `a • t = F(µ_a) t`. -/
def linearMapToTangentKernelOfFieldExtension :
    letI := tangentKernelModule e K
    V →ₗ[K] tangentKernel F K :=
  letI := tangentKernelModule e K
  { ((kerClosedPointOverAddEquivTangentKernel F K).toAddMonoidHom.comp E.toAddMonoidHom).comp
      v with
    map_smul' := fun a c => Subtype.ext (by
      change ((kerClosedPointOverAddEquivTangentKernel F K (E (v (a • c))) : tangentKernel F K) :
          F.obj (op (specOver k (TrivSqZeroExt K K)))) =
        ((a • kerClosedPointOverAddEquivTangentKernel F K (E (v c)) : tangentKernel F K) :
          F.obj (op (specOver k (TrivSqZeroExt K K))))
      rw [coe_smul_tangentKernel F e K a, coe_kerClosedPointOverAddEquivTangentKernel_apply,
        coe_kerClosedPointOverAddEquivTangentKernel_apply, hE a (v c) (v (a • c)) (hv a c),
        map_scaleOver_specOverDualNumberIso]) }

theorem linearMapToTangentKernelOfFieldExtension_bijective (hbij : Function.Bijective v) :
    Function.Bijective (linearMapToTangentKernelOfFieldExtension e G E hE v hv) :=
  ((kerClosedPointOverAddEquivTangentKernel F K).bijective.comp E.bijective).comp hbij

/-- **The tangent kernel over a field extension as a `K`-vector space**: if `v` is bijective,
`linearMapToTangentKernelOfFieldExtension` is a `K`-linear equivalence; this is its inverse
`ker(F(K[ε]) → F(K)) ≃ₗ[K] V`. -/
def linearEquivTangentKernelOfFieldExtension (hbij : Function.Bijective v) :
    letI := tangentKernelModule e K
    tangentKernel F K ≃ₗ[K] V :=
  letI := tangentKernelModule e K
  (LinearEquiv.ofBijective (linearMapToTangentKernelOfFieldExtension e G E hE v hv)
    (linearMapToTangentKernelOfFieldExtension_bijective e G E hE v hv hbij)).symm

end FieldExtension

end AlgebraicGeometry.Scheme
