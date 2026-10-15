# Descent across finite purely inseparable field extensions

[BaseChange](BaseChange.lean), imported as `Aglib.RingTheory.Descent.PurelyInseparable.BaseChange`, constructs actual descent data over `R ⊗[K] L` for a commutative `K`-algebra `R`. The fields satisfy finite purely inseparable `L/K`; the algebra being descended carries the stated formal-etale/etale structure. No Noetherian premise is inserted on `R`.

In `Algebra.Descent.PurelyInseparable`, the base-changed overlap and invariant reconstruction use literal tensor-product maps. Finite/etale properties of the invariants retain their module-finite or etale inputs. [Morphisms](Morphisms.lean) supplies the global tensor-map full-faithfulness result and descent of the actual algebra morphism.

The lower [purely inseparable tensor augmentation](../../TensorProduct/PurelyInseparable.lean) proves the nil/nilpotent overlap-kernel statement, and [nilpotent descent](../Nilpotent.lean) constructs the coaction. Original finite-etale applications remain external consumers of these general algebra objects/maps.
