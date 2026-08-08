import GreenFrame.Concrete.Finite.CoordinateCutoffs

/-!
# Finiteness of the literal retained coordinate sets

The finite-section operators stay in the ambient Hilbert spaces, avoiding an
arbitrary enumeration of rows.  This checkpoint nevertheless proves that the
retained state, residual, depth-one, and bulk index types are genuinely
finite.  The encodings retain both the current number and the physical base.
-/

namespace GreenFrame.Concrete

instance retainedStateIndexFinite (N : ℕ) :
    Finite (RetainedStateIndex N) := by
  let encode : RetainedStateIndex N → Fin (N + 1) := fun n =>
    ⟨(n.1 : ℕ), Nat.lt_succ_of_le n.2⟩
  apply Finite.of_injective encode
  intro a b h
  apply Subtype.ext
  apply PNat.eq
  exact congrArg Fin.val h

instance retainedResidualEventFinite (N : ℕ) :
    Finite (RetainedResidualEvent N) := by
  let encode : RetainedResidualEvent N → Fin (N + 1) × Fin (N + 1) :=
    fun e =>
      (⟨(e.1.1 : ℕ), Nat.lt_succ_of_le e.2.1⟩,
        ⟨e.1.2, Nat.lt_succ_of_le (by
          have hb := e.2.2
          simp only [baseNat] at hb
          omega)⟩)
  apply Finite.of_injective encode
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · apply PNat.eq
    exact congrArg (fun z => z.1.val) h
  · exact congrArg (fun z => z.2.val) h

instance retainedGreenEventFinite (N : ℕ) :
    Finite (RetainedGreenEvent N) := by
  let encode : RetainedGreenEvent N → Fin (N + 1) × Fin (N + 1) :=
    fun e =>
      (⟨e.1.1, Nat.lt_succ_of_le (by
          have hb := e.2.2
          simp only [baseNat] at hb
          omega)⟩,
        ⟨(e.1.2 : ℕ),
          Nat.lt_succ_of_le (greenEventRetained_parent e.2)⟩)
  apply Finite.of_injective encode
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z => z.1.val) h
  · apply PNat.eq
    exact congrArg (fun z => z.2.val) h

instance retainedDepthOneEventFinite (N : ℕ) :
    Finite (RetainedDepthOneEvent N) := by
  let encode : RetainedDepthOneEvent N → RetainedGreenEvent N :=
    fun e => ⟨e.1.1, e.2⟩
  apply Finite.of_injective encode
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Subtype.val h

instance retainedBulkEventFinite (N : ℕ) :
    Finite (RetainedBulkEvent N) := by
  let encode : RetainedBulkEvent N → RetainedGreenEvent N :=
    fun e => ⟨e.1.1, e.2⟩
  apply Finite.of_injective encode
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Subtype.val h

end GreenFrame.Concrete
