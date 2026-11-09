import TsigmaProof.Even
import TsigmaProof.Odd

/-! # `n = 8` and `n = 9`: the weighted orders of Table `tbl:small-orders`

Generated mechanically from Table `tbl:small-orders` of paper 1; every claim is checked by `decide`. -/

namespace Tsigma

/-- The position of a vertex in an order written as a list (first = 0). -/
def pos {V : Type} [DecidableEq V] (o : List V) (v : V) : ℕ := o.idxOf v

namespace Even

instance (k : ℕ) (v : V) : Decidable (valid k v) := by unfold valid; split <;> infer_instance
instance (k : ℕ) (x y : V) : Decidable (garc k x y) := by unfold garc; split <;> infer_instance
instance (k : ℕ) (x y : V) : Decidable (tarc k x y) := by unfold tarc; infer_instance

/-- The 14 weighted orders for `n = 8`. -/
def cert8 : List (ℕ × (V → ℕ)) :=
  [(5, pos [.T2, .T1, (.U 1), .T3, (.W 1), .P1, .P2, .T0]),
   (3, pos [.P1, (.U 1), (.W 1), .P2, .T0, .T2, .T1, .T3]),
   (1, pos [.T3, .P1, .T1, (.U 1), .P2, .T0, (.W 1), .T2]),
   (1, pos [(.W 1), .T1, .P2, .T0, .T2, .T3, .P1, (.U 1)]),
   (1, pos [.T3, .P2, .T2, .P1, (.U 1), (.W 1), .T0, .T1]),
   (1, pos [(.W 1), .T2, .P1, .T0, .T1, (.U 1), .T3, .P2]),
   (1, pos [(.U 1), .P2, .T0, .T2, .T3, (.W 1), .P1, .T1]),
   (1, pos [.P2, .T0, .T3, (.W 1), .T2, .P1, .T1, (.U 1)]),
   (1, pos [.T0, .T3, .P2, (.W 1), .T2, .P1, .T1, (.U 1)]),
   (1, pos [(.U 1), .T0, .T3, (.W 1), .T1, .P2, .T2, .P1]),
   (1, pos [.T0, .T3, .P1, (.W 1), .T1, .P2, .T2, (.U 1)]),
   (1, pos [.P1, (.U 1), .T0, .T1, .T3, (.W 1), .P2, .T2]),
   (1, pos [(.W 1), .P1, .T0, .T1, .P2, .T2, (.U 1), .T3]),
   (1, pos [(.W 1), .T0, .T2, .P1, .T1, (.U 1), .T3, .P2])]

theorem cert8_total : (cert8.map Prod.fst).sum = 20 := by decide

theorem cert8_inj : ∀ p ∈ cert8, ∀ x y, valid 1 x → valid 1 y → x ≠ y → p.2 x ≠ p.2 y := by
  have h : ∀ p ∈ cert8, ∀ x ∈ vs 1, ∀ y ∈ vs 1, x ≠ y → p.2 x ≠ p.2 y := by decide
  intro p hp x y hx hy
  exact h p hp x ((mem_vs 1 x).2 hx) y ((mem_vs 1 y).2 hy)

theorem bob8 : BobFwd cert8 (tarc 1) (vs 1) 13 := by
  unfold BobFwd
  decide

end Even

namespace Odd

instance (k : ℕ) (v : V) : Decidable (valid k v) := by unfold valid; split <;> infer_instance
instance (k : ℕ) (x y : V) : Decidable (garc k x y) := by unfold garc; split <;> infer_instance
instance (k : ℕ) (x y : V) : Decidable (tarc k x y) := by unfold tarc; infer_instance

/-- The 17 weighted orders for `n = 9`. -/
def cert9 : List (ℕ × (V → ℕ)) :=
  [(7, pos [.F, .H, .G, .N0, .N1, .N2, .N3, .P1, .P2]),
   (1, pos [.H, .P2, .G, .N0, .N1, .N2, .N3, .F, .P1]),
   (1, pos [.N2, .N3, .F, .P2, .G, .P1, .H, .N0, .N1]),
   (1, pos [.P2, .N1, .N3, .G, .P1, .H, .N2, .F, .N0]),
   (1, pos [.P1, .N0, .N3, .H, .P2, .G, .N2, .F, .N1]),
   (1, pos [.N3, .G, .P1, .H, .N0, .N2, .F, .P2, .N1]),
   (1, pos [.F, .P1, .N0, .N3, .H, .P2, .G, .N1, .N2]),
   (1, pos [.P2, .N1, .P1, .N0, .N3, .H, .G, .N2, .F]),
   (1, pos [.P1, .N0, .P2, .N1, .N3, .H, .G, .N2, .F]),
   (1, pos [.N2, .N3, .F, .P1, .H, .N0, .P2, .N1, .G]),
   (1, pos [.N2, .P1, .N0, .N3, .F, .H, .P2, .G, .N1]),
   (1, pos [.P1, .N0, .N2, .N3, .H, .F, .P2, .G, .N1]),
   (1, pos [.N1, .P1, .N0, .N3, .H, .N2, .F, .P2, .G]),
   (1, pos [.P2, .N1, .N3, .G, .N2, .F, .P1, .N0, .H]),
   (1, pos [.N2, .N3, .F, .P2, .G, .N1, .P1, .H, .N0]),
   (1, pos [.N2, .P2, .N1, .N3, .F, .G, .P1, .H, .N0]),
   (1, pos [.P2, .N1, .N2, .N3, .G, .F, .P1, .H, .N0])]

theorem cert9_total : (cert9.map Prod.fst).sum = 23 := by decide

theorem cert9_inj : ∀ p ∈ cert9, ∀ x y, valid 0 x → valid 0 y → x ≠ y → p.2 x ≠ p.2 y := by
  have h : ∀ p ∈ cert9, ∀ x ∈ vs 0, ∀ y ∈ vs 0, x ≠ y → p.2 x ≠ p.2 y := by decide
  intro p hp x y hx hy
  exact h p hp x ((mem_vs 0 x).2 hx) y ((mem_vs 0 y).2 hy)

theorem bob9 : BobFwd cert9 (tarc 0) (vs 0) 15 := by
  unfold BobFwd
  decide

end Odd

end Tsigma
