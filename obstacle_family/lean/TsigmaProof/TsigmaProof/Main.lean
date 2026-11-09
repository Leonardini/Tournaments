import TsigmaProof.UpperEven
import TsigmaProof.UpperOdd
import TsigmaProof.Small

/-!
# Theorem `thm:family-value` of paper 1

For every `n ≥ 8`, the completion `Ĝ_n` (even `n`) or `Ĥ_n` (odd `n`), and the obstacle `G_n` or
`H_n` itself, have predictability exactly `(2n - 3) / (3n - 4)`.

The predictability is the value of the game in which Alice picks an arc and Bob a linear order,
Bob winning if the arc is forward.  With integer weights (`Common.lean`):

* Bob has linear orders (rankings injective on the vertices) with weights totalling `3n - 4` under
  which every arc is forward with weight at least `2n - 3`;
* Alice has arcs of the obstacle, each with weight 1, totalling `3n - 4`, of which every ranking
  makes at most `2n - 3` forward.

By weak duality (`weak_duality`), no strategy of either player does better, which is the
statement that the value is `(2n - 3) / (3n - 4)` (`*_value_exact` below).  Here `n = 2k + 6`
(even) or `n = 2k + 9` (odd).
-/

namespace Tsigma

namespace Even

theorem garc_irrefl (k : ℕ) (x : V) : ¬ garc k x x := by
  rcases x with _ | _ | _ | _ | _ | _ | i | i <;> simp [garc]

/-- Every arc of `G_{2k+6}` between two of its vertices is an arc of the completion. -/
theorem garc_tarc (k : ℕ) (x y : V) (hx : valid k x) (hy : valid k y) (h : garc k x y) :
    tarc k x y :=
  ⟨hx, hy, fun hxy => garc_irrefl k x (hxy ▸ h), Or.inl h⟩

theorem bob_any (k : ℕ) (hk : 1 ≤ k) : ∃ L : List (ℕ × (V → ℕ)),
    (∀ p ∈ L, ∀ x y, valid k x → valid k y → x ≠ y → p.2 x ≠ p.2 y) ∧
    (L.map Prod.fst).sum = 6 * k + 14 ∧ BobFwd L (tarc k) (vs k) (4 * k + 9) := by
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | h2
  · exact ⟨cert8, cert8_inj, cert8_total, bob8⟩
  · exact ⟨certList k, fun p hp x y hx hy hxy => certList_inj k h2 x y hx hy hxy p hp,
      certList_total k h2, bob k h2⟩

theorem oarcs_tarc (k : ℕ) (hk : 1 ≤ k) :
    ∀ q ∈ oarcs k, q.1.1 ∈ vs k ∧ q.1.2 ∈ vs k ∧ tarc k q.1.1 q.1.2 := by
  intro q hq
  obtain ⟨hx, hy, h⟩ := oarcs_arcs k hk q hq
  exact ⟨(mem_vs k _).2 hx, (mem_vs k _).2 hy, garc_tarc k _ _ hx hy h⟩

/-- **Theorem `thm:family-value`, even `n = 2k + 6 ≥ 8`.**  Both players' strategies. -/
theorem value (k : ℕ) (hk : 1 ≤ k) :
    (∃ L : List (ℕ × (V → ℕ)),
      (∀ p ∈ L, ∀ x y, valid k x → valid k y → x ≠ y → p.2 x ≠ p.2 y) ∧
      (L.map Prod.fst).sum = 6 * k + 14 ∧ BobFwd L (tarc k) (vs k) (4 * k + 9) ∧
      BobFwd L (garc k) (vs k) (4 * k + 9)) ∧
    AliceFwd (oarcs k) (4 * k + 9) ∧ ((oarcs k).map Prod.snd).sum = 6 * k + 14 ∧
    (∀ q ∈ oarcs k, valid k q.1.1 ∧ valid k q.1.2 ∧ garc k q.1.1 q.1.2) := by
  obtain ⟨L, hinj, htot, hbob⟩ := bob_any k hk
  refine ⟨⟨L, hinj, htot, hbob, ?_⟩, alice k hk, oarcs_total k hk, oarcs_arcs k hk⟩
  intro x hx y hy h
  exact hbob x hx y hy (garc_tarc k x y ((mem_vs k x).1 hx) ((mem_vs k y).1 hy) h)

/-- **The value is exactly `(4k + 9) / (6k + 14)`**, for the completion (`E = tarc k`) and for
the obstacle (`E = garc k`): no weighted orders make every arc forward with a larger fraction of
their total weight, and no weighted arcs keep every ranking below a smaller fraction. -/
theorem value_exact (k : ℕ) (hk : 1 ≤ k) (E : V → V → Prop) (hE : E = tarc k ∨ E = garc k) :
    (∀ (L : List (ℕ × (V → ℕ))) (β : ℕ), BobFwd L E (vs k) β →
        β * (6 * k + 14) ≤ (4 * k + 9) * (L.map Prod.fst).sum) ∧
    (∀ (A : List ((V × V) × ℕ)) (γ : ℕ), AliceFwd A γ →
        (∀ q ∈ A, q.1.1 ∈ vs k ∧ q.1.2 ∈ vs k ∧ E q.1.1 q.1.2) →
        (4 * k + 9) * (A.map Prod.snd).sum ≤ γ * (6 * k + 14)) := by
  obtain ⟨⟨L0, _, htot, hbobT, hbobG⟩, hal, haltot, harcs⟩ := value k hk
  constructor
  · intro L β hL
    have := weak_duality L (oarcs k) E (vs k) β (4 * k + 9) hL hal (by
      intro q hq
      obtain ⟨hx, hy, h⟩ := harcs q hq
      refine ⟨(mem_vs k _).2 hx, (mem_vs k _).2 hy, ?_⟩
      rcases hE with rfl | rfl
      · exact garc_tarc k _ _ hx hy h
      · exact h)
    rwa [haltot] at this
  · intro A γ hA hAE
    have hb : BobFwd L0 E (vs k) (4 * k + 9) := by rcases hE with rfl | rfl <;> assumption
    have := weak_duality L0 A E (vs k) (4 * k + 9) γ hb hA hAE
    rwa [htot] at this

end Even

namespace Odd

theorem garc_irrefl (k : ℕ) (x : V) : ¬ garc k x x := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | i | i <;> simp [garc]

theorem garc_tarc (k : ℕ) (x y : V) (hx : valid k x) (hy : valid k y) (h : garc k x y) :
    tarc k x y :=
  ⟨hx, hy, fun hxy => garc_irrefl k x (hxy ▸ h), Or.inl h⟩

/-- Alice's weighted arcs: all arcs of `H_{2k+9}`, with weight 1. -/
def alist (k : ℕ) : List ((V × V) × ℕ) := if k = 0 then oarcs0 else oarcs k

theorem alist_props (k : ℕ) :
    AliceFwd (alist k) (4 * k + 15) ∧ ((alist k).map Prod.snd).sum = 6 * k + 23 ∧
    (∀ q ∈ alist k, valid k q.1.1 ∧ valid k q.1.2 ∧ garc k q.1.1 q.1.2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [alist, if_pos rfl]
    exact ⟨alice0, oarcs0_total, oarcs0_arcs⟩
  · simp only [alist, if_neg (Nat.pos_iff_ne_zero.1 hk)]
    exact ⟨alice k hk, oarcs_total k hk, oarcs_arcs k hk⟩

theorem bob_any (k : ℕ) : ∃ L : List (ℕ × (V → ℕ)),
    (∀ p ∈ L, ∀ x y, valid k x → valid k y → x ≠ y → p.2 x ≠ p.2 y) ∧
    (L.map Prod.fst).sum = 6 * k + 23 ∧ BobFwd L (tarc k) (vs k) (4 * k + 15) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨cert9, cert9_inj, cert9_total, bob9⟩
  · exact ⟨certList k, fun p hp x y hx hy hxy => certList_inj k hk x y hx hy hxy p hp,
      certList_total k hk, bob k hk⟩

/-- **Theorem `thm:family-value`, odd `n = 2k + 9 ≥ 9`.**  Both players' strategies. -/
theorem value (k : ℕ) :
    (∃ L : List (ℕ × (V → ℕ)),
      (∀ p ∈ L, ∀ x y, valid k x → valid k y → x ≠ y → p.2 x ≠ p.2 y) ∧
      (L.map Prod.fst).sum = 6 * k + 23 ∧ BobFwd L (tarc k) (vs k) (4 * k + 15) ∧
      BobFwd L (garc k) (vs k) (4 * k + 15)) ∧
    AliceFwd (alist k) (4 * k + 15) ∧ ((alist k).map Prod.snd).sum = 6 * k + 23 ∧
    (∀ q ∈ alist k, valid k q.1.1 ∧ valid k q.1.2 ∧ garc k q.1.1 q.1.2) := by
  obtain ⟨L, hinj, htot, hbob⟩ := bob_any k
  obtain ⟨hal, haltot, harcs⟩ := alist_props k
  refine ⟨⟨L, hinj, htot, hbob, ?_⟩, hal, haltot, harcs⟩
  intro x hx y hy h
  exact hbob x hx y hy (garc_tarc k x y ((mem_vs k x).1 hx) ((mem_vs k y).1 hy) h)

/-- **The value is exactly `(4k + 15) / (6k + 23)`**, for the completion and for the obstacle. -/
theorem value_exact (k : ℕ) (E : V → V → Prop) (hE : E = tarc k ∨ E = garc k) :
    (∀ (L : List (ℕ × (V → ℕ))) (β : ℕ), BobFwd L E (vs k) β →
        β * (6 * k + 23) ≤ (4 * k + 15) * (L.map Prod.fst).sum) ∧
    (∀ (A : List ((V × V) × ℕ)) (γ : ℕ), AliceFwd A γ →
        (∀ q ∈ A, q.1.1 ∈ vs k ∧ q.1.2 ∈ vs k ∧ E q.1.1 q.1.2) →
        (4 * k + 15) * (A.map Prod.snd).sum ≤ γ * (6 * k + 23)) := by
  obtain ⟨⟨L0, _, htot, hbobT, hbobG⟩, hal, haltot, harcs⟩ := value k
  constructor
  · intro L β hL
    have := weak_duality L (alist k) E (vs k) β (4 * k + 15) hL hal (by
      intro q hq
      obtain ⟨hx, hy, h⟩ := harcs q hq
      refine ⟨(mem_vs k _).2 hx, (mem_vs k _).2 hy, ?_⟩
      rcases hE with rfl | rfl
      · exact garc_tarc k _ _ hx hy h
      · exact h)
    rwa [haltot] at this
  · intro A γ hA hAE
    have hb : BobFwd L0 E (vs k) (4 * k + 15) := by rcases hE with rfl | rfl <;> assumption
    have := weak_duality L0 A E (vs k) (4 * k + 15) γ hb hA hAE
    rwa [htot] at this

end Odd

end Tsigma
