import TsigmaProof.UpperEven
import TsigmaProof.UpperOdd
import TsigmaProof.Small

/-!
# Theorem `thm:family-value` of paper 1

For every `n ≥ 8`, the completion `Ĝ_n` (even `n`) or `Ĥ_n` (odd `n`), and the obstacle `G_n` or
`H_n` itself, have predictability exactly `(2n - 3) / (3n - 4)`.

The predictability is the value of the game in which Alice picks an arc and Bob a linear order,
Bob winning if the arc is forward.  With integer weights (`Common.lean`):

* Bob has linear orders (rankings injective on the vertices) with weights totalling `c(3n - 4)` under
  which every arc is forward with weight at least `c(2n - 3)`, and every arc outside the obstacle with
  weight at least `c(2n - 3) + 1` (the strict certificates of Appendix `app:family`; `c = 1` for
  `n = 8, 9`, `c = 2` for even `n ≥ 10`, `c = 6` for odd `n ≥ 11`);
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

/-- Bob's strict certificate, for every `k ≥ 1`. -/
theorem bob_any (k : ℕ) (hk : 1 ≤ k) : ∃ (c : ℕ) (L : List (ℕ × (V → ℕ))), 0 < c ∧
    (∀ p ∈ L, ∀ x y, valid k x → valid k y → x ≠ y → p.2 x ≠ p.2 y) ∧
    (L.map Prod.fst).sum = c * (6 * k + 14) ∧ BobFwd L (tarc k) (vs k) (c * (4 * k + 9)) ∧
    (∀ x ∈ vs k, ∀ y ∈ vs k, tarc k x y → ¬ garc k x y → c * (4 * k + 9) + 1 ≤ fwdWeight L x y) := by
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | h2
  · exact ⟨1, cert8, by omega, cert8_inj, cert8_total, bob8, bob8_strict⟩
  · refine ⟨2, certList k, by omega, fun p hp x y hx hy hxy => certList_inj k h2 x y hx hy hxy p hp,
      by rw [certList_total k h2]; ring, ?_, ?_⟩
    · have := bob k h2
      intro x hx y hy h
      have := this x hx y hy h
      omega
    · intro x _ y _ h hg
      have := bob_strict k h2 x y h hg
      omega

theorem oarcs_tarc (k : ℕ) (hk : 1 ≤ k) :
    ∀ q ∈ oarcs k, q.1.1 ∈ vs k ∧ q.1.2 ∈ vs k ∧ tarc k q.1.1 q.1.2 := by
  intro q hq
  obtain ⟨hx, hy, h⟩ := oarcs_arcs k hk q hq
  exact ⟨(mem_vs k _).2 hx, (mem_vs k _).2 hy, garc_tarc k _ _ hx hy h⟩

/-- **Theorem `thm:family-value`, even `n = 2k + 6 ≥ 8`.**  Both players' strategies. -/
theorem value (k : ℕ) (hk : 1 ≤ k) :
    (∃ (c : ℕ) (L : List (ℕ × (V → ℕ))), 0 < c ∧
      (∀ p ∈ L, ∀ x y, valid k x → valid k y → x ≠ y → p.2 x ≠ p.2 y) ∧
      (L.map Prod.fst).sum = c * (6 * k + 14) ∧ BobFwd L (tarc k) (vs k) (c * (4 * k + 9)) ∧
      BobFwd L (garc k) (vs k) (c * (4 * k + 9)) ∧
      (∀ x ∈ vs k, ∀ y ∈ vs k, tarc k x y → ¬ garc k x y → c * (4 * k + 9) + 1 ≤ fwdWeight L x y)) ∧
    AliceFwd (oarcs k) (4 * k + 9) ∧ ((oarcs k).map Prod.snd).sum = 6 * k + 14 ∧
    (∀ q ∈ oarcs k, valid k q.1.1 ∧ valid k q.1.2 ∧ garc k q.1.1 q.1.2) := by
  obtain ⟨c, L, hc, hinj, htot, hbob, hstr⟩ := bob_any k hk
  refine ⟨⟨c, L, hc, hinj, htot, hbob, ?_, hstr⟩, alice k hk, oarcs_total k hk, oarcs_arcs k hk⟩
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
  obtain ⟨⟨c, L0, hc, _, htot, hbobT, hbobG, _⟩, hal, haltot, harcs⟩ := value k hk
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
    have hb : BobFwd L0 E (vs k) (c * (4 * k + 9)) := by rcases hE with rfl | rfl <;> assumption
    have h := weak_duality L0 A E (vs k) (c * (4 * k + 9)) γ hb hA hAE
    rw [htot] at h
    have h' : c * ((4 * k + 9) * (A.map Prod.snd).sum) ≤ c * (γ * (6 * k + 14)) := by
      calc c * ((4 * k + 9) * (A.map Prod.snd).sum) = c * (4 * k + 9) * (A.map Prod.snd).sum := by ring
        _ ≤ γ * (c * (6 * k + 14)) := h
        _ = c * (γ * (6 * k + 14)) := by ring
    exact Nat.le_of_mul_le_mul_left h' hc

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

/-- Bob's strict certificate, for every `k ≥ 0`. -/
theorem bob_any (k : ℕ) : ∃ (c : ℕ) (L : List (ℕ × (V → ℕ))), 0 < c ∧
    (∀ p ∈ L, ∀ x y, valid k x → valid k y → x ≠ y → p.2 x ≠ p.2 y) ∧
    (L.map Prod.fst).sum = c * (6 * k + 23) ∧ BobFwd L (tarc k) (vs k) (c * (4 * k + 15)) ∧
    (∀ x ∈ vs k, ∀ y ∈ vs k, tarc k x y → ¬ garc k x y → c * (4 * k + 15) + 1 ≤ fwdWeight L x y) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, cert9, by omega, cert9_inj, cert9_total, bob9, bob9_strict⟩
  · refine ⟨6, certList k, by omega, fun p hp x y hx hy hxy => certList_inj k hk x y hx hy hxy p hp,
      by rw [certList_total k hk]; ring, ?_, ?_⟩
    · have := bob k hk
      intro x hx y hy h
      have := this x hx y hy h
      omega
    · intro x _ y _ h hg
      have := bob_strict k hk x y h hg
      omega

/-- **Theorem `thm:family-value`, odd `n = 2k + 9 ≥ 9`.**  Both players' strategies. -/
theorem value (k : ℕ) :
    (∃ (c : ℕ) (L : List (ℕ × (V → ℕ))), 0 < c ∧
      (∀ p ∈ L, ∀ x y, valid k x → valid k y → x ≠ y → p.2 x ≠ p.2 y) ∧
      (L.map Prod.fst).sum = c * (6 * k + 23) ∧ BobFwd L (tarc k) (vs k) (c * (4 * k + 15)) ∧
      BobFwd L (garc k) (vs k) (c * (4 * k + 15)) ∧
      (∀ x ∈ vs k, ∀ y ∈ vs k, tarc k x y → ¬ garc k x y → c * (4 * k + 15) + 1 ≤ fwdWeight L x y)) ∧
    AliceFwd (alist k) (4 * k + 15) ∧ ((alist k).map Prod.snd).sum = 6 * k + 23 ∧
    (∀ q ∈ alist k, valid k q.1.1 ∧ valid k q.1.2 ∧ garc k q.1.1 q.1.2) := by
  obtain ⟨c, L, hc, hinj, htot, hbob, hstr⟩ := bob_any k
  obtain ⟨hal, haltot, harcs⟩ := alist_props k
  refine ⟨⟨c, L, hc, hinj, htot, hbob, ?_, hstr⟩, hal, haltot, harcs⟩
  intro x hx y hy h
  exact hbob x hx y hy (garc_tarc k x y ((mem_vs k x).1 hx) ((mem_vs k y).1 hy) h)

/-- **The value is exactly `(4k + 15) / (6k + 23)`**, for the completion and for the obstacle. -/
theorem value_exact (k : ℕ) (E : V → V → Prop) (hE : E = tarc k ∨ E = garc k) :
    (∀ (L : List (ℕ × (V → ℕ))) (β : ℕ), BobFwd L E (vs k) β →
        β * (6 * k + 23) ≤ (4 * k + 15) * (L.map Prod.fst).sum) ∧
    (∀ (A : List ((V × V) × ℕ)) (γ : ℕ), AliceFwd A γ →
        (∀ q ∈ A, q.1.1 ∈ vs k ∧ q.1.2 ∈ vs k ∧ E q.1.1 q.1.2) →
        (4 * k + 15) * (A.map Prod.snd).sum ≤ γ * (6 * k + 23)) := by
  obtain ⟨⟨c, L0, hc, _, htot, hbobT, hbobG, _⟩, hal, haltot, harcs⟩ := value k
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
    have hb : BobFwd L0 E (vs k) (c * (4 * k + 15)) := by rcases hE with rfl | rfl <;> assumption
    have h := weak_duality L0 A E (vs k) (c * (4 * k + 15)) γ hb hA hAE
    rw [htot] at h
    have h' : c * ((4 * k + 15) * (A.map Prod.snd).sum) ≤ c * (γ * (6 * k + 23)) := by
      calc c * ((4 * k + 15) * (A.map Prod.snd).sum) = c * (4 * k + 15) * (A.map Prod.snd).sum := by
            ring
        _ ≤ γ * (c * (6 * k + 23)) := h
        _ = c * (γ * (6 * k + 23)) := by ring
    exact Nat.le_of_mul_le_mul_left h' hc

end Odd

end Tsigma
