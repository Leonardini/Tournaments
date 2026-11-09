import TsigmaProof.Support

/-!
# Sums over the arcs of the obstacle, and the uniform distribution

For a function on pairs of vertices that vanishes off the arcs of `G_n` (`H_n`), its sum over the
ordered pairs of vertices is its sum over the list `oarcs k` of Alice's side, which lists every arc
once (`psum_garc`).  With it, the uniform distribution `unif k` on the arcs is an optimal Alice
strategy (Proposition `prop:family-bound`), and every order `π` of positive weight in an optimal Bob
strategy makes exactly `2n - 3` arcs of the obstacle forward (`aliceWeight_tight`).
-/

namespace Tsigma

theorem list_sum_div {α : Type} (l : List α) (f : α → ℚ) (c : ℚ) :
    (l.map (fun a => f a / c)).sum = (l.map f).sum / c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, add_div]

/-- Forward weight of a list of arcs of weight 1, all of whose forward arcs weigh `c`. -/
theorem list_fwd_const {V : Type} (l : List ((V × V) × ℕ)) (r : V → ℕ) (y : V → V → ℚ) (c : ℚ)
    (hs : ∀ q ∈ l, q.2 = 1) (h : ∀ q ∈ l, r q.1.1 < r q.1.2 → y q.1.1 q.1.2 = c) :
    (l.map (fun q => if r q.1.1 < r q.1.2 then y q.1.1 q.1.2 else 0)).sum =
      c * (((l.map (fun q => if r q.1.1 < r q.1.2 then q.2 else 0)).sum : ℕ) : ℚ) := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [ih (fun p hp => hs p (List.mem_cons_of_mem _ hp)) (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    by_cases hr : r q.1.1 < r q.1.2
    · rw [if_pos hr, if_pos hr, h q List.mem_cons_self hr, hs q List.mem_cons_self]
      push_cast
      ring
    · rw [if_neg hr, if_neg hr]
      push_cast
      ring

/-- Total of a list of arcs of weight 1, all but `e` of weight `c`. -/
theorem list_sum_split {V : Type} [DecidableEq V] (l : List ((V × V) × ℕ)) (y : V → V → ℚ) (c : ℚ)
    (e : V × V) (hs : ∀ q ∈ l, q.2 = 1) (h : ∀ q ∈ l, q.1 ≠ e → y q.1.1 q.1.2 = c) :
    (l.map (fun q => y q.1.1 q.1.2)).sum = c * (((l.map Prod.snd).sum : ℕ) : ℚ) +
      (y e.1 e.2 - c) * (((l.map (fun q => if q.1 = e then 1 else 0)).sum : ℕ) : ℚ) := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [ih (fun p hp => hs p (List.mem_cons_of_mem _ hp)) (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    rw [hs q List.mem_cons_self]
    by_cases he : q.1 = e
    · rw [if_pos he, ← he]
      push_cast
      ring
    · rw [if_neg he, h q List.mem_cons_self he]
      push_cast
      ring

namespace Even

theorem oarcs_snd (k : ℕ) : ∀ q ∈ oarcs k, q.2 = 1 := by
  intro q hq
  simp only [oarcs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hq
  rcases hq with ((((((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | ⟨t, ht, h⟩) |
    ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩ <;> subst h <;> rfl

theorem oarcs_nodup (k : ℕ) : ((oarcs k).map Prod.fst).Nodup := by
  simp [oarcs, List.nodup_append, List.nodup_cons, List.map_map, Function.comp_def]
  and_intros
  all_goals first
    | exact List.Nodup.map (fun a b h => by simp at h; omega) List.nodup_range
    | (intro a ha a2 hb h1; omega)
    | (intro a ha a2 b hex h1 h2; subst h1; subst h2; simp at hex; (try omega))

theorem garc_mem (k : ℕ) (x z : V) (hx : valid k x) (hz : valid k z) (h : garc k x z) :
    (x, z) ∈ (oarcs k).map Prod.fst := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases z with _ | _ | _ | _ | _ | _ | b | b <;>
    simp [garc, valid, oarcs] at h hx hz ⊢
  all_goals first
    | omega
    | exact ⟨b - 1, by omega, by omega⟩
    | exact ⟨a - 1, by omega, by omega⟩
    | (rcases h with ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
       · exact Or.inl ⟨b - 1, by omega, by omega, by omega⟩
       · exact Or.inr ⟨b - 1, by omega, by omega, by omega⟩)

theorem garc_valid (k : ℕ) (hk : 1 ≤ k) (x z : V) (h : garc k x z) : valid k x ∧ valid k z := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases z with _ | _ | _ | _ | _ | _ | b | b <;>
    simp [garc, valid] at h ⊢ <;> omega

theorem oarcs_vs (k : ℕ) (hk : 1 ≤ k) : ∀ q ∈ (oarcs k).map Prod.fst, q.1 ∈ vs k ∧ q.2 ∈ vs k := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  obtain ⟨h1, h2, _⟩ := oarcs_arcs k hk p hp
  exact ⟨(mem_vs k _).2 h1, (mem_vs k _).2 h2⟩

/-- A sum over the pairs of vertices of a function supported on the arcs of `G_n` is a sum over
`oarcs k`. -/
theorem psum_garc (k : ℕ) (hk : 1 ≤ k) (f : V → V → ℚ) (hf : ∀ x z, f x z ≠ 0 → garc k x z) :
    psum (vs k) f = ((oarcs k).map (fun q => f q.1.1 q.1.2)).sum := by
  rw [psum_eq_list (vs k) ((oarcs k).map Prod.fst) (oarcs_nodup k) (oarcs_vs k hk) f
    (fun x hx z hz h => garc_mem k x z ((mem_vs k x).1 hx) ((mem_vs k z).1 hz) (hf x z h)),
    List.map_map]
  rfl

/-- The uniform distribution on the arcs of `G_n`. -/
def unif (k : ℕ) (x z : V) : ℚ := if garc k x z then 1 / ((6 * k + 14 : ℕ) : ℚ) else 0

theorem fwdQ_garc (k : ℕ) (hk : 1 ≤ k) (r : V → ℕ) (y : V → V → ℚ)
    (hy : ∀ x z, y x z ≠ 0 → garc k x z) :
    fwdQ (vs k) r y = ((oarcs k).map (fun q => if r q.1.1 < r q.1.2 then y q.1.1 q.1.2 else 0)).sum :=
  psum_garc k hk _ (fun x z h => by
    by_cases hr : r x < r z
    · rw [if_pos hr] at h; exact hy x z h
    · rw [if_neg hr] at h; exact absurd rfl h)

theorem unif_supp (k : ℕ) (x z : V) (h : unif k x z ≠ 0) : garc k x z := by
  unfold unif at h
  by_contra hg
  rw [if_neg hg] at h
  exact h rfl

theorem unif_fwd (k : ℕ) (hk : 1 ≤ k) (r : V → ℕ) :
    fwdQ (vs k) r (unif k) = (aliceWeight (oarcs k) r : ℚ) / ((6 * k + 14 : ℕ) : ℚ) := by
  rw [fwdQ_garc k hk r (unif k) (unif_supp k), aliceWeight, Nat.cast_list_sum, List.map_map,
    ← list_sum_div]
  apply congrArg
  apply List.map_congr_left
  intro q hq
  have hg := (oarcs_arcs k hk q hq).2.2
  have h1 := oarcs_snd k q hq
  simp only [Function.comp_apply, unif, if_pos hg, h1]
  split_ifs <;> simp

theorem unif_opt (k : ℕ) (hk : 1 ≤ k) : AliceOpt (vs k) (garc k) (rho k) (unif k) := by
  have hN : (0 : ℚ) < ((6 * k + 14 : ℕ) : ℚ) := by positivity
  refine ⟨fun x z => by unfold unif; split_ifs <;> positivity, unif_supp k, ?_, ?_⟩
  · rw [psum_garc k hk (unif k) (unif_supp k)]
    have : ((oarcs k).map (fun q => unif k q.1.1 q.1.2)) =
        ((oarcs k).map (fun q => ((q.2 : ℕ) : ℚ) / ((6 * k + 14 : ℕ) : ℚ))) := by
      apply List.map_congr_left
      intro q hq
      simp [unif, (oarcs_arcs k hk q hq).2.2, oarcs_snd k q hq]
    have h2 : ((oarcs k).map (fun q => ((q.2 : ℕ) : ℚ))).sum = (((oarcs k).map Prod.snd).sum : ℕ) := by
      rw [Nat.cast_list_sum, List.map_map]
      rfl
    rw [this, list_sum_div, h2, oarcs_total k hk]
    field_simp
  · intro r _
    rw [unif_fwd k hk r, rho]
    apply div_le_div_of_nonneg_right _ hN.le
    exact_mod_cast alice k hk r

/-- Every order of positive weight in an optimal Bob strategy for `G_n` makes exactly `2n - 3` arcs of
`G_n` forward. -/
theorem aliceWeight_tight (k : ℕ) (hk : 1 ≤ k) (r : V → ℕ)
    (ht : fwdQ (vs k) r (unif k) = rho k) : aliceWeight (oarcs k) r = 4 * k + 9 := by
  rw [unif_fwd k hk r, rho] at ht
  have hN : ((6 * k + 14 : ℕ) : ℚ) ≠ 0 := by positivity
  have : (aliceWeight (oarcs k) r : ℚ) = ((4 * k + 9 : ℕ) : ℚ) := by
    field_simp at ht
    exact ht
  exact_mod_cast this

end Even

/-- A list of arcs of weight 1, each of weight at least `c`, totalling `c` times their number: all
weigh `c`. -/
theorem list_eq_of_ge {V : Type} (l : List ((V × V) × ℕ)) (y : V → V → ℚ) (c : ℚ)
    (hs : ∀ q ∈ l, q.2 = 1) (hge : ∀ q ∈ l, c ≤ y q.1.1 q.1.2)
    (hsum : (l.map (fun q => y q.1.1 q.1.2)).sum = c * (((l.map Prod.snd).sum : ℕ) : ℚ)) :
    ∀ q ∈ l, y q.1.1 q.1.2 = c := by
  have hd : (l.map (fun q => y q.1.1 q.1.2 - c)).sum =
      (l.map (fun q => y q.1.1 q.1.2)).sum - c * (((l.map Prod.snd).sum : ℕ) : ℚ) := by
    clear hge hsum
    induction l with
    | nil => simp
    | cons q l ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      rw [ih (fun p hp => hs p (List.mem_cons_of_mem _ hp)), hs q List.mem_cons_self]
      push_cast
      ring
  rw [hsum, sub_self] at hd
  have hnn : ∀ a ∈ l.map (fun q => y q.1.1 q.1.2 - c), 0 ≤ a := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
    linarith [hge q hq]
  intro q hq
  have := List.single_le_sum hnn _ (List.mem_map.2 ⟨q, hq, rfl⟩)
  rw [hd] at this
  linarith [hge q hq]

namespace Odd

theorem oarcs_snd (k : ℕ) : ∀ q ∈ oarcs k, q.2 = 1 := by
  intro q hq
  simp only [oarcs, fixedArcs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hq
  rcases hq with ((((((((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h) | (h | h)) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) |
    ⟨t, ht, h⟩) <;> subst h <;> rfl

theorem oarcs_nodup (k : ℕ) (hk : 1 ≤ k) : ((oarcs k).map Prod.fst).Nodup := by
  simp [oarcs, fixedArcs, List.nodup_append, List.nodup_cons, List.map_map, Function.comp_def]
  and_intros
  all_goals first
    | omega
    | exact List.Nodup.map (fun a b h => by simp at h; omega) List.nodup_range
    | (intro a ha a2 hb h1; omega)
    | (intro a ha a2 b hex h1 h2; subst h1; subst h2; simp at hex; (try omega))
    | (intro a ha h; omega)
    | (intro h; omega)

theorem garc_mem (k : ℕ) (hk : 1 ≤ k) (x z : V) (hx : valid k x) (hz : valid k z) (h : garc k x z) :
    (x, z) ∈ (oarcs k).map Prod.fst := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;>
    rcases z with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp [garc, valid, oarcs, fixedArcs] at h hx hz ⊢
  all_goals first
    | omega
    | exact ⟨b - 1, by omega, by omega⟩
    | exact ⟨a - 1, by omega, by omega⟩
    | (rcases h with ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
       · exact Or.inl ⟨a - 1, by omega, by omega, by omega⟩
       · exact Or.inr ⟨a - 1, by omega, by omega, by omega⟩)

theorem oarcs_vs (k : ℕ) (hk : 1 ≤ k) : ∀ q ∈ (oarcs k).map Prod.fst, q.1 ∈ vs k ∧ q.2 ∈ vs k := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  obtain ⟨h1, h2, _⟩ := oarcs_arcs k hk p hp
  exact ⟨(mem_vs k _).2 h1, (mem_vs k _).2 h2⟩

theorem garc_valid (k : ℕ) (hk : 1 ≤ k) (x z : V) (h : garc k x z) : valid k x ∧ valid k z := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;>
    rcases z with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp [garc, valid] at h ⊢ <;> omega

theorem psum_garc (k : ℕ) (hk : 1 ≤ k) (f : V → V → ℚ) (hf : ∀ x z, f x z ≠ 0 → garc k x z) :
    psum (vs k) f = ((oarcs k).map (fun q => f q.1.1 q.1.2)).sum := by
  rw [psum_eq_list (vs k) ((oarcs k).map Prod.fst) (oarcs_nodup k hk) (oarcs_vs k hk) f
    (fun x hx z hz h => garc_mem k hk x z ((mem_vs k x).1 hx) ((mem_vs k z).1 hz) (hf x z h)),
    List.map_map]
  rfl

/-- The uniform distribution on the arcs of `H_n`. -/
def unif (k : ℕ) (x z : V) : ℚ := if garc k x z then 1 / ((6 * k + 23 : ℕ) : ℚ) else 0

theorem fwdQ_garc (k : ℕ) (hk : 1 ≤ k) (r : V → ℕ) (y : V → V → ℚ)
    (hy : ∀ x z, y x z ≠ 0 → garc k x z) :
    fwdQ (vs k) r y = ((oarcs k).map (fun q => if r q.1.1 < r q.1.2 then y q.1.1 q.1.2 else 0)).sum :=
  psum_garc k hk _ (fun x z h => by
    by_cases hr : r x < r z
    · rw [if_pos hr] at h; exact hy x z h
    · rw [if_neg hr] at h; exact absurd rfl h)

theorem unif_supp (k : ℕ) (x z : V) (h : unif k x z ≠ 0) : garc k x z := by
  unfold unif at h
  by_contra hg
  rw [if_neg hg] at h
  exact h rfl

theorem unif_fwd (k : ℕ) (hk : 1 ≤ k) (r : V → ℕ) :
    fwdQ (vs k) r (unif k) = (aliceWeight (oarcs k) r : ℚ) / ((6 * k + 23 : ℕ) : ℚ) := by
  rw [fwdQ_garc k hk r (unif k) (unif_supp k), aliceWeight, Nat.cast_list_sum, List.map_map,
    ← list_sum_div]
  apply congrArg
  apply List.map_congr_left
  intro q hq
  have hg := (oarcs_arcs k hk q hq).2.2
  have h1 := oarcs_snd k q hq
  simp only [Function.comp_apply, unif, if_pos hg, h1]
  split_ifs <;> simp

theorem unif_opt (k : ℕ) (hk : 1 ≤ k) : AliceOpt (vs k) (garc k) (rho k) (unif k) := by
  have hN : (0 : ℚ) < ((6 * k + 23 : ℕ) : ℚ) := by positivity
  refine ⟨fun x z => by unfold unif; split_ifs <;> positivity, unif_supp k, ?_, ?_⟩
  · rw [psum_garc k hk (unif k) (unif_supp k)]
    have : ((oarcs k).map (fun q => unif k q.1.1 q.1.2)) =
        ((oarcs k).map (fun q => ((q.2 : ℕ) : ℚ) / ((6 * k + 23 : ℕ) : ℚ))) := by
      apply List.map_congr_left
      intro q hq
      simp [unif, (oarcs_arcs k hk q hq).2.2, oarcs_snd k q hq]
    have h2 : ((oarcs k).map (fun q => ((q.2 : ℕ) : ℚ))).sum = (((oarcs k).map Prod.snd).sum : ℕ) := by
      rw [Nat.cast_list_sum, List.map_map]
      rfl
    rw [this, list_sum_div, h2, oarcs_total k hk]
    field_simp
  · intro r _
    rw [unif_fwd k hk r, rho]
    apply div_le_div_of_nonneg_right _ hN.le
    exact_mod_cast alice k hk r

theorem aliceWeight_tight (k : ℕ) (hk : 1 ≤ k) (r : V → ℕ)
    (ht : fwdQ (vs k) r (unif k) = rho k) : aliceWeight (oarcs k) r = 4 * k + 15 := by
  rw [unif_fwd k hk r, rho] at ht
  have hN : ((6 * k + 23 : ℕ) : ℚ) ≠ 0 := by positivity
  have : (aliceWeight (oarcs k) r : ℚ) = ((4 * k + 15 : ℕ) : ℚ) := by
    field_simp at ht
    exact ht
  exact_mod_cast this

end Odd

end Tsigma
