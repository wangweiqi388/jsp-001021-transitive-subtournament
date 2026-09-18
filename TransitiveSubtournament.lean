import Init

/-!
# JSP-001021: Every tournament contains a transitive subtournament of size ≥ ⌈log₂(n+1)⌉

Erdős–Moser (1964). We formalize the constructive pigeonhole induction:
pick a vertex `v`, split the remaining vertices into out-neighbours `O` and
in-neighbours `I`, recurse on the larger side, then prepend (resp. append) `v`.

Only the standard library `Init` is required (no mathlib).
-/

namespace JustinSunPrize

/-- Lower bound function: `bound 0 = 0`, `bound (n+1) = 1 + bound ((n+1)/2)`.
    This equals `⌈log₂(n+1)⌉`. -/
def bound : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + bound ((n + 1) / 2)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

theorem bound_succ_eq (n : Nat) (h : n > 0) : bound n = bound (n / 2) + 1 := by
  cases n with
  | zero => cases h
  | succ n' => rw [bound.eq_2, Nat.add_comm]

theorem two_mul_add_one_div_two (M : Nat) : (2 * M + 1) / 2 = M := by
  apply Nat.div_eq_of_lt_le <;> omega

theorem pigeon_div (n M : Nat) (h : n ≤ 2 * M + 1) : n / 2 ≤ M := by
  have h' : n / 2 ≤ (2 * M + 1) / 2 := Nat.div_le_div_right h
  rwa [two_mul_add_one_div_two M] at h'

theorem bound_mono_aux (n : Nat) : ∀ m, m ≤ n → bound m ≤ bound n :=
  Nat.strongRecOn (motive := fun n => ∀ m, m ≤ n → bound m ≤ bound n) n (by
    intro n ih m hm
    cases m with
    | zero => simp [bound]
    | succ m' =>
      cases n with
      | zero => exact (Nat.not_succ_le_zero m' hm).elim
      | succ n' =>
        rw [bound_succ_eq (m' + 1) (Nat.succ_pos m'), bound_succ_eq (n' + 1) (Nat.succ_pos n')]
        apply Nat.add_le_add_right
        exact ih ((n' + 1) / 2) (Nat.div_lt_self (Nat.succ_pos n') (by decide)) ((m' + 1) / 2) (Nat.div_le_div_right hm))

theorem bound_mono {m n : Nat} (h : m ≤ n) : bound m ≤ bound n := bound_mono_aux n m h

/-!
## Link lemma: `bound n = ⌈log₂(n+1)⌉`

`bound n` is exactly the ceiling of `log₂(n+1)`: it is the least `k` such that
`n + 1 ≤ 2 ^ k`. The next lemmas establish this machine-checked, so the
formalized theorem `transitiveSubtournament` reads "every n-tournament contains a
transitive subtournament of size at least `⌈log₂(n+1)⌉`".
-/

theorem le_two_mul_div_add_one (m : Nat) : m ≤ 2 * (m / 2) + 1 := by
  have h := Nat.div_add_mod m 2
  have hm : m % 2 < 2 := Nat.mod_lt m (by decide)
  omega

theorem two_pow_bound_ge : ∀ n : Nat, n + 1 ≤ 2 ^ bound n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [bound.eq_1]
    | succ m =>
      rw [bound_succ_eq (m + 1) (Nat.succ_pos m), Nat.pow_succ]
      have hm : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      have hih := ih ((m + 1) / 2) hm
      have h3 := le_two_mul_div_add_one (m + 1)
      omega

theorem bound_le_of_two_pow : ∀ (n k : Nat), n + 1 ≤ 2 ^ k → bound n ≤ k := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k hk
    cases n with
    | zero => simp [bound.eq_1]
    | succ m =>
      cases k with
      | zero =>
        have h1 : (2 : Nat) ^ 0 = 1 := rfl
        rw [h1] at hk
        omega
      | succ k' =>
        rw [bound_succ_eq (m + 1) (Nat.succ_pos m)]
        apply Nat.add_le_add_right
        apply ih ((m + 1) / 2) (Nat.div_lt_self (Nat.succ_pos m) (by decide))
        have hps : (2 : Nat) ^ (k' + 1) = 2 ^ k' * 2 := Nat.pow_succ _ _
        rw [hps] at hk
        omega

/-- `bound n` is the least `k` with `n + 1 ≤ 2 ^ k`, i.e. `bound n = ⌈log₂(n+1)⌉`. -/
theorem bound_spec (n : Nat) :
    n + 1 ≤ 2 ^ bound n ∧ ∀ k, n + 1 ≤ 2 ^ k → bound n ≤ k :=
  ⟨two_pow_bound_ge n, bound_le_of_two_pow n⟩

/-- A tournament: for any two distinct vertices exactly one edge direction holds. -/
structure Tournament (α : Type u) where
  toEdge : α → α → Bool
  irrefl : ∀ (a : α), toEdge a a = false
  total : ∀ (a b : α), a ≠ b → toEdge a b = true ∨ toEdge b a = true
  asym : ∀ (a b : α), a ≠ b → toEdge a b = true → toEdge b a = false

/-- `l` is a transitive subtournament of `T`: its vertices are distinct and ordered
    so that every earlier vertex has a forward edge to every later vertex (equivalently
    the induced subgraph is a transitive tournament / acyclic).

    We define it inductively, mirroring the Erdős–Moser construction: a transitive
    subtournament is either empty, or obtained by prepending a vertex `v` that beats
    every vertex to its right (`O`), or by appending a vertex `v` beaten by every vertex
    to its left (`I`). This is exactly the class of linearly ordered, all-forward
    subtournaments — equivalently `l.Nodup ∧ l.Pairwise (fun a b => T.toEdge a b = true)`
    (note Lean's `List.Pairwise` is the all-pairs predicate, not adjacent-only). -/
inductive isTopo {α : Type u} (T : Tournament α) : List α → Prop
  | nil : isTopo T []
  | cons (v : α) (l : List α) (h : ∀ a, a ∈ l → T.toEdge v a = true) (hl : isTopo T l) (hv : v ∉ l) :
      isTopo T (v :: l)
  | snk (v : α) (l : List α) (h : ∀ a, a ∈ l → T.toEdge a v = true) (hl : isTopo T l) (hv : v ∉ l) :
      isTopo T (l ++ [v])

/-- Correctness of `isTopo`: any `isTopo` list is a genuine total order with
    **all** forward edges — i.e. a real transitive subtournament (acyclic; a
    3-cycle `a→b→c→a` ordered `[a,b,c]` cannot satisfy this, since it would
    require `T.toEdge a c = true` while `c→a`). Hence, with `l.Nodup`, `isTopo T l`
    yields `l.Pairwise (fun a b => T.toEdge a b = true)` (the all-pairs formulation). -/
theorem isTopo_pairwise {α : Type u} {T : Tournament α} {l : List α} (h : isTopo T l) :
    l.Pairwise (fun a b => T.toEdge a b = true) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons v l hv hl hvnot ih =>
      rw [List.pairwise_cons]
      exact ⟨hv, ih⟩
  | snk v l hv hl hvnot ih =>
      rw [List.pairwise_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      have hbv : b = v := by simpa using hb
      subst hbv
      exact hv a ha

/-- Nodup is preserved by filtering. -/
theorem nodup_filter {α : Type u} (p : α → Bool) {l : List α} (h : l.Nodup) : (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    cases hpa : p a
    · rw [List.filter, hpa]
      exact ih (List.nodup_cons.mp h).right
    · rw [List.filter, hpa]
      rw [List.nodup_cons]
      constructor
      · intro ha
        exact (List.nodup_cons.mp h).left ((List.mem_filter.mp ha).left)
      · exact ih (List.nodup_cons.mp h).right

/-- Lengths of a filter and its complement sum to the whole list length. -/
theorem filter_partition {α : Type u} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter fun x => ! p x).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter, List.length_cons]
    cases h : p a <;> simp <;> omega

theorem not_mem_filter_of_not_mem {α : Type u} (p : α → Bool) {a : α} {l : List α} (h : a ∉ l) :
    a ∉ l.filter p := by
  intro ha
  exact h (List.mem_filter.mp ha).left

theorem not_mem_of_subset_of_not_mem {α : Type u} {a : α} {l₁ l₂ : List α}
    (h₁ : a ∉ l₂) (subset : ∀ x, x ∈ l₁ → x ∈ l₂) : a ∉ l₁ := by
  intro ha
  exact h₁ (subset a ha)

/-- A solution: a transitive subtournament `l` inside `s` of size at least `bound s.length`. -/
structure Sol (α : Type u) (T : Tournament α) (s : List α) (hs : s.Nodup) where
  l : List α
  nodup : l.Nodup
  topo : isTopo T l
  len : l.length ≥ bound s.length
  subset : ∀ x, x ∈ l → x ∈ s

def solve {α : Type u} (T : Tournament α) (s : List α) (hs : s.Nodup) : Sol α T s hs := match h : s with
| [] =>
    { l := [], nodup := by simp, topo := isTopo.nil, len := by simp [bound], subset := by intro x hx; cases hx }
| v :: rest =>
  by
      have hs' : (v :: rest).Nodup := h ▸ hs
      have vnin : v ∉ rest := (List.nodup_cons.mp hs').left
      have restNd : rest.Nodup := (List.nodup_cons.mp hs').right
      let p : α → Bool := fun x => T.toEdge v x
      let O := rest.filter p
      let I := rest.filter fun x => ! p x
      have ONd : O.Nodup := nodup_filter p restNd
      have INd : I.Nodup := nodup_filter (fun x => ! p x) restNd
      have part : O.length + I.length = rest.length := filter_partition p rest
      have twoMax : O.length + I.length ≤ 2 * max O.length I.length := by
        calc
          O.length + I.length ≤ max O.length I.length + max O.length I.length :=
            Nat.add_le_add (Nat.le_max_left O.length I.length) (Nat.le_max_right O.length I.length)
          _ = 2 * max O.length I.length := by rw [Nat.two_mul]
      have leRest : rest.length ≤ 2 * max O.length I.length := by
        rw [← part]; exact twoMax
      have sLen : s.length = rest.length + 1 := by rw [h]; exact List.length_cons
      have leS : s.length ≤ 2 * max O.length I.length + 1 := by
        rw [sLen]; exact Nat.add_le_add_right leRest 1
      have big : s.length / 2 ≤ max O.length I.length := pigeon_div s.length (max O.length I.length) leS
      have sPos : s.length > 0 := by rw [sLen]; exact Nat.succ_pos rest.length
      if hO : O.length ≥ I.length then
        -- I ≤ O : the larger side is O; prepend v at the front.
        have maxEqO : max O.length I.length = O.length := Nat.max_eq_left hO
        have halfO : s.length / 2 ≤ O.length := by rw [maxEqO] at big; exact big
        let solO := solve T O ONd
        have edge_v : ∀ a ∈ solO.l, T.toEdge v a = true := by
          intro a ha
          have haO : a ∈ O := solO.subset a ha
          exact (List.mem_filter.mp haO).right
        have vninO : v ∉ O := not_mem_filter_of_not_mem p vnin
        have vninSolO : v ∉ solO.l := not_mem_of_subset_of_not_mem vninO solO.subset
        have nodL : (v :: solO.l).Nodup := by
          rw [List.nodup_cons]
          constructor
          · exact not_mem_of_subset_of_not_mem vninO solO.subset
          · exact solO.nodup
        have topoL : isTopo T (v :: solO.l) := isTopo.cons v solO.l edge_v solO.topo vninSolO
        have hlenO : bound O.length ≤ solO.l.length := solO.len
        have hbO : bound (s.length / 2) ≤ bound O.length := bound_mono halfO
        have hlen : bound (s.length / 2) ≤ solO.l.length := Nat.le_trans hbO hlenO
        have hbnd : bound s.length = bound (s.length / 2) + 1 := bound_succ_eq s.length sPos
        have hlen_final : bound s.length ≤ (v :: solO.l).length := by
          rw [hbnd, List.length_cons]
          exact Nat.add_le_add_right hlen 1
        have subset : ∀ x, x ∈ v :: solO.l → x ∈ s := by
          intro x hx
          rw [List.mem_cons] at hx
          rcases hx with hx | hx
          · simpa [h] using (List.mem_cons.mpr (Or.inl hx))
          · simpa [h] using (List.mem_cons_of_mem v ((List.mem_filter.mp (solO.subset x hx)).left))
        exact { l := v :: solO.l, nodup := nodL, topo := topoL, len := h ▸ hlen_final, subset := h ▸ subset }
      else
        -- O < I : the larger side is I; append v at the end.
        have hOI : O.length ≤ I.length := Nat.le_of_lt (Nat.lt_of_not_ge hO)
        have maxEqI : max O.length I.length = I.length := Nat.max_eq_right hOI
        have halfI : s.length / 2 ≤ I.length := by rw [maxEqI] at big; exact big
        let solI := solve T I INd
        have edge_to_v : ∀ a ∈ solI.l, T.toEdge a v = true := by
          intro a ha
          have haI : a ∈ I := solI.subset a ha
          have hnot : ! (T.toEdge v a) = true := by
            simpa [p] using (List.mem_filter.mp haI).right
          have har : a ∈ rest := (List.mem_filter.mp haI).left
          have hne : v ≠ a := by
            intro hva
            rw [← hva] at har
            exact vnin har
          have hv_a_false : T.toEdge v a = false := by
            cases hv : T.toEdge v a with
            | false => rfl
            | true => simp [hv] at hnot
          have htot := T.total v a hne
          simpa [hv_a_false] using htot
        have vninI : v ∉ I := not_mem_filter_of_not_mem (fun x => ! p x) vnin
        have vninSolI : v ∉ solI.l := not_mem_of_subset_of_not_mem vninI solI.subset
        have nodL : (solI.l ++ [v]).Nodup := by
          rw [List.nodup_append]
          constructor
          · exact solI.nodup
          constructor
          · simp
          · intro a ha b hb
            have bv : b = v := by simpa using hb
            subst b
            intro hav
            have hv_l : v ∈ solI.l := hav ▸ ha
            exact not_mem_of_subset_of_not_mem vninI solI.subset hv_l
        have topoL : isTopo T (solI.l ++ [v]) := isTopo.snk v solI.l edge_to_v solI.topo vninSolI
        have hlenI : bound I.length ≤ solI.l.length := solI.len
        have hbI : bound (s.length / 2) ≤ bound I.length := bound_mono halfI
        have hlen : bound (s.length / 2) ≤ solI.l.length := Nat.le_trans hbI hlenI
        have hbnd : bound s.length = bound (s.length / 2) + 1 := bound_succ_eq s.length sPos
        have hlen_final : bound s.length ≤ (solI.l ++ [v]).length := by
          rw [hbnd, List.length_append]
          have hvlen : [v].length = 1 := by simp
          rw [hvlen]
          exact Nat.add_le_add_right hlen 1
        have subset : ∀ x, x ∈ solI.l ++ [v] → x ∈ s := by
          intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · simpa [h] using (List.mem_cons_of_mem v ((List.mem_filter.mp (solI.subset x hx)).left))
          · have xv : x = v := by simpa using hx
            simpa [h] using (List.mem_cons.mpr (Or.inl xv))
        exact { l := solI.l ++ [v], nodup := nodL, topo := topoL, len := h ▸ hlen_final, subset := h ▸ subset }
termination_by s.length
decreasing_by
  all_goals
    apply Nat.lt_of_le_of_lt
    · apply List.length_filter_le
    · rw [List.length_cons]
      exact Nat.lt_succ_self _

theorem transitiveSubtournament (n : Nat) (T : Tournament (Fin n)) :
    ∃ (l : List (Fin n)), l.Nodup ∧ isTopo T l ∧ l.length ≥ bound n := by
  have nd : (List.finRange n).Nodup := List.nodup_finRange n
  let r := solve T (List.finRange n) nd
  refine ⟨r.l, r.nodup, r.topo, ?_⟩
  simpa [List.length_finRange] using r.len

end JustinSunPrize
