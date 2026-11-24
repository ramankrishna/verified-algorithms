import Mathlib

namespace VerifiedAlgorithms

/-- Directed graph on `Fin n` with non-negative integer weights; `none` means no edge. -/
abbrev Weights (n : ℕ) := Fin n → Fin n → Option ℕ

/-- Minimum where `none` means infinity. -/
def omin : Option ℕ → Option ℕ → Option ℕ
  | none, b => b
  | some a, none => some a
  | some a, some b => some (min a b)

/-- Relax every edge leaving `u`, whose settled distance is `du`. -/
def relax {n : ℕ} (w : Weights n) (dist : Fin n → Option ℕ) (u : Fin n) (du : ℕ) :
    Fin n → Option ℕ :=
  fun v => match w u v with
    | none => dist v
    | some c => omin (dist v) (some (du + c))

/-- The unvisited vertex with the smallest finite tentative distance (linear scan). -/
def pickMin {n : ℕ} (dist : Fin n → Option ℕ) (visited : Finset (Fin n)) :
    Option (Fin n × ℕ) :=
  (List.finRange n).foldl (fun best v =>
    if v ∈ visited then best else
    match dist v, best with
    | none, _ => best
    | some d, none => some (v, d)
    | some d, some (b, db) => if d < db then some (v, d) else some (b, db)) none

/-- Main loop: settle the closest unvisited vertex, relax its edges, repeat (fuel = n). -/
def dijkstraLoop {n : ℕ} (w : Weights n) :
    ℕ → (Fin n → Option ℕ) → Finset (Fin n) → (Fin n → Option ℕ)
  | 0, dist, _ => dist
  | k + 1, dist, visited =>
    match pickMin dist visited with
    | none => dist
    | some (u, du) => dijkstraLoop w k (relax w dist u du) (insert u visited)

/-- Dijkstra's algorithm from source `s` (array version, O(n²)). -/
def dijkstra {n : ℕ} (w : Weights n) (s : Fin n) : Fin n → Option ℕ :=
  dijkstraLoop w n (fun v => if v = s then some 0 else none) ∅

/-- `Reach w s v c`: some walk from `s` to `v` has total weight `c`. -/
inductive Reach {n : ℕ} (w : Weights n) (s : Fin n) : Fin n → ℕ → Prop
  | refl : Reach w s s 0
  | step {u v : Fin n} {c c' : ℕ} : Reach w s u c → w u v = some c' → Reach w s v (c + c')

theorem omin_le_left {a : Option ℕ} {x : ℕ} (b : Option ℕ) (h : a = some x) :
    ∃ y, omin a b = some y ∧ y ≤ x := by
  subst h
  cases b with
  | none => exact ⟨x, rfl, le_refl _⟩
  | some b => exact ⟨min x b, rfl, min_le_left _ _⟩

theorem omin_le_right (a : Option ℕ) (y : ℕ) : ∃ z, omin a (some y) = some z ∧ z ≤ y := by
  cases a with
  | none => exact ⟨y, rfl, le_refl _⟩
  | some a => exact ⟨min a y, rfl, min_le_right _ _⟩

theorem omin_cases {a b : Option ℕ} {z : ℕ} (h : omin a b = some z) :
    a = some z ∨ b = some z := by
  match a, b, h with
  | none, b, h => exact Or.inr h
  | some a, none, h => exact Or.inl h
  | some a, some b, h =>
    simp only [omin, Option.some.injEq] at h
    subst h
    rcases min_choice a b with h' | h'
    · left
      rw [h']
    · right
      rw [h']

theorem relax_mono {n : ℕ} (w : Weights n) (dist : Fin n → Option ℕ) (u : Fin n) (du : ℕ)
    (v : Fin n) {x : ℕ} (h : dist v = some x) :
    ∃ y, relax w dist u du v = some y ∧ y ≤ x := by
  rcases hw : w u v with _ | c
  · exact ⟨x, by simp [relax, hw, h], le_refl _⟩
  · obtain ⟨y, hy, hle⟩ := omin_le_left (some (du + c)) h
    exact ⟨y, by simp only [relax, hw]; exact hy, hle⟩

theorem relax_edge {n : ℕ} (w : Weights n) (dist : Fin n → Option ℕ) (u : Fin n) (du : ℕ)
    (v : Fin n) {c : ℕ} (hw : w u v = some c) :
    ∃ y, relax w dist u du v = some y ∧ y ≤ du + c := by
  obtain ⟨z, hz, hle⟩ := omin_le_right (dist v) (du + c)
  exact ⟨z, by simp only [relax, hw]; exact hz, hle⟩

theorem relax_cases {n : ℕ} (w : Weights n) (dist : Fin n → Option ℕ) (u : Fin n) (du : ℕ)
    (v : Fin n) {y : ℕ} (h : relax w dist u du v = some y) :
    dist v = some y ∨ ∃ c, w u v = some c ∧ y = du + c := by
  rcases hw : w u v with _ | c
  · left
    simpa [relax, hw] using h
  · simp only [relax, hw] at h
    rcases omin_cases h with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨c, rfl, (Option.some.inj h').symm⟩

theorem relax_settled {n : ℕ} (w : Weights n) (dist : Fin n → Option ℕ) (u : Fin n) (du : ℕ)
    (x : Fin n) {dx : ℕ} (hx : dist x = some dx) (hle : dx ≤ du) :
    relax w dist u du x = some dx := by
  rcases hw : w u x with _ | c
  · simp [relax, hw, hx]
  · simp only [relax, hw, hx, omin, Option.some.injEq]
    omega

theorem fold_pick {n : ℕ} (dist : Fin n → Option ℕ) (visited : Finset (Fin n))
    (f : Option (Fin n × ℕ) → Fin n → Option (Fin n × ℕ))
    (P1 : ∀ best v, v ∈ visited → f best v = best)
    (P2 : ∀ best v, v ∉ visited → dist v = none → f best v = best)
    (P3 : ∀ v d, v ∉ visited → dist v = some d → f none v = some (v, d))
    (P4 : ∀ v d b db, v ∉ visited → dist v = some d →
      f (some (b, db)) v = if d < db then some (v, d) else some (b, db)) :
    ∀ (l : List (Fin n)) (best : Option (Fin n × ℕ)),
    (∀ b db, best = some (b, db) → b ∉ visited ∧ dist b = some db) →
    ∀ r, l.foldl f best = r →
    (∀ b db, r = some (b, db) →
      b ∉ visited ∧ dist b = some db ∧
      (∀ v ∈ l, v ∉ visited → ∀ d, dist v = some d → db ≤ d) ∧
      (∀ b0 db0, best = some (b0, db0) → db ≤ db0)) ∧
    (r = none → best = none ∧ ∀ v ∈ l, v ∉ visited → dist v = none) := by
  intro l
  induction l with
  | nil =>
    intro best hb r hr
    simp only [List.foldl_nil] at hr
    subst hr
    refine ⟨fun b db h => ?_, fun h => ⟨h, by simp⟩⟩
    obtain ⟨h1, h2⟩ := hb b db h
    refine ⟨h1, h2, by simp, ?_⟩
    intro b0 db0 h0
    rw [h] at h0
    simp only [Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨-, rfl⟩ := h0
    exact le_refl _
  | cons v l ih =>
    intro best hb r hr
    have hstep : (∀ b db, f best v = some (b, db) → b ∉ visited ∧ dist b = some db ∧
          (v ∉ visited → ∀ d, dist v = some d → db ≤ d) ∧
          (∀ b0 db0, best = some (b0, db0) → db ≤ db0)) ∧
        (f best v = none → best = none ∧ (v ∉ visited → dist v = none)) := by
      by_cases hv : v ∈ visited
      · rw [P1 best v hv]
        refine ⟨fun b db h => ?_, fun h => ⟨h, fun h' => absurd hv h'⟩⟩
        obtain ⟨h1, h2⟩ := hb b db h
        refine ⟨h1, h2, fun h' => absurd hv h', ?_⟩
        intro b0 db0 h0
        rw [h] at h0
        simp only [Option.some.injEq, Prod.mk.injEq] at h0
        obtain ⟨-, rfl⟩ := h0
        exact le_refl _
      · rcases hd : dist v with _ | d
        · rw [P2 best v hv hd]
          refine ⟨fun b db h => ?_, fun h => ⟨h, fun _ => rfl⟩⟩
          obtain ⟨h1, h2⟩ := hb b db h
          refine ⟨h1, h2, fun _ d' hd' => by simp [hd] at hd', ?_⟩
          intro b0 db0 h0
          rw [h] at h0
          simp only [Option.some.injEq, Prod.mk.injEq] at h0
          obtain ⟨-, rfl⟩ := h0
          exact le_refl _
        · rcases best with _ | ⟨b1, db1⟩
          · rw [P3 v d hv hd]
            refine ⟨fun b db h => ?_, fun h => by simp at h⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨hv, hd, fun _ d' hd' => ?_, fun b0 db0 h0 => by simp at h0⟩
            simp only [hd, Option.some.injEq] at hd'
            omega
          · rw [P4 v d b1 db1 hv hd]
            obtain ⟨hb1, hdb1⟩ := hb b1 db1 rfl
            split_ifs with hlt
            · refine ⟨fun b db h => ?_, fun h => by simp at h⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨hv, hd, fun _ d' hd' => ?_, fun b0 db0 h0 => ?_⟩
              · simp only [hd, Option.some.injEq] at hd'
                omega
              · simp only [Option.some.injEq, Prod.mk.injEq] at h0
                obtain ⟨-, rfl⟩ := h0
                omega
            · refine ⟨fun b db h => ?_, fun h => by simp at h⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨hb1, hdb1, fun _ d' hd' => ?_, fun b0 db0 h0 => ?_⟩
              · simp only [hd, Option.some.injEq] at hd'
                omega
              · simp only [Option.some.injEq, Prod.mk.injEq] at h0
                obtain ⟨-, rfl⟩ := h0
                exact le_refl _
    have hb' : ∀ b db, f best v = some (b, db) → b ∉ visited ∧ dist b = some db :=
      fun b db h => ⟨(hstep.1 b db h).1, (hstep.1 b db h).2.1⟩
    simp only [List.foldl_cons] at hr
    obtain ⟨ih1, ih2⟩ := ih (f best v) hb' r hr
    refine ⟨fun b db h => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := ih1 b db h
      refine ⟨h1, h2, ?_, ?_⟩
      · intro u hu hvis d hd
        rcases List.mem_cons.mp hu with huv | hu
        · rw [huv] at hvis hd
          rcases hfb : f best v with _ | ⟨b2, db2⟩
          · have h5 := (hstep.2 hfb).2 hvis
            simp [h5] at hd
          · have h6 := (hstep.1 b2 db2 hfb).2.2.1 hvis d hd
            have h7 := h4 b2 db2 hfb
            omega
        · exact h3 u hu hvis d hd
      · intro b0 db0 h0
        rcases hfb : f best v with _ | ⟨b2, db2⟩
        · have h5 := (hstep.2 hfb).1
          simp [h5] at h0
        · have h6 := (hstep.1 b2 db2 hfb).2.2.2 b0 db0 h0
          have h7 := h4 b2 db2 hfb
          omega
    · obtain ⟨h1, h2⟩ := ih2 h
      obtain ⟨h3, h4⟩ := hstep.2 h1
      refine ⟨h3, ?_⟩
      intro u hu hvis
      rcases List.mem_cons.mp hu with huv | hu
      · rw [huv] at hvis ⊢
        exact h4 hvis
      · exact h2 u hu hvis

theorem pickMin_spec {n : ℕ} (dist : Fin n → Option ℕ) (visited : Finset (Fin n)) :
    (∀ u du, pickMin dist visited = some (u, du) → u ∉ visited ∧ dist u = some du ∧
      ∀ v, v ∉ visited → ∀ d, dist v = some d → du ≤ d) ∧
    (pickMin dist visited = none → ∀ v, v ∉ visited → dist v = none) := by
  have H : ∀ r, pickMin dist visited = r →
      (∀ b db, r = some (b, db) →
        b ∉ visited ∧ dist b = some db ∧
        (∀ v ∈ List.finRange n, v ∉ visited → ∀ d, dist v = some d → db ≤ d) ∧
        (∀ b0 db0, (none : Option (Fin n × ℕ)) = some (b0, db0) → db ≤ db0)) ∧
      (r = none → (none : Option (Fin n × ℕ)) = none ∧
        ∀ v ∈ List.finRange n, v ∉ visited → dist v = none) := by
    unfold pickMin
    apply fold_pick
    all_goals (intros; simp_all)
  refine ⟨fun u du h => ?_, fun h v hv => ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := (H _ rfl).1 u du h
    exact ⟨h1, h2, fun v hv d hd => h3 v (List.mem_finRange v) hv d hd⟩
  · exact ((H _ rfl).2 h).2 v (List.mem_finRange v) hv

theorem optimal_of_closed {n : ℕ} (w : Weights n) (s : Fin n) (dist : Fin n → Option ℕ)
    (visited : Finset (Fin n)) (Ds : dist s = some 0)
    (R : ∀ u ∈ visited, ∀ du, dist u = some du → ∀ v c', w u v = some c' →
      ∃ dv, dist v = some dv ∧ dv ≤ du + c')
    (E : ∀ v c, dist v = some c → v ∈ visited) :
    ∀ v c, Reach w s v c → ∃ c₀, dist v = some c₀ ∧ c₀ ≤ c := by
  intro v c h
  induction h with
  | refl => exact ⟨0, Ds, le_refl _⟩
  | step hr hw ih =>
    obtain ⟨cu, hcu, hle⟩ := ih
    obtain ⟨dv, hdv, hle2⟩ := R _ (E _ _ hcu) cu hcu _ _ hw
    exact ⟨dv, hdv, by omega⟩

theorem loop_correct {n : ℕ} (w : Weights n) (s : Fin n) :
    ∀ (k : ℕ) (dist : Fin n → Option ℕ) (visited : Finset (Fin n)),
    (∀ v c, dist v = some c → Reach w s v c) →
    dist s = some 0 →
    (∀ u ∈ visited, ∃ du, dist u = some du) →
    (∀ u ∈ visited, ∀ du, dist u = some du → ∀ v dv, v ∉ visited → dist v = some dv →
      du ≤ dv) →
    (∀ u ∈ visited, ∀ du, dist u = some du → ∀ v c', w u v = some c' →
      ∃ dv, dist v = some dv ∧ dv ≤ du + c') →
    n ≤ visited.card + k →
    (∀ v c, dijkstraLoop w k dist visited v = some c → Reach w s v c) ∧
    (∀ v c, Reach w s v c → ∃ c₀, dijkstraLoop w k dist visited v = some c₀ ∧ c₀ ≤ c) := by
  intro k
  induction k with
  | zero =>
    intro dist visited S Ds V M R hk
    simp only [dijkstraLoop]
    refine ⟨S, optimal_of_closed w s dist visited Ds R ?_⟩
    intro v c _
    have h1 := Finset.card_le_univ visited
    have h2 : visited.card = Fintype.card (Fin n) := by
      simp only [Fintype.card_fin] at h1 ⊢
      omega
    rw [Finset.eq_univ_of_card visited h2]
    exact Finset.mem_univ v
  | succ k ih =>
    intro dist visited S Ds V M R hk
    obtain ⟨specS, specN⟩ := pickMin_spec dist visited
    rcases hp : pickMin dist visited with _ | ⟨u, du⟩
    · simp only [dijkstraLoop, hp]
      refine ⟨S, optimal_of_closed w s dist visited Ds R ?_⟩
      intro v c hc
      by_contra hv
      have := specN hp v hv
      simp [this] at hc
    · simp only [dijkstraLoop, hp]
      obtain ⟨hu, hdu, hmin⟩ := specS u du hp
      -- settled vertices keep their distance
      have settled : ∀ x ∈ insert u visited, ∀ dx, dist x = some dx →
          relax w dist u du x = some dx := by
        intro x hx dx hdx
        apply relax_settled w dist u du x hdx
        rcases Finset.mem_insert.mp hx with hxu | hx
        · rw [hxu, hdu] at hdx
          simp only [Option.some.injEq] at hdx
          omega
        · exact M x hx dx hdx u du hu hdu
      have old : ∀ x ∈ insert u visited, ∀ dx, relax w dist u du x = some dx →
          dist x = some dx ∧ dx ≤ du := by
        intro x hx dx hdx
        rcases Finset.mem_insert.mp hx with hxu | hx'
        · rw [hxu] at hdx ⊢
          have := settled u (Finset.mem_insert_self u visited) du hdu
          rw [this] at hdx
          simp only [Option.some.injEq] at hdx
          subst hdx
          exact ⟨hdu, le_refl _⟩
        · obtain ⟨dx0, hdx0⟩ := V x hx'
          have := settled x hx dx0 hdx0
          rw [this] at hdx
          simp only [Option.some.injEq] at hdx
          subst hdx
          exact ⟨hdx0, M x hx' dx0 hdx0 u du hu hdu⟩
      apply ih
      · intro v c h
        rcases relax_cases w dist u du v h with h' | ⟨c', hw, rfl⟩
        · exact S v c h'
        · exact Reach.step (S u du hdu) hw
      · exact relax_settled w dist u du s Ds (Nat.zero_le _)
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxu | hx'
        · rw [hxu]
          exact ⟨du, settled u (Finset.mem_insert_self u visited) du hdu⟩
        · obtain ⟨dx0, hdx0⟩ := V x hx'
          exact ⟨dx0, settled x hx dx0 hdx0⟩
      · intro x hx dx hdx v dv hv hdv
        obtain ⟨-, hxle⟩ := old x hx dx hdx
        have hvu : v ∉ visited := fun h => hv (Finset.mem_insert_of_mem h)
        rcases relax_cases w dist u du v hdv with h' | ⟨c', -, rfl⟩
        · have := hmin v hvu dv h'
          omega
        · omega
      · intro x hx dx hdx v c' hw
        obtain ⟨hdx0, -⟩ := old x hx dx hdx
        rcases Finset.mem_insert.mp hx with hxu | hx'
        · rw [hxu, hdu] at hdx0
          simp only [Option.some.injEq] at hdx0
          rw [hxu] at hw
          obtain ⟨y, hy, hle⟩ := relax_edge w dist u du v hw
          exact ⟨y, hy, by omega⟩
        · obtain ⟨dv, hdv, hle⟩ := R x hx' dx hdx0 v c' hw
          obtain ⟨y, hy, hle2⟩ := relax_mono w dist u du v hdv
          exact ⟨y, hy, by omega⟩
      · rw [Finset.card_insert_of_notMem hu]
        omega

/-- Dijkstra is correct: every reported distance is the weight of a real walk, and it is
at most the weight of every walk. So it is exactly the shortest-path distance, and `none`
exactly when `v` is unreachable. -/
theorem dijkstra_correct {n : ℕ} (w : Weights n) (s v : Fin n) :
    (∀ c, dijkstra w s v = some c → Reach w s v c) ∧
    (∀ c, Reach w s v c → ∃ c₀, dijkstra w s v = some c₀ ∧ c₀ ≤ c) := by
  have hS : ∀ v c, (fun v => if v = s then some 0 else none) v = some c → Reach w s v c := by
    intro v c h
    by_cases hv : v = s
    · subst hv
      simp at h
      subst h
      exact Reach.refl
    · simp [hv] at h
  have hDs : (fun v => if v = s then some 0 else none) s = some 0 := by simp
  have H := loop_correct w s n (fun v => if v = s then some 0 else none) ∅ hS hDs
    (by intro u hu; simp at hu) (by intro u hu; simp at hu) (by intro u hu; simp at hu)
    (by simp)
  exact ⟨H.1 v, H.2 v⟩

end VerifiedAlgorithms
