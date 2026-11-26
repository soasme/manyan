import Ref.Choice

/-!
# A value with nothing kept unevaluated is kept one way

The evaluator gives each value in order (`Val.canon`): its sets and
functions sorted by `Val.code`, each value once. So two equal values it
computes with nothing kept unevaluated are the same (`computed_eq`), and
nothing it computes, as which element `CHOOSE` takes, can depend on how
a value is written.
-/
namespace Ref

/-- `x` before `y` in a sorted list: no later, and not the same unless
both are `[6]`, which values kept unevaluated share. -/
def Before (x y : List Int) : Prop := x ≤ y ∧ (x = y → x = [6])

/-! ## Sorting -/

section
variable {α : Type}

theorem mem_nub : ∀ {l : List (List Int × α)} {p}, p ∈ sortBy.nub l → p ∈ l
  | [], _, h => by simp [sortBy.nub] at h
  | q :: l, p, h => by
    rw [sortBy.nub] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact .head _
    · exact .tail _ ((List.dropWhile_suffix _).subset (mem_nub h))
termination_by l => l.length
decreasing_by simp_wf; exact Nat.lt_succ_of_le ((List.dropWhile_suffix _).length_le)

theorem pairwise_nub : ∀ {l : List (List Int × α)}, l.Pairwise (fun p q => p.1 ≤ q.1) →
    (sortBy.nub l).Pairwise (fun p q => Before p.1 q.1)
  | [], _ => by simp [sortBy.nub]
  | a :: l, h => by
    rw [sortBy.nub]
    have hs := (List.dropWhile_suffix (fun b : List Int × α => b.1 == a.1 && a.1 != [6]) (l := l)).sublist
    have hl := List.pairwise_cons.1 h
    refine List.pairwise_cons.2 ⟨fun b hb => ?_, pairwise_nub (hl.2.sublist hs)⟩
    have hb := mem_nub hb
    refine ⟨hl.1 b (hs.subset hb), fun e => ?_⟩
    -- The first left is not one dropped, and lies between `a` and `b`.
    refine Classical.byContradiction fun ne => ?_
    have hne : l.dropWhile (fun b : List Int × α => b.1 == a.1 && a.1 != [6]) ≠ [] := List.ne_nil_of_mem hb
    have hd := List.head_dropWhile_not (fun b : List Int × α => b.1 == a.1 && a.1 != [6]) hne
    have hhead := List.head_mem hne
    have le1 := hl.1 _ (hs.subset hhead)
    have le2 : ((l.dropWhile _).head hne).1 ≤ b.1 := by
      generalize hr : l.dropWhile (fun b : List Int × α => b.1 == a.1 && a.1 != [6]) = r at hb hne hhead hd ⊢
      have hrp : r.Pairwise (fun p q : List Int × α => p.1 ≤ q.1) := hr ▸ hl.2.sublist hs
      cases r with
      | nil => cases hb
      | cons x r =>
        simp only [List.head_cons]
        rcases List.mem_cons.1 hb with rfl | hb
        · exact List.le_refl _
        · exact (List.pairwise_cons.1 hrp).1 b hb
    rw [← e] at le2
    have : ((l.dropWhile _).head hne).1 = a.1 := List.le_antisymm le2 le1
    simp [this, ne] at hd
termination_by l => l.length
decreasing_by simp_wf; exact Nat.lt_succ_of_le ((List.dropWhile_suffix _).length_le)

theorem mem_dropWhile {p : α → Bool} {a} (ha : p a = false) : ∀ {l : List α}, a ∈ l → a ∈ l.dropWhile p
  | x :: l, h => by
    rw [List.dropWhile_cons]
    split
    · rcases List.mem_cons.1 h with rfl | h
      · simp_all
      · exact mem_dropWhile ha h
    · exact h

/-- What `sortBy` drops has the key of one it keeps. -/
theorem nub_complete : ∀ {l : List (List Int × α)} {a}, a ∈ l → ∃ b ∈ sortBy.nub l, b.1 = a.1
  | [], _, h => by cases h
  | b :: l, a, h => by
    rw [sortBy.nub]
    by_cases hd : (a.1 == b.1 && b.1 != [6]) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hd
      exact ⟨b, .head _, hd.1.symm⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨a, .head _, rfl⟩
      · have : a ∈ l.dropWhile fun c : List Int × α => c.1 == b.1 && b.1 != [6] :=
          mem_dropWhile (by simpa using hd) h
        obtain ⟨c, hc, e⟩ := nub_complete this
        exact ⟨c, .tail _ hc, e⟩
termination_by l => l.length
decreasing_by simp_wf; exact Nat.lt_succ_of_le ((List.dropWhile_suffix _).length_le)

variable (k : α → List Int)

/-- What `sortBy` keeps, with its key. -/
theorem mem_keyed {l : List α} {p} (h : p ∈ sortBy.nub ((l.map fun a => (k a, a)).mergeSort
    fun p q => decide (p.1 ≤ q.1))) : p.2 ∈ l ∧ p.1 = k p.2 := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ((List.mergeSort_perm _ _).mem_iff.1 (mem_nub h))
  exact ⟨ha, rfl⟩

theorem mem_sortBy {l : List α} {a} (h : a ∈ sortBy k l) : a ∈ l := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact (mem_keyed k hp).1

theorem pairwise_sortBy (l : List α) : (sortBy k l).Pairwise (fun a b => Before (k a) (k b)) := by
  unfold sortBy
  rw [List.pairwise_map]
  have := List.pairwise_mergeSort (le := fun p q : List Int × α => decide (p.1 ≤ q.1))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; exact List.le_trans h1 h2)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact List.le_total _ _)
    (l.map fun a => (k a, a))
  refine (pairwise_nub (by simpa using this)).imp_of_mem fun hp hq e => ?_
  rw [← (mem_keyed k hp).2, ← (mem_keyed k hq).2]; exact e

theorem sortBy_complete {l : List α} {a} (h : a ∈ l) : ∃ b ∈ sortBy k l, k b = k a := by
  have : (k a, a) ∈ (l.map fun a => (k a, a)).mergeSort fun p q => decide (p.1 ≤ q.1) :=
    (List.mergeSort_perm _ _).mem_iff.2 (List.mem_map.2 ⟨a, h, rfl⟩)
  obtain ⟨q, hq, e⟩ := nub_complete this
  exact ⟨q.2, List.mem_map.2 ⟨q, hq, rfl⟩, (mem_keyed k hq).2 ▸ e⟩

end

/-! ## Codes -/

theorem ground_set (l : List Val) : (Val.set l).ground ↔ ∀ a ∈ l, a.ground := by
  rw [Val.ground]; simp

theorem ground_fcn (g : List (Val × Val)) :
    (Val.fcn g).ground ↔ ∀ p ∈ g, p.1.ground ∧ p.2.ground := by
  rw [Val.ground]; simp

theorem enc_cons (v : Val) (h : v.ground) : ∃ t r, v.enc = t :: r ∧ 0 ≤ t ∧ t < 6 := by
  cases v <;> rw [Val.enc] <;> first | exact ⟨_, _, rfl, by decide, by decide⟩ | simp [Val.ground] at h

theorem code_lt_six {v : Val} (h : v.ground) : v.code < [6] := by
  obtain ⟨t, r, e, -, ht⟩ := enc_cons v h
  rw [Val.code]; simp only [h, ↓reduceIte, e]; exact List.Lex.rel ht

theorem code_le_six (v : Val) : v.code ≤ [6] := by
  by_cases h : v.ground
  · exact List.le_of_lt (code_lt_six h)
  · rw [Val.code]; simp only [h, Bool.false_eq_true, ↓reduceIte]; exact List.le_refl _

/-- In a sorted list, values with nothing kept unevaluated come in strict order. -/
theorem lt_of_before {a b : Val} (ha : a.ground) (h : Before a.code b.code) : a.code < b.code :=
  Std.lt_of_le_of_ne h.1 fun e => List.lt_irrefl _ (h.2 e ▸ code_lt_six ha)

theorem enc_set (l : List Val) : (Val.set l).enc = 4 :: (l.map Val.enc).flatten ++ [-1] := by
  rw [Val.enc]; simp

theorem enc_fcn (g : List (Val × Val)) :
    (Val.fcn g).enc = 5 :: (g.map fun p => p.1.enc ++ p.2.enc).flatten ++ [-1] := by
  rw [Val.enc]; simp only [List.cons_append, List.cons.injEq, true_and]
  rw [List.attach_map_val (f := fun p : Val × Val => p.1.enc ++ p.2.enc)]

/-- Codes, each followed by -1, which none starts with, are read back one way. -/
theorem flat_prefix {β} (f : β → List Int) : ∀ {l l' : List β} {r s : List Int},
    (∀ a ∈ l, ∀ b ∈ l', ∀ r s, f a ++ r = f b ++ s → a = b ∧ r = s) →
    (∀ b, b ∈ l ∨ b ∈ l' → ∃ t u, f b = t :: u ∧ 0 ≤ t) →
    (l.map f).flatten ++ -1 :: r = (l'.map f).flatten ++ -1 :: s → l = l' ∧ r = s
  | [], [], _, _, _, _, h => by simpa using h
  | [], b :: _, _, _, _, hp, h => by
    obtain ⟨t, u, e, ht⟩ := hp b (.inr (.head _))
    simp only [List.map_cons, List.flatten_cons, e] at h; simp at h; omega
  | a :: _, [], _, _, _, hp, h => by
    obtain ⟨t, u, e, ht⟩ := hp a (.inl (.head _))
    simp only [List.map_cons, List.flatten_cons, e] at h; simp at h; omega
  | a :: l, b :: l', r, s, hf, hp, h => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
    obtain ⟨rfl, e⟩ := hf a (.head _) b (.head _) _ _ h
    obtain ⟨rfl, rfl⟩ := flat_prefix f (fun a ha b hb => hf a (.tail _ ha) b (.tail _ hb))
      (fun b hb => hp b (hb.imp (.tail _) (.tail _))) e
    exact ⟨rfl, rfl⟩

theorem singletons {β} (f : β → Int) : ∀ l : List β, (l.map fun b => [f b]).flatten = l.map f
  | [] => rfl
  | b :: l => by simp [singletons f l]

theorem chars_prefix {x y : String} {r s : List Int}
    (h : (x.toList.map fun ch => (ch.toNat : Int)) ++ -1 :: r =
      (y.toList.map fun ch => (ch.toNat : Int)) ++ -1 :: s) : x = y ∧ r = s := by
  have := flat_prefix (fun ch : Char => [(ch.toNat : Int)]) (l := x.toList) (l' := y.toList) (r := r) (s := s)
    (fun a _ b _ r s e => by
      simp only [List.singleton_append, List.cons.injEq, Int.ofNat_inj] at e
      exact ⟨Char.toNat_inj.mp e.1, e.2⟩)
    (fun b _ => ⟨_, _, rfl, Int.natCast_nonneg _⟩)
    (by rw [singletons, singletons]; exact h)
  exact ⟨String.toList_inj.mp this.1, this.2⟩

/-- A code is not the start of another. -/
theorem enc_prefix_n : ∀ n (a b : Val), sizeOf a + sizeOf b < n → a.ground → b.ground →
    ∀ r s, a.enc ++ r = b.enc ++ s → a = b ∧ r = s
  | 0, _, _, hn, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, a, b, hn, ga, gb, r, s, h => by
    cases a <;> cases b
    all_goals try (simp [Val.ground] at ga; done)
    all_goals try (simp [Val.ground] at gb; done)
    all_goals try simp only [enc_set, enc_fcn] at h
    all_goals try (simp [Val.enc] at h; done)
    all_goals try (simp [Val.enc] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    all_goals simp only [Val.enc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    · rename_i x y; cases x <;> cases y <;> simp_all
    · obtain ⟨rfl, rfl⟩ := chars_prefix h; exact ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := chars_prefix h; exact ⟨rfl, rfl⟩
    · rename_i x y
      have gx := (ground_set x).1 ga
      have gy := (ground_set y).1 gb
      obtain ⟨rfl, rfl⟩ := flat_prefix Val.enc
        (fun a ha b hb r s e => enc_prefix_n n a b
          (by have := size_set ha; have := size_set hb; omega) (gx a ha) (gy b hb) r s e)
        (fun b hb => let ⟨t, u, e, ht, _⟩ := enc_cons b (hb.elim (gx b) (gy b)); ⟨t, u, e, ht⟩) h
      exact ⟨rfl, rfl⟩
    · rename_i x y
      have gx := (ground_fcn x).1 ga
      have gy := (ground_fcn y).1 gb
      obtain ⟨rfl, rfl⟩ := flat_prefix (fun p : Val × Val => p.1.enc ++ p.2.enc)
        (fun p hp q hq r s e => by
          simp only [List.append_assoc] at e
          obtain ⟨k, e⟩ := enc_prefix_n n p.1 q.1
            (by have := size_fst hp; have := size_fst hq; omega) (gx p hp).1 (gy q hq).1 _ _ e
          obtain ⟨v, rfl⟩ := enc_prefix_n n p.2 q.2
            (by have := size_snd hp; have := size_snd hq; omega) (gx p hp).2 (gy q hq).2 _ _ e
          exact ⟨Prod.ext k v, rfl⟩)
        (fun p hp => let ⟨t, u, e, ht, _⟩ := enc_cons p.1 (hp.elim (fun h => (gx p h).1) (fun h => (gy p h).1))
          ⟨t, u ++ p.2.enc, by simp [e], ht⟩) h
      exact ⟨rfl, rfl⟩

theorem enc_inj {a b : Val} (ga : a.ground) (gb : b.ground) (h : a.enc = b.enc) : a = b :=
  (enc_prefix_n _ a b (Nat.lt_succ_self _) ga gb [] [] (by simp [h])).1

theorem code_inj {a b : Val} (ga : a.ground) (gb : b.ground) (h : a.code = b.code) : a = b := by
  simp only [Val.code, ga, gb, ↓reduceIte] at h; exact enc_inj ga gb h

/-! ## Values in order -/

/-- A value whose sets and functions are in order of `Val.code`. -/
inductive Canon : Val → Prop
  | bool (b) : Canon (.bool b)
  | int (n) : Canon (.int n)
  | str (s) : Canon (.str s)
  | model (s) : Canon (.model s)
  | lazy (s) : Canon (.lazy s)
  | set {l : List Val} : (∀ a ∈ l, Canon a) → l.Pairwise (fun a b => Before a.code b.code) →
      Canon (.set l)
  | fcn {g : List (Val × Val)} : (∀ p ∈ g, Canon p.1) → (∀ p ∈ g, Canon p.2) →
      g.Pairwise (fun p q => Before p.1.code q.1.code) → Canon (.fcn g)

theorem canon_set (l : List Val) :
    (Val.set l).canon = .set (sortBy Val.code (l.attach.map fun ⟨a, _⟩ => a.canon)) := by
  rw [Val.canon]

theorem canon_fcn (g : List (Val × Val)) :
    (Val.fcn g).canon = .fcn (sortBy (·.1.code) (g.attach.map fun ⟨p, _⟩ => (p.1.canon, p.2.canon))) := by
  rw [Val.canon]

theorem canon_canon : ∀ v : Val, Canon v.canon
  | .bool _ | .int _ | .str _ | .model _ | .lazy _ => by unfold Val.canon; constructor
  | .set l => by
    rw [canon_set]
    refine .set (fun b hb => ?_) (pairwise_sortBy _ _)
    obtain ⟨⟨a, ha⟩, _, rfl⟩ := List.mem_map.1 (mem_sortBy _ hb)
    have := List.sizeOf_lt_of_mem ha
    exact canon_canon a
  | .fcn g => by
    rw [canon_fcn]
    have h : ∀ q ∈ sortBy (·.1.code) (g.attach.map fun ⟨p, _⟩ => (p.1.canon, p.2.canon)),
        Canon q.1 ∧ Canon q.2 := fun q hq => by
      obtain ⟨⟨p, hp⟩, _, rfl⟩ := List.mem_map.1 (mem_sortBy _ hq)
      have := List.sizeOf_lt_of_mem hp
      exact ⟨canon_canon p.1, canon_canon p.2⟩
    exact .fcn (fun q hq => (h q hq).1) (fun q hq => (h q hq).2) (pairwise_sortBy _ _)
termination_by v => sizeOf v
decreasing_by all_goals (simp_wf; first | omega | (cases p; simp at *; omega))

theorem ground_of_Ground {v : Val} (h : Ground v) : v.ground := by
  induction h with
  | bool | int | str | model => simp [Val.ground]
  | set _ ih => exact (ground_set _).2 ih
  | fcn _ _ _ ihk ihv => exact (ground_fcn _).2 fun p hp => ⟨ihk p hp, ihv p hp⟩

/-- `Val.canon` keeps what a value with nothing kept unevaluated is. -/
theorem ground_canon : ∀ v : Val, v.ground → v.canon.ground
  | .bool _, h | .int _, h | .str _, h | .model _, h | .lazy _, h => by unfold Val.canon; exact h
  | .set l, h => by
    rw [canon_set, ground_set]
    intro b hb
    obtain ⟨⟨a, ha⟩, _, rfl⟩ := List.mem_map.1 (mem_sortBy _ hb)
    have := List.sizeOf_lt_of_mem ha
    exact ground_canon a ((ground_set l).1 h a ha)
  | .fcn g, h => by
    rw [canon_fcn, ground_fcn]
    intro q hq
    obtain ⟨⟨p, hp⟩, _, rfl⟩ := List.mem_map.1 (mem_sortBy _ hq)
    have := List.sizeOf_lt_of_mem hp
    have g := (ground_fcn g).1 h p hp
    exact ⟨ground_canon p.1 g.1, ground_canon p.2 g.2⟩
termination_by v => sizeOf v
decreasing_by all_goals (simp_wf; first | omega | (cases p; simp at *; omega))

theorem canon_feq : ∀ v : Val, Ground v → Feq v.canon v
  | .bool _, h | .int _, h | .str _, h | .model _, h | .lazy _, h => by unfold Val.canon; exact feq_refl h
  | .set l, h => by
    cases h with | set hl =>
    have gl : ∀ a ∈ l, a.ground := fun a ha => ground_of_Ground (hl a ha)
    rw [canon_set, feq_set]
    refine ⟨fun b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨⟨a, ha⟩, _, rfl⟩ := List.mem_map.1 (mem_sortBy _ hb)
      have := List.sizeOf_lt_of_mem ha
      exact ⟨a, ha, canon_feq a (hl a ha)⟩
    · have hm : a.canon ∈ l.attach.map (fun ⟨a, _⟩ => a.canon) := List.mem_map.2 ⟨⟨a, ha⟩, List.mem_attach _ _, rfl⟩
      obtain ⟨b, hb, e⟩ := sortBy_complete _ hm
      obtain ⟨⟨c, hc⟩, _, rfl⟩ := List.mem_map.1 (mem_sortBy _ hb)
      have := List.sizeOf_lt_of_mem ha
      have := code_inj (ground_canon c (gl c hc)) (ground_canon a (gl a ha)) e
      exact ⟨c.canon, hb, this ▸ canon_feq a (hl a ha)⟩
  | .fcn g, h => by
    cases h with | fcn hk hv hf =>
    rw [canon_fcn, feq_fcn]
    refine ⟨fun q hq => ?_, fun p hp => ?_, fun q hq p hp e => ?_⟩
    · obtain ⟨⟨c, hc⟩, _, rfl⟩ := List.mem_map.1 (mem_sortBy _ hq)
      have := size_fst hc
      exact ⟨c, hc, canon_feq c.1 (hk c hc)⟩
    · have hm : (p.1.canon, p.2.canon) ∈ g.attach.map (fun ⟨p, _⟩ => (p.1.canon, p.2.canon)) :=
        List.mem_map.2 ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩
      obtain ⟨q, hq, e⟩ := sortBy_complete (fun q : Val × Val => q.1.code) hm
      obtain ⟨⟨c, hc⟩, _, rfl⟩ := List.mem_map.1 (mem_sortBy _ hq)
      have := size_fst hp
      have := code_inj (ground_canon c.1 (ground_of_Ground (hk c hc)))
        (ground_canon p.1 (ground_of_Ground (hk p hp))) (by simpa using e)
      refine ⟨_, hq, ?_⟩
      show Feq c.1.canon p.1
      rw [this]; exact canon_feq p.1 (hk p hp)
    · obtain ⟨⟨c, hc⟩, _, rfl⟩ := List.mem_map.1 (mem_sortBy _ hq)
      have := size_fst hc
      have := size_snd hc
      have k : Feq c.1 p.1 := feq_trans (feq_symm (canon_feq c.1 (hk c hc))) e
      exact feq_trans (canon_feq c.2 (hv c hc)) (hf c hc p hp k)
termination_by v => sizeOf v
decreasing_by all_goals (simp_wf; simp at *; omega)

/-! ## One way -/

/-- Two lists in strict order with the same elements are the same. -/
theorem sorted_unique {α} {R : α → α → Prop} (irr : ∀ a, ¬ R a a) (asymm : ∀ a b, R a b → ¬ R b a) :
    ∀ {l l' : List α}, l.Pairwise R → l'.Pairwise R → (∀ a, a ∈ l ↔ a ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (.head _)) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).1 (.head _)) List.not_mem_nil
  | a :: l, b :: l', hl, hl', h => by
    have hl := List.pairwise_cons.1 hl
    have hl' := List.pairwise_cons.1 hl'
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 (.head _)) with e | ha
      · exact e
      · rcases List.mem_cons.1 ((h b).2 (.head _)) with e | hb
        · exact e.symm
        · exact absurd (hl.1 b hb) (asymm _ _ (hl'.1 a ha))
    subst hab
    have tail : ∀ x, x ∈ l ↔ x ∈ l' := fun x =>
      ⟨fun hx => (List.mem_cons.1 ((h x).1 (.tail _ hx))).resolve_left
          fun e => irr a (e ▸ hl.1 x hx),
       fun hx => (List.mem_cons.1 ((h x).2 (.tail _ hx))).resolve_left
          fun e => irr a (e ▸ hl'.1 x hx)⟩
    rw [sorted_unique irr asymm hl.2 hl'.2 tail]

theorem strict {l : List Val} (hg : ∀ a ∈ l, a.ground) (h : l.Pairwise fun a b => Before a.code b.code) :
    l.Pairwise fun a b => a.code < b.code :=
  h.imp_of_mem fun ha _ e => lt_of_before (hg _ ha) e

theorem strict_fst {g : List (Val × Val)} (hg : ∀ p ∈ g, p.1.ground)
    (h : g.Pairwise fun p q => Before p.1.code q.1.code) : g.Pairwise fun p q => p.1.code < q.1.code :=
  h.imp_of_mem fun hp _ e => lt_of_before (hg _ hp) e

theorem canon_eq_n : ∀ n (a b : Val), sizeOf a + sizeOf b < n → Canon a → Canon b →
    a.ground → b.ground → Feq a b → a = b
  | 0, _, _, hn, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, a, b, hn, ca, cb, ga, gb, h => by
    rcases feq_kind h with ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ |
      ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
    all_goals try (rw [Feq, Val.feq] at h; simp at h; rw [h])
    · cases ca with | set hx px => cases cb with | set hy py =>
      have gx := (ground_set x).1 ga
      have gy := (ground_set y).1 gb
      have ih : ∀ a ∈ x, ∀ b ∈ y, Feq a b → a = b := fun a ha b hb =>
        canon_eq_n n a b (by have := size_set ha; have := size_set hb; omega)
          (hx a ha) (hy b hb) (gx a ha) (gy b hb)
      have ⟨f, g⟩ := (feq_set x y).1 h
      rw [sorted_unique (R := fun a b : Val => a.code < b.code) (fun a => List.lt_irrefl _)
        (fun _ _ => List.lt_asymm) (strict gx px) (strict gy py) fun a =>
          ⟨fun ha => let ⟨b, hb, e⟩ := f a ha; ih a ha b hb e ▸ hb,
           fun hb => let ⟨c, hc, e⟩ := g a hb; (ih c hc a hb e) ▸ hc⟩]
    · cases ca with | fcn hxk hxv px => cases cb with | fcn hyk hyv py =>
      have gx := (ground_fcn x).1 ga
      have gy := (ground_fcn y).1 gb
      have ⟨f, g, v⟩ := (feq_fcn x y).1 h
      have ih : ∀ p ∈ x, ∀ q ∈ y, Feq p.1 q.1 → p = q := fun p hp q hq e => by
        have k := canon_eq_n n p.1 q.1 (by have := size_fst hp; have := size_fst hq; omega)
          (hxk p hp) (hyk q hq) (gx p hp).1 (gy q hq).1 e
        have w := canon_eq_n n p.2 q.2 (by have := size_snd hp; have := size_snd hq; omega)
          (hxv p hp) (hyv q hq) (gx p hp).2 (gy q hq).2 (v p hp q hq e)
        exact Prod.ext k w
      rw [sorted_unique (R := fun p q : Val × Val => p.1.code < q.1.code) (fun a => List.lt_irrefl _)
        (fun _ _ => List.lt_asymm) (strict_fst (fun p hp => (gx p hp).1) px)
        (strict_fst (fun p hp => (gy p hp).1) py) fun p =>
          ⟨fun hp => let ⟨q, hq, e⟩ := f p hp; ih p hp q hq e ▸ hq,
           fun hq => let ⟨c, hc, e⟩ := g p hq; (ih c hc p hq e) ▸ hc⟩]

theorem pairwise_or {α} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l →
    a = b ∨ R a b ∨ R b a
  | _ :: _, h, _, _, ha, hb => by
    have h := List.pairwise_cons.1 h
    rcases List.mem_cons.1 ha with ea | ha' <;> rcases List.mem_cons.1 hb with eb | hb'
    · exact .inl (ea.trans eb.symm)
    · subst ea; exact .inr (.inl (h.1 _ hb'))
    · subst eb; exact .inr (.inr (h.1 _ ha'))
    · exact pairwise_or h.2 ha' hb'

/-- Equal values in order, with nothing kept unevaluated, are the same. -/
theorem canon_eq {a b : Val} (ca : Canon a) (cb : Canon b) (ga : a.ground) (gb : b.ground)
    (h : Feq a b) : a = b :=
  canon_eq_n _ a b (Nat.lt_succ_self _) ca cb ga gb h

/-- A value in order with nothing kept unevaluated maps equal arguments
to equal values, so `Ref/Choice.lean` holds of it. -/
theorem ground_of_canon : ∀ v : Val, Canon v → v.ground → Ground v
  | .bool _, _, _ => .bool _
  | .int _, _, _ => .int _
  | .str _, _, _ => .str _
  | .model _, _, _ => .model _
  | .lazy _, _, h => by simp [Val.ground] at h
  | .set l, c, h => by
    cases c with | set hl _ =>
    have g := (ground_set l).1 h
    exact .set fun a ha => by
      have := List.sizeOf_lt_of_mem ha
      exact ground_of_canon a (hl a ha) (g a ha)
  | .fcn x, c, h => by
    cases c with | fcn hk hv px =>
    have g := (ground_fcn x).1 h
    have gk : ∀ p ∈ x, Ground p.1 := fun p hp => by
      have := size_fst hp
      exact ground_of_canon p.1 (hk p hp) (g p hp).1
    have gv : ∀ p ∈ x, Ground p.2 := fun p hp => by
      have := size_snd hp
      exact ground_of_canon p.2 (hv p hp) (g p hp).2
    refine .fcn gk gv fun p hp q hq e => ?_
    have k := canon_eq (hk p hp) (hk q hq) (g p hp).1 (g q hq).1 e
    rcases pairwise_or (strict_fst (fun p hp => (g p hp).1) px) hp hq with rfl | lt | lt
    · exact feq_refl (gv p hp)
    · exact absurd (k ▸ lt) (List.lt_irrefl _)
    · exact absurd (k ▸ lt) (List.lt_irrefl _)
termination_by v => sizeOf v
decreasing_by all_goals (simp_wf; simp at *; omega)

/-! ## The values the evaluator computes -/

/-- Every value the evaluator computes is in order. -/
theorem sem_canon {O w n σ ρ e v} (h : sem O w n σ ρ e = .ok v) : Canon v := by
  cases n with
  | zero => simp [sem, tie, unknown, throw, throwThe, MonadExceptOf.throw] at h
  | succ n =>
    simp only [sem, tie] at h
    cases he : (tie O w n).eval σ ρ e with
    | error => rw [he] at h; cases h
    | ok x => rw [he] at h; cases h; exact canon_canon x

/-- Two values the evaluator computes with nothing kept unevaluated are
the same if they are equal, as `=` has them, whatever it computed them
from: there is one way to write each, so nothing it computes can depend
on how a value is written. -/
theorem computed_eq {O w n σ ρ e a O' w' n' σ' ρ' e' b}
    (ha : sem O w n σ ρ e = .ok a) (hb : sem O' w' n' σ' ρ' e' = .ok b)
    (ga : a.ground) (gb : b.ground) (h : Feq a b) : a = b :=
  canon_eq (sem_canon ha) (sem_canon hb) ga gb h

/-- The same, with `=` as the evaluator computes it, at any depth and
with any oracle. -/
theorem computed_eq_eval {O w n σ ρ e a O' w' n' σ' ρ' e' b O'' w'' m}
    (ha : sem O w n σ ρ e = .ok a) (hb : sem O' w' n' σ' ρ' e' = .ok b)
    (ga : a.ground) (gb : b.ground) (h : (tie O'' w'' m).eq a b = .ok true) : a = b :=
  computed_eq ha hb ga gb ((eqSound_tie O'' w'' m).eq a b true
    (ground_of_canon a (sem_canon ha) ga) (ground_of_canon b (sem_canon hb) gb) h).symm

end Ref
