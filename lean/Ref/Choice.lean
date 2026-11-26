import Ref.Sound

/-!
# `CHOOSE` takes a value of the set, not of its enumeration

`Oracle.classical χ` takes `CHOOSE x \in S : P`, for an enumerated `S`,
as χ's choice of a value equal (`Val.feq`) to one of the elements that
satisfy `P`. This proves that it is TLA⁺'s: `Val.feq` is an equivalence
on the values with nothing kept unevaluated (`Fin`), the evaluator's `=`
is `Val.feq` wherever it answers, and so two enumerations of the same
set, as `=` has it, give equal choices.
-/
namespace Ref

/-- `a.feq b`, as a proposition. -/
abbrev Feq (a b : Val) : Prop := a.feq b = true

theorem feq_set (x y : List Val) :
    Feq (.set x) (.set y) ↔ (∀ a ∈ x, ∃ b ∈ y, Feq a b) ∧ (∀ b ∈ y, ∃ a ∈ x, Feq a b) := by
  rw [Feq, Val.feq]; simp

theorem bimp (a b : Bool) : ((!a || b) = true) ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp

theorem feq_fcn (x y : List (Val × Val)) :
    Feq (.fcn x) (.fcn y) ↔ (∀ p ∈ x, ∃ q ∈ y, Feq p.1 q.1) ∧ (∀ q ∈ y, ∃ p ∈ x, Feq p.1 q.1) ∧
      (∀ p ∈ x, ∀ q ∈ y, Feq p.1 q.1 → Feq p.2 q.2) := by
  rw [Feq, Val.feq]
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_attach, true_and,
    Subtype.exists, Subtype.forall, bimp, and_assoc, true_implies, exists_prop, Feq]

/-- Values of different kinds are apart. -/
theorem feq_kind {a b : Val} (h : Feq a b) :
    (∃ x y, a = .bool x ∧ b = .bool y) ∨ (∃ x y, a = .int x ∧ b = .int y) ∨
    (∃ x y, a = .str x ∧ b = .str y) ∨ (∃ x y, a = .model x ∧ b = .model y) ∨
    (∃ x y, a = .set x ∧ b = .set y) ∨ (∃ x y, a = .fcn x ∧ b = .fcn y) := by
  unfold Feq Val.feq at h
  split at h <;> simp_all

theorem size_set {a : Val} {x : List Val} (h : a ∈ x) : sizeOf a < sizeOf (Val.set x) := by
  have := List.sizeOf_lt_of_mem h; simp; omega

theorem size_fst {p : Val × Val} {x : List (Val × Val)} (h : p ∈ x) : sizeOf p.1 < sizeOf (Val.fcn x) := by
  have := List.sizeOf_lt_of_mem h; cases p; simp at *; omega

theorem size_snd {p : Val × Val} {x : List (Val × Val)} (h : p ∈ x) : sizeOf p.2 < sizeOf (Val.fcn x) := by
  have := List.sizeOf_lt_of_mem h; cases p; simp at *; omega

theorem feq_atom {α} [BEq α] [LawfulBEq α] {x y : α} (h : (x == y) = true) : (y == x) = true := by
  simp_all

theorem feq_symm_n : ∀ n (a b : Val), sizeOf a + sizeOf b < n → Feq a b → Feq b a
  | 0, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, a, b, hn, h => by
    rcases feq_kind h with ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ |
      ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
    all_goals try (rw [Feq, Val.feq] at h ⊢; exact feq_atom h)
    · have ih : ∀ a ∈ x, ∀ b ∈ y, Feq a b → Feq b a := fun a ha b hb =>
        feq_symm_n n a b (by have := size_set ha; have := size_set hb; omega)
      have ih' : ∀ b ∈ y, ∀ a ∈ x, Feq b a → Feq a b := fun b hb a ha =>
        feq_symm_n n b a (by have := size_set ha; have := size_set hb; omega)
      rw [feq_set] at h ⊢
      exact ⟨fun b hb => let ⟨a, ha, e⟩ := h.2 b hb; ⟨a, ha, ih a ha b hb e⟩,
             fun a ha => let ⟨b, hb, e⟩ := h.1 a ha; ⟨b, hb, ih a ha b hb e⟩⟩
    · have ih : ∀ p ∈ x, ∀ q ∈ y, (Feq p.1 q.1 → Feq q.1 p.1) ∧ (Feq q.1 p.1 → Feq p.1 q.1) ∧
          (Feq p.2 q.2 → Feq q.2 p.2) := fun p hp q hq =>
        ⟨feq_symm_n n _ _ (by have := size_fst hp; have := size_fst hq; omega),
         feq_symm_n n _ _ (by have := size_fst hp; have := size_fst hq; omega),
         feq_symm_n n _ _ (by have := size_snd hp; have := size_snd hq; omega)⟩
      rw [feq_fcn] at h ⊢
      exact ⟨fun q hq => let ⟨p, hp, e⟩ := h.2.1 q hq; ⟨p, hp, (ih p hp q hq).1 e⟩,
             fun p hp => let ⟨q, hq, e⟩ := h.1 p hp; ⟨q, hq, (ih p hp q hq).1 e⟩,
             fun q hq p hp e => (ih p hp q hq).2.2 (h.2.2 p hp q hq ((ih p hp q hq).2.1 e))⟩

theorem feq_symm {a b : Val} (h : Feq a b) : Feq b a := feq_symm_n _ a b (Nat.lt_succ_self _) h

theorem feq_atom_trans {α} [BEq α] [LawfulBEq α] {x y z : α} (h1 : (x == y) = true)
    (h2 : (y == z) = true) : (x == z) = true := by
  simp_all

theorem feq_trans_n : ∀ n (a b c : Val), sizeOf a + sizeOf b + sizeOf c < n → Feq a b → Feq b c → Feq a c
  | 0, _, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, a, b, c, hn, h1, h2 => by
    rcases feq_kind h1 with ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ |
      ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ <;>
    rcases feq_kind h2 with ⟨_, z, hb, rfl⟩ | ⟨_, z, hb, rfl⟩ | ⟨_, z, hb, rfl⟩ | ⟨_, z, hb, rfl⟩ |
      ⟨_, z, hb, rfl⟩ | ⟨_, z, hb, rfl⟩ <;> cases hb
    all_goals try (rw [Feq, Val.feq] at h1 h2 ⊢; exact feq_atom_trans h1 h2)
    · have ih : ∀ a ∈ x, ∀ b ∈ y, ∀ c ∈ z, Feq a b → Feq b c → Feq a c := fun a ha b hb c hc =>
        feq_trans_n n a b c (by have := size_set ha; have := size_set hb; have := size_set hc; omega)
      rw [feq_set] at h1 h2 ⊢
      exact ⟨fun a ha => let ⟨b, hb, e⟩ := h1.1 a ha; let ⟨c, hc, e'⟩ := h2.1 b hb; ⟨c, hc, ih a ha b hb c hc e e'⟩,
             fun c hc => let ⟨b, hb, e'⟩ := h2.2 c hc; let ⟨a, ha, e⟩ := h1.2 b hb; ⟨a, ha, ih a ha b hb c hc e e'⟩⟩
    · rw [feq_fcn] at h1 h2 ⊢
      have ih : ∀ p ∈ x, ∀ q ∈ y, ∀ r ∈ z, (Feq p.1 q.1 → Feq q.1 r.1 → Feq p.1 r.1) ∧
          (Feq q.1 p.1 → Feq p.1 r.1 → Feq q.1 r.1) ∧ (Feq p.2 q.2 → Feq q.2 r.2 → Feq p.2 r.2) :=
        fun p hp q hq r hr =>
          ⟨feq_trans_n n _ _ _ (by have := size_fst hp; have := size_fst hq; have := size_fst hr; omega),
           feq_trans_n n _ _ _ (by have := size_fst hp; have := size_fst hq; have := size_fst hr; omega),
           feq_trans_n n _ _ _ (by have := size_snd hp; have := size_snd hq; have := size_snd hr; omega)⟩
      refine ⟨fun p hp => ?_, fun r hr => ?_, fun p hp r hr e => ?_⟩
      · obtain ⟨q, hq, e⟩ := h1.1 p hp; obtain ⟨r, hr, e'⟩ := h2.1 q hq
        exact ⟨r, hr, (ih p hp q hq r hr).1 e e'⟩
      · obtain ⟨q, hq, e'⟩ := h2.2.1 r hr; obtain ⟨p, hp, e⟩ := h1.2.1 q hq
        exact ⟨p, hp, (ih p hp q hq r hr).1 e e'⟩
      · obtain ⟨q, hq, eq⟩ := h1.1 p hp
        have eqr := (ih p hp q hq r hr).2.1 (feq_symm eq) e
        exact (ih p hp q hq r hr).2.2 (h1.2.2 p hp q hq eq) (h2.2.2 q hq r hr eqr)

theorem feq_trans {a b c : Val} (h1 : Feq a b) (h2 : Feq b c) : Feq a c :=
  feq_trans_n _ a b c (Nat.lt_succ_self _) h1 h2

/-- A value with nothing kept unevaluated, whose functions map equal
arguments to equal values. -/
inductive Ground : Val → Prop
  | bool (b) : Ground (.bool b)
  | int (n) : Ground (.int n)
  | str (s) : Ground (.str s)
  | model (s) : Ground (.model s)
  | set {l : List Val} : (∀ a ∈ l, Ground a) → Ground (.set l)
  | fcn {g : List (Val × Val)} : (∀ p ∈ g, Ground p.1) → (∀ p ∈ g, Ground p.2) →
      (∀ p ∈ g, ∀ q ∈ g, Feq p.1 q.1 → Feq p.2 q.2) → Ground (.fcn g)

theorem feq_refl {a : Val} (h : Ground a) : Feq a a := by
  induction h with
  | bool | int | str | model => rw [Feq, Val.feq]; simp
  | set _ ih => rw [feq_set]; exact ⟨fun a ha => ⟨a, ha, ih a ha⟩, fun a ha => ⟨a, ha, ih a ha⟩⟩
  | fcn _ _ hf ihk _ =>
    rw [feq_fcn]; exact ⟨fun p hp => ⟨p, hp, ihk p hp⟩, fun p hp => ⟨p, hp, ihk p hp⟩, hf⟩

/-! ## The evaluator's `=` is `Val.feq` -/

theorem anyOf_true : ∀ {l : List (M Bool)}, anyOf l = .ok true → ∃ m ∈ l, m = .ok true
  | [], h => by simp [anyOf, pure, Except.pure] at h
  | a :: l, h => by
    rw [Agree.anyOf_cons] at h
    rcases a with e | ⟨_ | _⟩ <;> simp only [Agree.anyStep] at h
    · split at h
      · obtain ⟨m, hm, e⟩ := anyOf_true ‹_›; exact ⟨m, .tail _ hm, e⟩
      · cases h
    · obtain ⟨m, hm, e⟩ := anyOf_true h; exact ⟨m, .tail _ hm, e⟩
    · exact ⟨_, .head _, rfl⟩

theorem anyOf_false : ∀ {l : List (M Bool)}, anyOf l = .ok false → ∀ m ∈ l, m = .ok false
  | [], _ => by simp
  | a :: l, h => by
    rw [Agree.anyOf_cons] at h
    rcases a with e | ⟨_ | _⟩ <;> simp only [Agree.anyStep] at h
    · split at h <;> cases h
    · intro m hm; cases hm with
      | head => rfl
      | tail _ hm => exact anyOf_false h m hm
    · cases h

theorem allOf_true {l : List (M Bool)} (h : allOf l = .ok true) : ∀ m ∈ l, m = .ok true := by
  unfold allOf at h
  cases ha : anyOf (l.map fun r => (! ·) <$> r) with
  | error => rw [ha] at h; cases h
  | ok b =>
    rw [ha] at h; simp [Functor.map, Except.map] at h; subst h
    intro m hm
    have := anyOf_false ha _ (List.mem_map_of_mem hm)
    cases m with
    | error => simp [Functor.map, Except.map] at this
    | ok x => cases x <;> simp_all [Functor.map, Except.map]

theorem allOf_false {l : List (M Bool)} (h : allOf l = .ok false) : ∃ m ∈ l, m = .ok false := by
  unfold allOf at h
  cases ha : anyOf (l.map fun r => (! ·) <$> r) with
  | error => rw [ha] at h; cases h
  | ok b =>
    rw [ha] at h; simp [Functor.map, Except.map] at h; subst h
    obtain ⟨m', hm', e⟩ := anyOf_true ha
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm'
    refine ⟨m, hm, ?_⟩
    cases m with
    | error => simp [Functor.map, Except.map] at e
    | ok x => cases x <;> simp_all [Functor.map, Except.map]

/-- A context whose `=`, membership in an enumerated set and application
of an enumerated function are `Val.feq`'s, where they answer. -/
structure EqSound (c : Ctx) : Prop where
  eq : ∀ a b r, Ground a → Ground b → c.eq a b = .ok r → r = a.feq b
  mem : ∀ v l r, Ground v → (∀ u ∈ l, Ground u) → c.mem v (.set l) = .ok r → r = l.any v.feq
  app : ∀ g a r, Ground (.fcn g) → Ground a → c.app (.fcn g) a = .ok r → ∃ p ∈ g, Feq a p.1 ∧ r = p.2

theorem Ground.elems {l} (h : Ground (.set l)) : ∀ a ∈ l, Ground a := by cases h; assumption

theorem bool_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

namespace Ctx
variable {c : Ctx} (hc : EqSound c)
include hc

theorem member_sound (v l r) (hv : Ground v) (hl : ∀ u ∈ l, Ground u) (h : c.member v (.set l) = .ok r) :
    r = l.any v.feq := by
  unfold Ctx.member at h
  cases r
  · have := anyOf_false h
    refine (List.any_eq_false.2 fun u hu => ?_).symm
    have := hc.eq v u false hv (hl u hu) (this _ (List.mem_map_of_mem hu))
    simp [← this]
  · obtain ⟨m, hm, e⟩ := anyOf_true h
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hm
    exact (List.any_eq_true.2 ⟨u, hu, (hc.eq v u true hv (hl u hu) e).symm⟩).symm

theorem lookupIn_sound (a) : ∀ g r, (∀ p ∈ g, Ground p.1) → Ground a → c.lookupIn a g = .ok r →
    ∃ p ∈ g, Feq a p.1 ∧ r = p.2
  | [], _, _, _, h => by simp [Ctx.lookupIn] at h
  | (k, v) :: g, r, hg, ha, h => by
    unfold Ctx.lookupIn at h
    cases he : c.eq a k with
    | error => rw [he] at h; cases h
    | ok b =>
      have hb := hc.eq a k b ha (hg _ (.head _)) he
      rw [he] at h
      cases b
      · obtain ⟨p, hp, e⟩ := lookupIn_sound a g r (fun p hp => hg p (.tail _ hp)) ha h
        exact ⟨p, .tail _ hp, e⟩
      · simp [bind, Except.bind, pure, Except.pure] at h
        exact ⟨(k, v), .head _, hb.symm, h.symm⟩

theorem apply_sound (g a r) (hg : Ground (.fcn g)) (ha : Ground a) (h : c.apply (.fcn g) a = .ok r) :
    ∃ p ∈ g, Feq a p.1 ∧ r = p.2 := by
  unfold Ctx.apply at h
  cases hg with
  | fcn hk _ _ => exact lookupIn_sound hc a g r hk ha h

omit hc in
theorem keys_ground {g : List (Val × Val)} (h : ∀ p ∈ g, Ground p.1) : Ground (.set (g.map Prod.fst)) :=
  .set fun a ha => by obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha; exact h p hp

omit hc in
theorem feq_keys (x y : List (Val × Val)) : Feq (.set (x.map Prod.fst)) (.set (y.map Prod.fst)) ↔
    (∀ p ∈ x, ∃ q ∈ y, Feq p.1 q.1) ∧ (∀ q ∈ y, ∃ p ∈ x, Feq p.1 q.1) := by
  rw [feq_set]; simp

theorem equal_sound (a b r) (ha : Ground a) (hb : Ground b) (h : c.equal a b = .ok r) : r = a.feq b := by
  cases ha <;> cases hb
  all_goals try (unfold Ctx.equal at h; simp [Val.isFcn, Val.isSet] at h; done)
  all_goals try (unfold Ctx.equal at h; simp [pure, Except.pure] at h; subst h; rw [Val.feq]; done)
  · -- sets
    rename_i x hx y hy
    unfold Ctx.equal at h
    cases r
    · obtain ⟨m, hm, e⟩ := allOf_false h
      symm; rw [Bool.eq_false_iff]; intro hf
      rcases List.mem_append.1 hm with hm | hm <;> obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hm
      · have := hc.mem u y false (hx u hu) hy e
        obtain ⟨b, hb, e'⟩ := ((feq_set x y).1 hf).1 u hu
        exact List.any_eq_false.1 this.symm b hb e'
      · have := hc.mem u x false (hy u hu) hx e
        obtain ⟨b, hb, e'⟩ := ((feq_set x y).1 hf).2 u hu
        have := List.any_eq_false.1 this.symm b hb
        exact this (feq_symm e')
    · have hall := allOf_true h
      refine Eq.symm ((feq_set x y).2 ⟨fun u hu => ?_, fun u hu => ?_⟩)
      · have := hc.mem u y true (hx u hu) hy (hall _ (List.mem_append_left _ (List.mem_map_of_mem hu)))
        exact List.any_eq_true.1 this.symm
      · have := hc.mem u x true (hy u hu) hx (hall _ (List.mem_append_right _ (List.mem_map_of_mem hu)))
        obtain ⟨b, hb, e⟩ := List.any_eq_true.1 this.symm
        exact ⟨b, hb, feq_symm e⟩
  · -- functions
    rename_i x hxk hxv hxf y hyk hyv hyf
    unfold Ctx.equal at h
    dsimp only at h
    cases hk : c.eq (.set (x.map Prod.fst)) (.set (y.map Prod.fst)) with
    | error => rw [hk] at h; cases h
    | ok kb =>
      have kfeq := hc.eq _ _ kb (keys_ground hxk) (keys_ground hyk) hk
      rw [hk] at h
      cases kb
      · simp [bind, Except.bind, pure, Except.pure] at h; subst h
        symm; rw [Bool.eq_false_iff]; intro hf
        have := ((feq_fcn x y).1 hf)
        have := (feq_keys x y).2 ⟨this.1, this.2.1⟩
        simp_all
      · have ks := (feq_keys x y).1 kfeq.symm
        simp only [bind, Except.bind, Bool.not_true] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        -- each pair: its value against y's at its argument
        have step : ∀ p ∈ x, ∀ b, (c.app (.fcn y) p.1 >>= c.eq p.2) = .ok b → ∃ q ∈ y, Feq p.1 q.1 ∧ b = p.2.feq q.2 := by
          intro p hp b e
          cases ha : c.app (.fcn y) p.1 with
          | error => rw [ha] at e; cases e
          | ok v' =>
            rw [ha] at e
            obtain ⟨q, hq, hkq, rfl⟩ := hc.app y p.1 v' (.fcn hyk hyv hyf) (hxk p hp) ha
            change c.eq p.2 q.2 = _ at e
            exact ⟨q, hq, hkq, hc.eq _ _ b (hxv p hp) (hyv q hq) e⟩
        cases r
        · obtain ⟨m, hm, e⟩ := allOf_false h
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
          obtain ⟨q, hq, hkq, hv⟩ := step p hp false (by simpa only [bind, Except.bind] using e)
          symm; rw [Bool.eq_false_iff]; intro hf
          have := ((feq_fcn x y).1 hf).2.2 p hp q hq hkq
          simp_all
        · have hall := allOf_true h
          refine Eq.symm ((feq_fcn x y).2 ⟨ks.1, ks.2, fun p hp q' hq' e => ?_⟩)
          obtain ⟨q, hq, hkq, hv⟩ := step p hp true
            (by simpa only [bind, Except.bind] using hall _ (List.mem_map.2 ⟨p, hp, rfl⟩))
          have : Feq q.1 q'.1 := feq_trans (feq_symm hkq) e
          exact feq_trans hv.symm (hyf q hq q' hq' this)

end Ctx

/-- At every depth and with any oracle, the evaluator's `=` is `Val.feq`
where it answers. -/
theorem eqSound_tie (O w) : ∀ n, EqSound (tie O w n)
  | 0 => ⟨fun _ _ _ _ _ h => by simp [tie] at h, fun _ _ _ _ _ h => by simp [tie] at h,
          fun _ _ _ _ _ h => by simp [tie] at h⟩
  | n + 1 =>
    have hc := eqSound_tie O w n
    ⟨Ctx.equal_sound hc, Ctx.member_sound hc, Ctx.apply_sound hc⟩

/-! ## `CHOOSE` -/

/-- χ chooses: of a predicate some value satisfies, a value that does. -/
def Chooses (χ : (Val → Prop) → Val) : Prop := ∀ P : Val → Prop, (∃ v, P v) → P (χ P)

theorem pick_feq {χ} (hχ : Chooses χ) {l : List Val} {w : Val} (hl : ∀ u ∈ w :: l, Ground u) :
    Feq (χ fun v => ∃ u ∈ w :: l, Feq v u)
      (((w :: l).find? (Val.feq (χ fun v => ∃ u ∈ w :: l, Feq v u))).getD w) := by
  have hp := hχ (fun v => ∃ u ∈ w :: l, Feq v u) ⟨w, w, .head _, feq_refl (hl w (.head _))⟩
  obtain ⟨u, hu, e⟩ := hp
  cases hf : (w :: l).find? (Val.feq (χ fun v => ∃ u ∈ w :: l, Feq v u)) with
  | none => exact absurd e (by simpa using List.find?_eq_none.1 hf u hu)
  | some r => simpa using List.find?_some hf

/-- `CHOOSE` from two enumerations of the same set (as `=` has it) of
values with nothing kept unevaluated takes equal values: the value it
takes is a function of the set. -/
theorem choose_same (χ) (hχ : Chooses χ) {l l' : List Val} (hl : ∀ u ∈ l, Ground u)
    (hl' : ∀ u ∈ l', Ground u) (same : Feq (.set l) (.set l')) (s s' : Val → M Bool) {r r'}
    (h : (Oracle.classical χ).choose s (some l) = .ok r)
    (h' : (Oracle.classical χ).choose s' (some l') = .ok r') : Feq r r' := by
  have hP : (fun v => ∃ u ∈ l, Feq v u) = (fun v => ∃ u ∈ l', Feq v u) := by
    funext v; apply propext
    have ⟨f, g⟩ := (feq_set l l').1 same
    exact ⟨fun ⟨u, hu, e⟩ => let ⟨u', hu', e'⟩ := f u hu; ⟨u', hu', feq_trans e e'⟩,
           fun ⟨u', hu', e'⟩ => let ⟨u, hu, e⟩ := g u' hu'; ⟨u, hu, feq_trans e' (feq_symm e)⟩⟩
  match l, l', h, h' with
  | [], _, h, _ => simp [Oracle.classical] at h
  | _, [], _, h' => simp [Oracle.classical] at h'
  | w :: l, w' :: l', h, h' =>
    simp only [Oracle.classical, pure, Except.pure, Except.ok.injEq] at h h'
    subst h h'
    have e := pick_feq hχ hl
    have e' := pick_feq hχ hl'
    have hc : (χ fun v => ∃ u ∈ w :: l, Feq v u) = χ fun v => ∃ u ∈ w' :: l', Feq v u := congrArg χ hP
    simp only [Feq] at e e' hc ⊢
    rw [hc] at e ⊢
    exact feq_trans (feq_symm e) e'

/-- So where the evaluator has two enumerated sets equal, `CHOOSE` takes
equal values from them. -/
theorem choose_eq (χ) (hχ : Chooses χ) (O w n) {l l' : List Val} (hl : ∀ u ∈ l, Ground u)
    (hl' : ∀ u ∈ l', Ground u) (heq : (tie O w n).eq (.set l) (.set l') = .ok true)
    (s s' : Val → M Bool) {r r'}
    (h : (Oracle.classical χ).choose s (some l) = .ok r)
    (h' : (Oracle.classical χ).choose s' (some l') = .ok r') : Feq r r' :=
  choose_same χ hχ hl hl' ((eqSound_tie O w n).eq _ _ _ (.set hl) (.set hl') heq).symm s s' h h'

end Ref
