import Ref.Sem

/-!
# The reference to run agrees with the definition

`sem Oracle.exec` never has a value where `sem (Oracle.classical χ)`, the
definition, has another, whatever the choice function `χ`: where both
have a value, it is the same. The evaluator is the same for every oracle,
and `exec` answers a question only where every choice function answers
it alike, so the proof follows the evaluator, one level at a time.
-/
namespace Ref

/-- Two results agree where both are values. -/
def Agree {α} (a b : M α) : Prop := ∀ x y, a = .ok x → b = .ok y → x = y

@[simp] theorem undef_eq {α} (why) : (undef why : M α) = .error (.undef why) := _root_.rfl
@[simp] theorem unknown_eq {α} (why) : (unknown why : M α) = .error (.unknown why) := _root_.rfl

/-- Lists of results that agree, one by one. -/
inductive Pointwise : List (M Bool) → List (M Bool) → Prop
  | nil : Pointwise [] []
  | cons {a b l1 l2} : Agree a b → Pointwise l1 l2 → Pointwise (a :: l1) (b :: l2)

namespace Agree

theorem refl {α} {a : M α} : Agree a a := by
  intro x y h1 h2; rw [h1] at h2; cases h2; exact _root_.rfl

theorem err_left {α} {e} {b : M α} : Agree (.error e) b := by
  intro x y h; cases h

theorem err_right {α} {e} {a : M α} : Agree a (.error e) := by
  intro x y _ h; cases h

theorem bind {α β} {a b : M α} {f g : α → M β} (h : Agree a b) (hf : ∀ x, Agree (f x) (g x)) :
    Agree (a >>= f) (b >>= g) := by
  intro x y h1 h2
  cases ha : a <;> cases hb : b <;> simp_all [Bind.bind, Except.bind]
  rename_i u v
  exact hf u x y h1 (h u v _root_.rfl _root_.rfl ▸ h2)

theorem map {α β} {a b : M α} (f : α → β) (h : Agree a b) : Agree (f <$> a) (f <$> b) := by
  have : ∀ (c : M α), f <$> c = c >>= fun x => pure (f x) := fun c => by
    cases c <;> rfl
  rw [this, this]
  exact bind h fun x => refl

theorem ite {α} {p : Prop} [Decidable p] {a b c d : M α} (h1 : Agree a b) (h2 : Agree c d) :
    Agree (if p then a else c) (if p then b else d) := by
  split <;> assumption

theorem mapM {α β} {f g : α → M β} : ∀ {l : List α}, (∀ x ∈ l, Agree (f x) (g x)) →
    Agree (l.mapM f) (l.mapM g)
  | [], _ => refl
  | x :: l, h => by
    simp only [List.mapM_cons]
    exact bind (h x (.head _)) fun u => bind (mapM fun y hy => h y (.tail _ hy)) fun _ => refl

theorem foldlM {α β} {f g : β → α → M β} : ∀ {l : List α} {init : β},
    (∀ acc, ∀ x ∈ l, Agree (f acc x) (g acc x)) → Agree (l.foldlM f init) (l.foldlM g init)
  | [], _, _ => refl
  | x :: l, _, h => by
    simp only [List.foldlM_cons]
    exact bind (h _ x (.head _)) fun _ => foldlM fun acc y hy => h acc y (.tail _ hy)

theorem filterAuxM {α} {p q : α → M Bool} : ∀ {l acc : List α}, (∀ x ∈ l, Agree (p x) (q x)) →
    Agree (List.filterAuxM p l acc) (List.filterAuxM q l acc)
  | [], _, _ => refl
  | x :: l, _, h => by
    simp only [List.filterAuxM]
    exact bind (h x (.head _)) fun _ => filterAuxM fun y hy => h y (.tail _ hy)

theorem filterM {α} {p q : α → M Bool} {l : List α} (h : ∀ x ∈ l, Agree (p x) (q x)) :
    Agree (l.filterM p) (l.filterM q) := by
  simp only [List.filterM]
  exact bind (filterAuxM h) fun _ => refl

/-- One step of `anyOf`: its head, then the rest's result. -/
def anyStep (a r : M Bool) : M Bool :=
  match a with
  | .ok true => .ok true
  | .ok false => r
  | .error e => match r with
    | .ok true => .ok true
    | _ => .error e

theorem anyOf_cons (a : M Bool) (l : List (M Bool)) : Ref.anyOf (a :: l) = anyStep a (Ref.anyOf l) := by
  rcases a with e | ⟨_ | _⟩ <;> rfl

theorem anyStep_agree {a b r1 r2 : M Bool} (hab : Agree a b) (hr : Agree r1 r2) :
    Agree (anyStep a r1) (anyStep b r2) := by
  intro x y h1 h2
  rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;>
    rcases r1 with _ | ⟨_ | _⟩ <;> rcases r2 with _ | ⟨_ | _⟩ <;>
    simp_all [anyStep, Agree]

theorem anyOf : ∀ {l1 l2 : List (M Bool)}, Pointwise l1 l2 → Agree (Ref.anyOf l1) (Ref.anyOf l2)
  | [], [], _ => refl
  | a :: _, b :: _, .cons hab hl => by
    rw [anyOf_cons, anyOf_cons]; exact anyStep_agree hab (anyOf hl)

theorem forall₂_map {α} {f g : α → M Bool} : ∀ {l : List α}, (∀ x ∈ l, Agree (f x) (g x)) →
    Pointwise (l.map f) (l.map g)
  | [], _ => .nil
  | x :: _, h => .cons (h x (.head _)) (forall₂_map fun y hy => h y (.tail _ hy))

theorem pointwise_append : ∀ {a1 a2 b1 b2 : List (M Bool)}, Pointwise a1 a2 → Pointwise b1 b2 →
    Pointwise (a1 ++ b1) (a2 ++ b2)
  | _, _, _, _, .nil, hb => hb
  | _, _, _, _, .cons h t, hb => .cons h (pointwise_append t hb)

theorem not {a b : M Bool} (h : Agree a b) : Agree ((! ·) <$> a) ((! ·) <$> b) := map _ h

theorem allOf {l1 l2 : List (M Bool)} (h : Pointwise l1 l2) : Agree (Ref.allOf l1) (Ref.allOf l2) := by
  unfold Ref.allOf
  apply not; apply anyOf
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (not hab) ih

theorem strictAll {l1 l2 : List (M Bool)} (h : Pointwise l1 l2) :
    Agree (Ref.strictAll l1) (Ref.strictAll l2) := by
  unfold Ref.strictAll
  refine bind ?_ fun _ => refl
  induction h with
  | nil => exact refl
  | cons hab _ ih =>
    simp only [List.mapM_cons]
    exact bind hab fun _ => bind ih fun _ => refl

end Agree

/-- Two oracles agree where both answer questions that agree. -/
structure OAgree (O1 O2 : Oracle) : Prop where
  all : ∀ m1 m2 p1 p2, (∀ v, Agree (m1 v) (m2 v)) → (∀ v, Agree (p1 v) (p2 v)) →
    Agree (O1.all m1 p1) (O2.all m2 p2)
  same : ∀ a1 a2 b1 b2, (∀ v, Agree (a1 v) (a2 v)) → (∀ v, Agree (b1 v) (b2 v)) →
    Agree (O1.same a1 b1) (O2.same a2 b2)
  finite : ∀ e1 e2 m1 m2, (∀ u v, Agree (e1 u v) (e2 u v)) → (∀ v, Agree (m1 v) (m2 v)) →
    Agree (O1.finite e1 m1) (O2.finite e2 m2)
  card : ∀ e1 e2 m1 m2, (∀ u v, Agree (e1 u v) (e2 u v)) → (∀ v, Agree (m1 v) (m2 v)) →
    Agree (O1.card e1 m1) (O2.card e2 m2)
  choose : ∀ s1 s2 h, (∀ v, Agree (s1 v) (s2 v)) → Agree (O1.choose s1 h) (O2.choose s2 h)

theorem exec_classical (χ) : OAgree Oracle.exec (Oracle.classical χ) where
  all _ _ _ _ _ _ := Agree.err_left
  same _ _ _ _ _ _ := Agree.err_left
  finite _ _ _ _ _ _ := Agree.err_left
  card _ _ _ _ _ _ := Agree.err_left
  choose s1 s2 h _ := by
    intro x y h1 h2
    match h with
    | some [w] =>
      simp only [Oracle.exec, Oracle.classical, pure, Except.pure] at h1 h2
      cases h1; cases h2
      simp only [List.find?]
      split <;> rfl
    | some [] => simp [Oracle.exec] at h1
    | some (_ :: _ :: _) => simp [Oracle.exec] at h1
    | none => simp [Oracle.exec] at h1

/-- Two contexts agree: the same world, and agreeing evaluations. -/
structure CAgree (c1 c2 : Ctx) : Prop where
  w : c1.w = c2.w
  O : OAgree c1.O c2.O
  ev : ∀ σ ρ e, Agree (c1.ev σ ρ e) (c2.ev σ ρ e)
  mem : ∀ a b, Agree (c1.mem a b) (c2.mem a b)
  eq : ∀ a b, Agree (c1.eq a b) (c2.eq a b)
  app : ∀ a b, Agree (c1.app a b) (c2.app a b)

/-- One step of agreement of the same code over agreeing contexts. -/
syntax "agree_step" : tactic
syntax "agree" : tactic
macro_rules | `(tactic| agree) => `(tactic| repeat' agree_step)
macro_rules | `(tactic| agree_step) => `(tactic| first | split | with_reducible first
  | exact Agree.refl
  | exact Agree.err_left
  | exact Agree.err_right
  | exact (‹CAgree _ _›).ev _ _ _
  | exact (‹CAgree _ _›).mem _ _
  | exact (‹CAgree _ _›).eq _ _
  | exact (‹CAgree _ _›).app _ _
  | (apply Agree.bind; intro _)
  | (apply Agree.bind)
  | apply Agree.map
  | apply Agree.ite
  | (apply Agree.mapM; intro _ _)
  | (apply Agree.filterM; intro _ _)
  | (apply Agree.foldlM; intro _ _ _)
  | apply Agree.anyOf
  | apply Agree.allOf
  | apply Agree.strictAll
  | exact Pointwise.nil
  | apply Pointwise.cons
  | apply Agree.pointwise_append
  | (apply Agree.forall₂_map; intro _ _)
  | (apply (‹CAgree _ _›).O.choose; intro _)
  | (apply (‹CAgree _ _›).O.same <;> intro _)
  | exact (‹CAgree _ _›).O.card _ _ _ _ (fun _ _ => (‹CAgree _ _›).eq _ _) (fun _ => (‹CAgree _ _›).mem _ _)
  | exact (‹CAgree _ _›).O.finite _ _ _ _ (fun _ _ => (‹CAgree _ _›).eq _ _) (fun _ => (‹CAgree _ _›).mem _ _)
  | (intro _; skip))

namespace Ctx
variable {c1 c2 : Ctx} (h : CAgree c1 c2)
include h

theorem lookup_eq : c1.lookup = c2.lookup := by
  funext ρ x; unfold Ctx.lookup; rw [h.w]

theorem arg_eq : c1.arg = c2.arg := by
  funext ρ e; unfold Ctx.arg; rw [h.w]

theorem mkSet_agree (vs) : Agree (c1.mkSet vs) (c2.mkSet vs) := by
  unfold Ctx.mkSet
  apply Agree.ite Agree.refl
  apply Agree.map; apply Agree.foldlM; intro out v _
  apply Agree.bind (Agree.anyOf (Agree.forall₂_map fun y _ => h.eq v y)); intro _; exact Agree.refl

theorem mkFcn_agree (g) : Agree (c1.mkFcn g) (c2.mkFcn g) := by
  unfold Ctx.mkFcn
  apply Agree.map; apply Agree.foldlM; intro out kv _
  apply Agree.bind (Agree.anyOf (Agree.forall₂_map fun y _ => h.eq _ _)); intro _; exact Agree.refl

theorem all_agree (S) {p1 p2 : Val → M Bool} (hp : ∀ v, Agree (p1 v) (p2 v)) :
    Agree (c1.all S p1) (c2.all S p2) := by
  unfold Ctx.all
  split
  · apply Agree.strictAll; apply Agree.forall₂_map; intro v _; exact hp v
  all_goals first
    | exact Agree.refl
    | exact h.O.all _ _ _ _ (fun v => h.mem _ _) hp

theorem any_agree (S) {p1 p2 : Val → M Bool} (hp : ∀ v, Agree (p1 v) (p2 v)) :
    Agree (c1.any S p1) (c2.any S p2) :=
  Agree.map _ (all_agree h S fun v => Agree.map _ (hp v))

theorem subseteq_agree (A B) : Agree (c1.subseteq A B) (c2.subseteq A B) :=
  all_agree h A fun v => h.mem v B

theorem update_agree (σ ρ) : ∀ f path e, Agree (c1.update σ ρ f path e) (c2.update σ ρ f path e)
  | f, [], e => by unfold Ctx.update; agree
  | f, k :: path, e => by
    unfold Ctx.update
    split
    · apply Agree.map; apply Agree.mapM; intro _ _
      apply Agree.bind (h.eq _ _); intro b
      apply Agree.ite
      · exact Agree.bind (update_agree σ ρ _ path e) fun _ => Agree.refl
      · exact Agree.refl
    · exact Agree.refl

end Ctx

macro_rules | `(tactic| agree_step) => `(tactic| with_reducible first
  | exact Ctx.mkSet_agree ‹CAgree _ _› _
  | exact Ctx.mkFcn_agree ‹CAgree _ _› _
  | exact Ctx.subseteq_agree ‹CAgree _ _› _ _
  | (apply Ctx.all_agree ‹CAgree _ _›; intro _)
  | (apply Ctx.any_agree ‹CAgree _ _›; intro _))

namespace Ctx
variable {c1 c2 : Ctx} (h : CAgree c1 c2)
include h

theorem binder_agree (σ ρ b x S body) :
    Agree (c1.binder σ ρ b x S body) (c2.binder σ ρ b x S body) := by
  unfold Ctx.binder
  cases b <;> dsimp only
  case select => cases S.seq? <;> dsimp only <;> agree
  all_goals agree

theorem strict1_agree (o S) : Agree (c1.strict1 o S) (c2.strict1 o S) := by
  unfold Ctx.strict1; agree

theorem strict2_agree (o A B) : Agree (c1.strict2 o A B) (c2.strict2 o A B) := by
  unfold Ctx.strict2; agree

theorem strict_agree (o vs) : Agree (c1.strict o vs) (c2.strict o vs) := by
  unfold Ctx.strict
  split
  all_goals first
    | exact mkSet_agree h _
    | exact strict1_agree h _ _
    | exact strict2_agree h _ _ _
    | agree

theorem unchanged_agree (σ ρ e) : Agree (c1.unchanged σ ρ e) (c2.unchanged σ ρ e) := by
  unfold Ctx.unchanged; agree

theorem force_agree (v) : Agree (c1.force v) (c2.force v) := by
  unfold Ctx.force; agree

theorem lookupIn_agree (a) : ∀ g, Agree (c1.lookupIn a g) (c2.lookupIn a g)
  | [] => Agree.refl
  | _ :: g => by unfold Ctx.lookupIn; apply Agree.bind (h.eq _ _); intro _; exact Agree.ite Agree.refl (lookupIn_agree a g)

end Ctx

macro_rules | `(tactic| agree_step) => `(tactic| with_reducible first
  | exact Ctx.strict_agree ‹CAgree _ _› _ _
  | exact Ctx.binder_agree ‹CAgree _ _› _ _ _ _ _ _
  | exact Ctx.update_agree ‹CAgree _ _› _ _ _ _ _
  | exact Ctx.unchanged_agree ‹CAgree _ _› _ _ _
  | exact Ctx.force_agree ‹CAgree _ _› _
  | exact Ctx.lookupIn_agree ‹CAgree _ _› _ _)

namespace Ctx
variable {c1 c2 : Ctx} (h : CAgree c1 c2)
include h

theorem op_agree (σ ρ o args) : Agree (c1.op σ ρ o args) (c2.op σ ρ o args) := by
  unfold Ctx.op Ctx.op.strictOp
  rw [lookup_eq h, arg_eq h, h.w]
  agree

theorem eval_agree (σ ρ e) : Agree (c1.eval σ ρ e) (c2.eval σ ρ e) := by
  unfold Ctx.eval
  rw [lookup_eq h, h.w]
  cases e <;> dsimp only
  all_goals first
    | exact op_agree h _ _ _ _
    | agree

theorem member_agree (v S) : Agree (c1.member v S) (c2.member v S) := by
  unfold Ctx.member; agree

theorem equal_agree (a b) : Agree (c1.equal a b) (c2.equal a b) := by
  unfold Ctx.equal; agree

theorem apply_agree (f a) : Agree (c1.apply f a) (c2.apply f a) := by
  unfold Ctx.apply; agree

end Ctx

/-- At every depth, evaluating with `exec` agrees with the definition. -/
theorem tie_agree (χ w) : ∀ n, CAgree (tie .exec w n) (tie (.classical χ) w n)
  | 0 => ⟨_root_.rfl, exec_classical χ, fun _ _ _ => Agree.err_left, fun _ _ => Agree.err_left,
          fun _ _ => Agree.err_left, fun _ _ => Agree.err_left⟩
  | n + 1 =>
    have h := tie_agree χ w n
    ⟨_root_.rfl, exec_classical χ, fun σ ρ e => Agree.map _ (Ctx.eval_agree h σ ρ e), Ctx.member_agree h,
     Ctx.equal_agree h, Ctx.apply_agree h⟩

/-- Where the reference to run has a value, the definition has no other,
whatever the choice function. -/
theorem sem_agree (χ w n σ ρ e) : Agree (sem .exec w n σ ρ e) (sem (.classical χ) w n σ ρ e) :=
  (tie_agree χ w n).ev σ ρ e

end Ref
