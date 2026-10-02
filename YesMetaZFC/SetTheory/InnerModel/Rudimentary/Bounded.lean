import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Construction

/-! # Jensen 运算图的有界表示

集合像按两个方向刻画：每个成员有输入见证，每组合法输入有输出成员。
反向要求实际输出存在，不能只把无界成员等式的量词限制到任意容器。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

inductive Ri_sym where
  | prod | mid | last | range | mem | fibers

def ri_left_l {α : Type u} : Ri_sym → α → α → α
  | .prod, x, _ | .range, x, _ | .mem, x, _ => x
  | .mid, _, y | .last, _, y | .fibers, _, y => y

def ri_right_l {α : Type u} : Ri_sym → α → α → α
  | .prod, _, y | .fibers, _, y => y
  | .mid, x, _ | .last, x, _ | .range, x, _ | .mem, x, _ => x

def Ri_valid_d (p : M.Domain) : Prop := ∃ a b, KPair_d M p a b

def ri_valid_m {n} (p : Term n) : Formula 1 n :=
  Formula.existsMem p (Formula.existsMem .newest (Formula.existsMem p.weaken.weaken
    (Formula.existsMem .newest (kpair0_m p.weaken.weaken.weaken.weaken (.bound 2) .newest))))
derive_free_closed ri_valid_m

theorem ri_valid_delta_l {n} (p : Term n) : (ri_valid_m p).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))

theorem ri_valid_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p : Term n) :
    Formula.satisfies ρ (ri_valid_m p) ↔ Ri_valid_d (p.eval ρ) := by
  simp only [ri_valid_m, Formula.satisfies_existsMem_iff, kpair0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨_, _, a, _, _, _, b, _, h⟩; exact ⟨a, b, h⟩
  · rintro ⟨a, b, h⟩
    obtain ⟨s, hs, ha⟩ := (kpair_union_l M h a).mpr (Or.inl rfl)
    obtain ⟨t, ht, hb⟩ := (kpair_union_l M h b).mpr (Or.inr rfl)
    exact ⟨s, hs, a, ha, t, ht, b, hb, h⟩

def Ri_guard_d : Ri_sym → M.Domain → M.Domain → Prop
  | .mid, a, _ | .last, a, _ | .range, a, _ => Ri_valid_d a
  | .mem, a, b => M.mem a b
  | _, _, _ => True

def ri_guard_m {n} : Ri_sym → Term n → Term n → Formula 1 n
  | .mid, a, _ | .last, a, _ | .range, a, _ => ri_valid_m a
  | .mem, a, b => .mem a b
  | _, _, _ => .truth

@[simp] theorem ri_guard_closed_l {n} (k : Ri_sym) (a b : Term n)
    (ha : a.freeSupport = []) (hb : b.freeSupport = []) : (ri_guard_m k a b).FreeClosed := by
  cases k <;> simp -implicitDefEqProofs [ri_guard_m, Definitional.Formula.FreeClosed, ha, hb]

theorem ri_guard_delta_l {n} (k : Ri_sym) (a b : Term n) : (ri_guard_m k a b).IsDelta0 := by
  cases k <;> first | exact ri_valid_delta_l _ | exact .mem _ _ | exact .truth

theorem ri_guard_sat_l (hE : Extensional M) {n} (ρ : Env M n) (k : Ri_sym) (a b : Term n) :
    Formula.satisfies ρ (ri_guard_m k a b) ↔ Ri_guard_d k (a.eval ρ) (b.eval ρ) := by
  cases k <;> simp only [ri_guard_m, Ri_guard_d, ri_valid_sat_l hE, Formula.satisfies_mem_iff,
    Formula.satisfies_truth_iff]

def Ri_value_d : Ri_sym → M.Domain → M.Domain → M.Domain → M.Domain → Prop
  | .prod, _, a, b, w => KPair_d M w a b
  | .mid, _, a, b, w => ∃ p q, KPair_d M a p q ∧ Rd_triple_d w p b q
  | .last, _, a, b, w => ∃ p q, KPair_d M a p q ∧ Rd_triple_d w p q b
  | .range, _, a, _, w => ∃ p, KPair_d M a p w
  | .mem, _, a, b, w => M.mem a b ∧ KPair_d M w a b
  | .fibers, x, a, _, w => Rd_fiber_d x a w

def ri_value_m {n} : Ri_sym → Term n → Term n → Term n → Term n → Formula 1 n
  | .prod, _, a, b, w => kpair0_m w a b
  | .mid, _, a, b, w => Formula.existsMem a (Formula.existsMem .newest
      (Formula.existsMem a.weaken.weaken (Formula.existsMem .newest
        (.conj (kpair0_m a.weaken.weaken.weaken.weaken (.bound 2) .newest)
          (rd_triple0_m w.weaken.weaken.weaken.weaken (.bound 2) b.weaken.weaken.weaken.weaken .newest)))))
  | .last, _, a, b, w => Formula.existsMem a (Formula.existsMem .newest
      (Formula.existsMem a.weaken.weaken (Formula.existsMem .newest
        (.conj (kpair0_m a.weaken.weaken.weaken.weaken (.bound 2) .newest)
          (rd_triple0_m w.weaken.weaken.weaken.weaken (.bound 2) .newest b.weaken.weaken.weaken.weaken)))))
  | .range, _, a, _, w => Formula.existsMem a (Formula.existsMem .newest
      (kpair0_m a.weaken.weaken .newest w.weaken.weaken))
  | .mem, _, a, b, w => .conj (.mem a b) (kpair0_m w a b)
  | .fibers, x, a, _, w => rd_fiber0_m x a w

@[simp] theorem ri_value_closed_l {n} (k : Ri_sym) (x a b w : Term n)
    (hx : x.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) (hw : w.freeSupport = []) :
    (ri_value_m k x a b w).FreeClosed := by
  cases k <;> simp -implicitDefEqProofs [ri_value_m, Definitional.Formula.FreeClosed, hx, ha, hb, hw]

theorem ri_value_delta_l {n} (k : Ri_sym) (x a b w : Term n) : (ri_value_m k x a b w).IsDelta0 := by
  cases k
  · exact kpair0_delta_l ..
  · exact .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (rd_triple0_delta_l ..)))))
  · exact .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (rd_triple0_delta_l ..)))))
  · exact .existsMem _ (.existsMem _ (kpair0_delta_l ..))
  · exact .conj (.mem _ _) (kpair0_delta_l ..)
  · exact rd_fiber0_delta_l ..

theorem ri_value_sat_l (hE : Extensional M) {n} (ρ : Env M n) (k : Ri_sym) (x a b w : Term n) :
    Formula.satisfies ρ (ri_value_m k x a b w) ↔ Ri_value_d k (x.eval ρ) (a.eval ρ) (b.eval ρ) (w.eval ρ) := by
  cases k <;> simp only [ri_value_m, Ri_value_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, kpair0_sat_l hE, rd_triple0_sat_l hE,
    rd_fiber0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  · constructor
    · rintro ⟨_, _, p, _, _, _, q, _, h, g⟩; exact ⟨p, q, h, g⟩
    · rintro ⟨p, q, h, g⟩
      obtain ⟨s, hs, hp⟩ := (kpair_union_l M h p).mpr (Or.inl rfl)
      obtain ⟨t, ht, hq⟩ := (kpair_union_l M h q).mpr (Or.inr rfl)
      exact ⟨s, hs, p, hp, t, ht, q, hq, h, g⟩
  · constructor
    · rintro ⟨_, _, p, _, _, _, q, _, h, g⟩; exact ⟨p, q, h, g⟩
    · rintro ⟨p, q, h, g⟩
      obtain ⟨s, hs, hp⟩ := (kpair_union_l M h p).mpr (Or.inl rfl)
      obtain ⟨t, ht, hq⟩ := (kpair_union_l M h q).mpr (Or.inr rfl)
      exact ⟨s, hs, p, hp, t, ht, q, hq, h, g⟩
  · constructor
    · rintro ⟨_, _, p, _, h⟩; exact ⟨p, h⟩
    · rintro ⟨p, h⟩
      obtain ⟨s, hs, hp⟩ := (kpair_union_l M h p).mpr (Or.inl rfl)
      exact ⟨s, hs, p, hp, h⟩

theorem ri_total_l (hKP : M.Models KP) (k : Ri_sym) (x a b : M.Domain)
    (h : Ri_guard_d k a b) : ∃ w, Ri_value_d k x a b w := by
  let I := kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)
  have triple (p q r : M.Domain) : ∃ w, Rd_triple_d w p q r := by
    obtain ⟨s, hs⟩ := I.total q r
    obtain ⟨w, hw⟩ := I.total p s
    exact ⟨w, s, hs, hw⟩
  cases k with
  | prod => exact I.total a b
  | mid => obtain ⟨p, q, hp⟩ := h; exact (triple p b q).imp (fun w hw => ⟨p, q, hp, hw⟩)
  | last => obtain ⟨p, q, hp⟩ := h; exact (triple p q b).imp (fun w hw => ⟨p, q, hp, hw⟩)
  | range => obtain ⟨p, q, hp⟩ := h; exact ⟨q, p, hp⟩
  | mem => exact (I.total a b).imp (fun _ hw => ⟨h, hw⟩)
  | fibers => exact rd_fiber_exists_l hKP x a

theorem ri_unique_l (hE : Extensional M) {k : Ri_sym} {x a b v w : M.Domain}
    (h : Ri_value_d k x a b v) (g : Ri_value_d k x a b w) : v = w := by
  have triple {v w a b c : M.Domain} (h : Rd_triple_d v a b c) (g : Rd_triple_d w a b c) : v = w := by
    obtain ⟨p, hp, hv⟩ := h
    obtain ⟨q, hq, hw⟩ := g
    have he := kpair_unique_l M hE hp hq
    subst q
    exact kpair_unique_l M hE hv hw
  cases k with
  | prod => exact kpair_unique_l M hE h g
  | mid | last =>
    obtain ⟨p, q, hp, hv⟩ := h
    obtain ⟨r, s, hr, hw⟩ := g
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hr
    exact triple hv hw
  | range => obtain ⟨p, hp⟩ := h; obtain ⟨q, hq⟩ := g; exact (kpair_injective_l M hp hq).2
  | mem => exact kpair_unique_l M hE h.2 g.2
  | fibers => exact hE.eq_of_same_members v w (fun t => (h t).trans (g t).symm)

theorem ri_guard_of_value_l {k : Ri_sym} {x a b w : M.Domain} (h : Ri_value_d k x a b w) :
    Ri_guard_d k a b := by
  cases k with
  | prod | fibers => trivial
  | mid | last => exact h.elim fun p hp => hp.elim fun q hq => ⟨p, q, hq.1⟩
  | range => exact h.elim fun p hp => ⟨p, w, hp⟩
  | mem => exact h.1

def Ri_image_d (k : Ri_sym) (x y W : M.Domain) : Prop := ∀ t, M.mem t W ↔
  ∃ a, M.mem a (ri_left_l k x y) ∧ ∃ b, M.mem b (ri_right_l k x y) ∧ Ri_value_d k x a b t

def ri_image_m {n} (k : Ri_sym) (x y W : Term n) : Formula 1 n :=
  .conj (Formula.forallMem W (Formula.existsMem (ri_left_l k x y).weaken
    (Formula.existsMem (ri_right_l k x y).weaken.weaken
      (ri_value_m k x.weaken.weaken.weaken (.bound 1) .newest (.bound 2)))))
    (Formula.forallMem (ri_left_l k x y) (Formula.forallMem (ri_right_l k x y).weaken
      (.imp (ri_guard_m k (.bound 1) .newest) (Formula.existsMem W.weaken.weaken
        (ri_value_m k x.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)))))

@[simp] theorem ri_image_closed_l {n} (k : Ri_sym) (x y W : Term n)
    (hx : x.freeSupport = []) (hy : y.freeSupport = []) (hW : W.freeSupport = []) :
    (ri_image_m k x y W).FreeClosed := by
  have hl : (ri_left_l k x y).freeSupport = [] := by cases k <;> assumption
  have hr : (ri_right_l k x y).freeSupport = [] := by cases k <;> assumption
  simp -implicitDefEqProofs [ri_image_m, Definitional.Formula.FreeClosed, hx, hW, hl, hr]

theorem ri_image_delta_l {n} (k : Ri_sym) (x y W : Term n) : (ri_image_m k x y W).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (ri_value_delta_l ..))))
    (.forallMem _ (.forallMem _ (.imp (ri_guard_delta_l ..) (.existsMem _ (ri_value_delta_l ..)))))

theorem ri_image_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (k : Ri_sym) (x y W : Term n) :
    Formula.satisfies ρ (ri_image_m k x y W) ↔ Ri_image_d k (x.eval ρ) (y.eval ρ) (W.eval ρ) := by
  have hl : (ri_left_l k x y).eval ρ = ri_left_l k (x.eval ρ) (y.eval ρ) := by cases k <;> rfl
  have hr : (ri_right_l k x y).eval ρ = ri_right_l k (x.eval ρ) (y.eval ρ) := by cases k <;> rfl
  simp only [ri_image_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, ri_value_sat_l hKP.1, ri_guard_sat_l hKP.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hl, hr]
  constructor
  · rintro ⟨h, g⟩ t
    refine ⟨h t, fun ⟨a, ha, b, hb, ht⟩ => ?_⟩
    obtain ⟨s, hs, hv⟩ := g a ha b hb (ri_guard_of_value_l ht)
    exact (ri_unique_l hKP.1 hv ht) ▸ hs
  · intro h
    exact ⟨fun t => (h t).mp, fun a ha b hb hg =>
      (ri_total_l hKP k (x.eval ρ) a b hg).elim fun t ht => ⟨t, (h t).mpr ⟨a, ha, b, hb, ht⟩, ht⟩⟩

def ri_symbol_l : Ri_sym → Rd_sym
  | .prod => .prod | .mid => .mid | .last => .last | .range => .range | .mem => .mem | .fibers => .fibers

theorem ri_image_value_l (k : Ri_sym) (x y z W : M.Domain) :
    Ri_image_d k x y W ↔ Rd_fun_d (ri_symbol_l k) x y z W := by
  apply forall_congr'
  intro t
  apply iff_congr Iff.rfl
  cases k
  · exact ⟨fun ⟨a, ha, b, hb, ht⟩ => ⟨a, b, ha, hb, ht⟩,
      fun ⟨a, b, ha, hb, ht⟩ => ⟨a, ha, b, hb, ht⟩⟩
  · exact ⟨fun ⟨p, hp, b, hb, a, c, hq, ht⟩ => ⟨a, b, c, hb, ⟨p, hq, hp⟩, ht⟩,
      fun ⟨a, b, c, hb, ⟨p, hq, hp⟩, ht⟩ => ⟨p, hp, b, hb, a, c, hq, ht⟩⟩
  · exact ⟨fun ⟨p, hp, c, hc, a, b, hq, ht⟩ => ⟨a, b, c, hc, ⟨p, hq, hp⟩, ht⟩,
      fun ⟨a, b, c, hc, ⟨p, hq, hp⟩, ht⟩ => ⟨p, hp, c, hc, a, b, hq, ht⟩⟩
  · exact ⟨fun ⟨p, hp, _, _, a, hq⟩ => ⟨a, p, hq, hp⟩,
      fun ⟨a, p, hq, hp⟩ => ⟨p, hp, p, hp, a, hq⟩⟩
  · exact ⟨fun ⟨a, ha, b, hb, h, ht⟩ => ⟨a, b, ha, hb, h, ht⟩,
      fun ⟨a, b, ha, hb, h, ht⟩ => ⟨a, ha, b, hb, h, ht⟩⟩
  · exact ⟨fun ⟨a, ha, _, _, ht⟩ => ⟨a, ha, ht⟩, fun ⟨a, ha, ht⟩ => ⟨a, ha, a, ha, ht⟩⟩

end YesMetaZFC.SetTheory.InnerModel
