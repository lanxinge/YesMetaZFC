import YesMetaZFC.Model.Forcing.Atomic.Recursion
import YesMetaZFC.Model.Forcing.Boolean.Internal
import YesMetaZFC.SetTheory.Foundation
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # 模型内条件序与外部泛型滤子

泛型性只量化地模型中的集合 D；相对稠密版本直接服务于真值证明。
零元以下没有非零条件，其余部分只需预序，不要求宿主完备代数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SmallGraph
universe u
variable (M : SetTheory.Structure.{u})

structure Cond_order_d (B R z : M.Domain) : Prop where
  refl : ∀ p, M.mem p B → Entry_d M p p R
  trans : ∀ p q r, M.mem p B → M.mem q B → M.mem r B →
    Entry_d M p q R → Entry_d M q r R → Entry_d M p r R
  zero : ∀ p, M.mem p B → Entry_d M p z R → p = z

theorem cond_order_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    {B R z} (h : BooleanZF.Boolean_d (kpair_interpretation_l M hE hP) B R z) :
    Cond_order_d M B R z :=
  ⟨h.order.refl, h.order.trans, fun p hp hz =>
    h.order.antisymm p z hp h.bot_mem hz (h.bot_le p hp)⟩

def Dense_d (B R z : M.Domain) (P : M.Domain → Prop) (p : M.Domain) : Prop :=
  ∀ q, Below_d M B R z q p → ∃ r, Below_d M B R z r q ∧ P r

def Neg_d (B R z : M.Domain) (P : M.Domain → Prop) (p : M.Domain) : Prop :=
  ∀ q, Below_d M B R z q p → ¬ P q

def Lower_d (B R z : M.Domain) (P : M.Domain → Prop) : Prop :=
  ∀ p q, M.mem p B → Below_d M B R z q p → P p → P q

structure Generic_d (B R z : M.Domain) (U : M.Domain → Prop) : Prop where
  proper : ∀ p, U p → M.mem p B ∧ p ≠ z
  inhabited : ∃ p, U p
  upward : ∀ p q, U p → M.mem q B → Entry_d M p q R → U q
  directed : ∀ p q, U p → U q → ∃ r, U r ∧ Entry_d M r p R ∧ Entry_d M r q R
  meets : ∀ p, U p → ∀ D, Dense_d M B R z (fun q => M.mem q D) p →
    ∃ q, U q ∧ M.mem q D

variable {M} {B R z : M.Domain} (O : Cond_order_d M B R z)
include O

theorem below_refl_l {p} (hp : M.mem p B) (hn : p ≠ z) : Below_d M B R z p p :=
  ⟨hp, hn, O.refl p hp⟩

theorem below_trans_l {p q r} (hp : M.mem p B)
    (h : Below_d M B R z r q) (k : Below_d M B R z q p) : Below_d M B R z r p :=
  ⟨h.1, h.2.1, O.trans r q p h.1 k.1 hp h.2.2 k.2.2⟩

theorem dense_lower_l (P : M.Domain → Prop) : Lower_d M B R z (Dense_d M B R z P) :=
  fun _ _ hp hq h r hr => h r (below_trans_l O hp hr hq)

theorem neg_lower_l (P : M.Domain → Prop) : Lower_d M B R z (Neg_d M B R z P) :=
  fun _ _ hp hq h r hr => h r (below_trans_l O hp hr hq)

theorem dense_intro_l {P : M.Domain → Prop} (h : Lower_d M B R z P)
    {p} (hp : M.mem p B) (hP : P p) : Dense_d M B R z P p :=
  fun q hq => ⟨q, below_refl_l O hq.1 hq.2.1, h p q hp hq hP⟩

theorem dense_idem_l {P : M.Domain → Prop} {p}
    (h : Dense_d M B R z (Dense_d M B R z P) p) : Dense_d M B R z P p := by
  intro q hq
  obtain ⟨r, hr, hd⟩ := h q hq
  obtain ⟨s, hs, hP⟩ := hd r (below_refl_l O hr.1 hr.2.1)
  exact ⟨s, below_trans_l O hq.1 hs hr, hP⟩

/-- 原子条件的主滤子给出实际泛型实例：任意模型内稠密集都必须遇到该原子。 -/
theorem generic_atom_l {a} (ha : M.mem a B) (hn : a ≠ z)
    (hA : ∀ q, Below_d M B R z q a → Entry_d M a q R) :
    Generic_d M B R z (fun q => M.mem q B ∧ Entry_d M a q R) where
  proper q hq := ⟨hq.1, fun he => hn (O.zero a ha (he ▸ hq.2))⟩
  inhabited := ⟨a, ha, O.refl a ha⟩
  upward p q hp hq h := ⟨hq, O.trans a p q ha hp.1 hq hp.2 h⟩
  directed p q hp hq := ⟨a, ⟨ha, O.refl a ha⟩, hp.2, hq.2⟩
  meets p hp D hd := by
    obtain ⟨q, hq, hD⟩ := hd a ⟨ha, hn, hp.2⟩
    exact ⟨q, ⟨hq.1, hA q hq⟩, hD⟩

omit O in
/-- 任意内部集合族按反向包含排序；族自身作为排除值。 -/
theorem subset_order_l (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) (B : M.Domain) : ∃ R,
    (∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p) ∧ Cond_order_d M B R B ∧
      (∀ v, M.mem v R → ∃ p q, KPair_d M v p q) := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let φ : BinarySchema 0 := { body := .subset .newest (.bound 1) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => B⟩
  obtain ⟨R, hGraph, hR⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ B
  have hr p q : Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p :=
    (hR p q).trans (and_congr_right fun _ => and_congr_right fun _ =>
      Formula.satisfies_subset_iff ((ρ.push p).push q) .newest (.bound 1))
  refine ⟨R, hr, ?_, hGraph.1⟩
  exact {
    refl := fun p hp => (hr p p).mpr ⟨hp, hp, fun _ h => h⟩
    trans := fun p q r hp _ hr' hpq hqr => (hr p r).mpr
      ⟨hp, hr', fun x hx => ((hr p q).mp hpq).2.2 x (((hr q r).mp hqr).2.2 x hx)⟩
    zero := fun p _ hp => False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) B ((hr p B).mp hp).2.1) }

omit O in
theorem subset_below_l (hZF : M.Models ZF) {B R p q : M.Domain}
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (hp : M.mem p B) (hq : M.mem q B) (h : M.MemberSubset p q) : Below_d M B R B q p :=
  ⟨hq, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hq), (hR q p).mpr ⟨hq, hp, h⟩⟩

/-- 等号力迫在加强条件下保持；证明消费已构造的递归方程。 -/
theorem eq_force_lower_l (hZF : M.Models ZF) {s t}
    (hs : Name_d M B s) (ht : Name_d M B t) :
    Lower_d M B R z (fun p => Eq_force_d M B R z p s t) := by
  intro p q hp hq h
  obtain ⟨_, hl, hr⟩ := (eq_force_unfold_l M hZF hs ht).mp h
  apply (eq_force_unfold_l M hZF hs ht).mpr
  exact ⟨hq.1, fun a b hab r hr' hrb => hl a b hab r (below_trans_l O hp hr' hq) hrb,
    fun a b hab r hr' hrb => hr a b hab r (below_trans_l O hp hr' hq) hrb⟩

/-- 等号力迫为正则真值：在 p 下稠密成立即在 p 成立。 -/
theorem eq_force_dense_l (hZF : M.Models ZF) {s t p}
    (hs : Name_d M B s) (ht : Name_d M B t) (hp : M.mem p B)
    (h : Dense_d M B R z (fun q => Eq_force_d M B R z q s t) p) :
    Eq_force_d M B R z p s t := by
  apply (eq_force_unfold_l M hZF hs ht).mpr
  have hm (k : Bool) {s t} (hs : Name_d M B s)
      (h : ∀ q, Below_d M B R z q p → ∃ r, Below_d M B R z r q ∧ Eq_match_d M k B R z r s t) :
      Eq_match_d M k B R z p s t := by
    intro a b hab q hq hqb
    obtain ⟨r, hr, he⟩ := h q hq
    have hb := (name_entry_l M hs hab).2
    obtain ⟨v, d, c, hv, hd, hvc, he⟩ := he a b hab r (below_refl_l O hr.1 hr.2.1)
      (O.trans r q b hr.1 hq.1 hb hr.2.2 hqb)
    exact ⟨v, d, c, below_trans_l O hq.1 hv hr, hd, hvc, he⟩
  refine ⟨hp, ?_, ?_⟩
  · apply hm false hs
    intro q hq
    obtain ⟨r, hr, he⟩ := h q hq
    exact ⟨r, hr, ((eq_force_unfold_l M hZF hs ht).mp he).2.1⟩
  · apply hm true ht
    intro q hq
    obtain ⟨r, hr, he⟩ := h q hq
    exact ⟨r, hr, ((eq_force_unfold_l M hZF hs ht).mp he).2.2⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 实际公式的可定义条件集与泛型取见证

可定义性证书携带原 UnarySchema、参数环境及逐值语义证明。泛型引理先应用原分离
公理形成模型集合，再消费泛型性；不对任意外部谓词假定模型内分离。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Defined_d (P : M.Domain → Prop) : Prop :=
  ∃ n, ∃ φ : UnarySchema n, ∃ ρ : Env M n, ∀ p, φ.denote ρ p ↔ P p

def neg_pred_m {k n} (φ : UnarySchema k) (e : Fin k → Term n) (B R z p : Term n) : Formula 1 n :=
  .forallE (.imp (below_m B.weaken R.weaken z.weaken .newest p.weaken)
    (.neg (pred_m φ (fun i => (e i).weaken) .newest)))

@[simp] theorem neg_pred_m_freeClosed {k n} (φ : UnarySchema k) (e : Fin k → Term n)
    (B R z p : Term n) (he : ∀ i, (e i).freeSupport = [])
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hp : p.freeSupport = []) : (neg_pred_m φ e B R z p).FreeClosed := by
  simp -implicitDefEqProofs [neg_pred_m, Definitional.Formula.FreeClosed, *]

theorem neg_pred_sat_l (hE : Extensional M) {k n} (φ : UnarySchema k) (ρ : Env M n)
    (e : Fin k → Term n) (B R z p : Term n) :
    Formula.satisfies ρ (neg_pred_m φ e B R z p) ↔
      Neg_d M (B.eval ρ) (R.eval ρ) (z.eval ρ)
        (φ.denote (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k)) (p.eval ρ) := by
  simp only [neg_pred_m, Neg_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, below_sat_l M hE, pred_sat_l M,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  rfl

theorem defined_set_l (hZF : M.Models ZF) {P : M.Domain → Prop} (h : Defined_d M P) (B : M.Domain) :
    ∃ D, ∀ p, M.mem p D ↔ M.mem p B ∧ P p := by
  obtain ⟨n, φ, ρ, hφ⟩ := h
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ B
  exact ⟨D, fun p => (hD p).trans (and_congr_right fun _ => hφ p)⟩

/-- 判定集使用同一正文与其加强否定，三项条件参数显式加入原参数环境。 -/
theorem defined_decide_l (hE : Extensional M) {P : M.Domain → Prop}
    (h : Defined_d M P) (B R z : M.Domain) :
    Defined_d M (fun p => P p ∨ Neg_d M B R z P p) := by
  obtain ⟨n, φ, ρ, hφ⟩ := h
  let e : Fin n → Term (n + 4) := fun i => .bound ⟨i.val + 4, by omega⟩
  let ψ : UnarySchema (n + 3) := {
    body := .disj (pred_m φ e (.bound 0))
      (neg_pred_m φ e (.bound 3) (.bound 2) (.bound 1) (.bound 0))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, e] }
  let η := ((ρ.push B).push R).push z
  refine ⟨n + 3, ψ, η, fun p => ?_⟩
  have he : (⟨fun i => (e i).eval (η.push p), (η.push p).free⟩ : Env M n) = ρ := by
    cases ρ; rfl
  simp only [UnarySchema.denote, ψ, Formula.satisfies_disj_iff, pred_sat_l M,
    neg_pred_sat_l M hE, he]
  change (φ.denote ρ p ∨ Neg_d M B R z (φ.denote ρ) p) ↔ _
  exact or_congr (hφ p) (forall_congr' fun q => imp_congr_right fun _ => not_congr (hφ q))

theorem eq_force_defined_l (hE : Extensional M) (B R z s t : M.Domain) :
    Defined_d M (fun p => Eq_force_d M B R z p s t) := by
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push s).push t
  let φ : UnarySchema 5 :=
    { body := eq_force_m (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1) }
  exact ⟨5, φ, ρ, fun p => eq_force_sat_l M hE (ρ.push p)
    (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1)⟩

theorem mem_force_defined_l (hE : Extensional M) (B R z s t : M.Domain) :
    Defined_d M (fun p => Mem_force_d M B R z p s t) := by
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push s).push t
  let φ : UnarySchema 5 :=
    { body := mem_force_m (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1) }
  exact ⟨5, φ, ρ, fun p => mem_force_sat_l M hE (ρ.push p)
    (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1)⟩

variable {M} {B R z : M.Domain} {U : M.Domain → Prop}

theorem generic_pick_l (hZF : M.Models ZF) (hU : Generic_d M B R z U)
    {P : M.Domain → Prop} (hP : Defined_d M P) {p} (hp : U p)
    (hd : Dense_d M B R z P p) : ∃ q, U q ∧ P q := by
  obtain ⟨D, hD⟩ := defined_set_l M hZF hP B
  obtain ⟨q, hq, hqD⟩ := hU.meets p hp D (fun q hq => by
    obtain ⟨r, hr, hP⟩ := hd q hq
    exact ⟨r, hr, (hD r).mpr ⟨hr.1, hP⟩⟩)
  exact ⟨q, hq, ((hD q).mp hqD).2⟩

theorem generic_decide_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (hU : Generic_d M B R z U) {P : M.Domain → Prop} (hP : Defined_d M P) :
    (∃ p, U p ∧ P p) ∨ (∃ p, U p ∧ Neg_d M B R z P p) := by
  classical
  obtain ⟨p, hp⟩ := hU.inhabited
  obtain ⟨q, hq, hd⟩ := generic_pick_l hZF hU (defined_decide_l M hZF.1 hP B R z) hp (by
    intro q hq
    by_cases h : ∃ r, Below_d M B R z r q ∧ P r
    · obtain ⟨r, hr, hP⟩ := h
      exact ⟨r, hr, Or.inl hP⟩
    · exact ⟨q, below_refl_l O hq.1 hq.2.1, Or.inr (fun r hr hP => h ⟨r, hr, hP⟩)⟩)
  exact hd.elim (fun h => Or.inl ⟨q, hq, h⟩) (fun h => Or.inr ⟨q, hq, h⟩)

theorem generic_neg_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (hU : Generic_d M B R z U) {P : M.Domain → Prop}
    (hP : Defined_d M P) (hl : Lower_d M B R z P) :
    (∃ p, U p ∧ Neg_d M B R z P p) ↔ ¬ ∃ p, U p ∧ P p := by
  constructor
  · rintro ⟨p, hp, hn⟩ ⟨q, hq, hP⟩
    obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
    have hr' := hU.proper r hr
    exact hn r ⟨hr'.1, hr'.2, hrp⟩ (hl q r (hU.proper q hq).1 ⟨hr'.1, hr'.2, hrq⟩ hP)
  · intro h
    exact (generic_decide_l O hZF hU hP).elim (fun k => False.elim (h k)) id

end YesMetaZFC.Model.Forcing.Internal
