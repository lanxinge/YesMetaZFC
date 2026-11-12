import YesMetaZFC.Model.Forcing.Names.PairConstruction

/-! # 不依赖泛型选择的内部力迫规则

迭代的序关系必须在地模型中先行构造。这里直接从内部翻译证明代入、正则性
及蕴涵消去，不借助可数性或外部泛型存在性反推力迫关系。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem code_conj_l {n} (C D : Formula 1 (n + 4)) (ρ : Env M n) (p : M.Domain) :
    Code_d M B R z (.conj C D) ρ p ↔ Code_d M B R z C ρ p ∧ Code_d M B R z D ρ p := Formula.satisfies_conj_iff _ C D

theorem forces_mem_l (hE : Extensional M) {a n} (s t : Term n) (ρ : Env M n) (p : M.Domain) :
    Forces_d M B R z (.mem s t : Formula a n) ρ p ↔ Mem_force_d M B R z p (s.eval ρ) (t.eval ρ) :=
  code_mem_l M hE B R z s t ρ p

theorem forces_neg_l (hE : Extensional M) {a n} (φ : Formula a n) (ρ : Env M n) (p : M.Domain) :
    Forces_d M B R z (.neg φ) ρ p ↔ Neg_d M B R z (Forces_d M B R z φ ρ) p :=
  code_neg_l M hE B R z _ ρ p

theorem forces_conj_l {a n} (φ ψ : Formula a n) (ρ : Env M n) (p : M.Domain) :
    Forces_d M B R z (.conj φ ψ) ρ p ↔ Forces_d M B R z φ ρ p ∧ Forces_d M B R z ψ ρ p := code_conj_l _ _ ρ p

theorem forces_imp_l (hE : Extensional M) {a n} (φ ψ : Formula a n) (ρ : Env M n) (p : M.Domain) :
    Forces_d M B R z (.imp φ ψ) ρ p ↔
      Neg_d M B R z (fun q => Forces_d M B R z φ ρ q ∧ Neg_d M B R z (Forces_d M B R z ψ ρ) q) p := by
  simp only [Forces_d, force_code_m, imp_code_m, code_neg_l M hE, Neg_d, code_conj_l]

theorem forces_all_l (hE : Extensional M) {a n} (φ : Formula a (n + 1)) (ρ : Env M n) (p : M.Domain) :
    Forces_d M B R z (.forallE φ) ρ p ↔ ∀ t, Name_d M B t → Forces_d M B R z φ (ρ.push t) p :=
  code_all_l M hE B R z _ ρ p

theorem forces_disj_l {a n} (φ ψ : Formula a n) (ρ : Env M n) (p : M.Domain) :
    Forces_d M B R z (.disj φ ψ) ρ p ↔ Forces_d M B R z (.neg (.conj (.neg φ) (.neg ψ))) ρ p := Iff.rfl

theorem forces_iff_l {a n} (φ ψ : Formula a n) (ρ : Env M n) (p : M.Domain) :
    Forces_d M B R z (.iff φ ψ) ρ p ↔ Forces_d M B R z (.conj (.imp φ ψ) (.imp ψ φ)) ρ p := Iff.rfl

theorem forces_exists_l {a n} (φ : Formula a (n + 1)) (ρ : Env M n) (p : M.Domain) :
    Forces_d M B R z (.existsE φ) ρ p ↔ Forces_d M B R z (.neg (.forallE (.neg φ))) ρ p := Iff.rfl

/-- 存在引入只消费给定名称见证的向下闭性。 -/
theorem forces_exists_intro_l (O : Cond_order_d M B R z) (hE : Extensional M) {a n}
    {φ : Formula a (n + 1)} {ρ : Env M n} {p t} (ht : Name_d M B t)
    (hLower : Lower_d M B R z (Forces_d M B R z φ (ρ.push t)))
    (hp : M.mem p B) (hφ : Forces_d M B R z φ (ρ.push t) p) :
    Forces_d M B R z (.existsE φ) ρ p := by
  rw [forces_exists_l, forces_neg_l hE]
  intro q hq hn
  have hn := (forces_all_l hE _ _ q).mp hn t ht
  exact (forces_neg_l hE _ _ q).mp hn q (below_refl_l O hq.1 hq.2.1)
    (hLower p q hp hq hφ)

/-- 存在力迫的见证在条件以下稠密出现，不预设最大值原理或名称选择函数。 -/
theorem forces_exists_dense_l (hE : Extensional M) {a n} {φ : Formula a (n + 1)} {ρ : Env M n} {p}
    (h : Forces_d M B R z (.existsE φ) ρ p) :
    Dense_d M B R z (fun q => ∃ t, Name_d M B t ∧ Forces_d M B R z φ (ρ.push t) q) p := by
  rw [forces_exists_l, forces_neg_l hE] at h
  intro q hq
  apply Classical.byContradiction
  intro hn
  apply h q hq
  rw [forces_all_l hE]
  intro t ht
  rw [forces_neg_l hE]
  exact fun r hr hφ => hn ⟨r, hr, t, ht, hφ⟩

/-- 任意有限变量代入与力迫翻译交换；参数仍使用原公式与原环境。 -/
theorem forces_bind_l (hE : Extensional M) {a n} (φ : Formula a n) {m}
    (e : Fin n → Term m) (ρ : Env M m) (p : M.Domain) :
    Forces_d M B R z (φ.bind e) ρ p ↔ Forces_d M B R z φ (Definitional.Env.substitute ρ e) p := by
  induction φ generalizing m p with
  | falsum => simp only [Forces_d, Definitional.Formula.bind, force_code_m, Code_d, Formula.satisfies_falsum_iff]
  | truth => simp only [Forces_d, Definitional.Formula.bind, force_code_m, Code_d, Formula.satisfies_truth_iff]
  | mem s t =>
    simp only [Definitional.Formula.bind, Forces_d, force_code_m, code_mem_l M hE, Definitional.Term.eval_bind]
  | atom r h ts =>
    cases r
    · simp only [Definitional.Formula.bind, Forces_d, force_code_m, code_eq_l M hE,
        Definitional.TermVector.get_bind, Definitional.Term.eval_bind]
    · simp only [Definitional.Formula.bind, Forces_d, force_code_m, code_all_l M hE,
        imp_code_m, code_neg_l M hE, Neg_d, code_conj_l, code_mem_l M hE,
        Definitional.TermVector.get_bind, Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
        Definitional.Term.eval_bind]
  | neg φ ih =>
    simp only [Definitional.Formula.bind, forces_neg_l hE, Neg_d, ih]
  | conj φ ψ ih jh =>
    simp only [Definitional.Formula.bind, forces_conj_l, ih, jh]
  | disj φ ψ ih jh =>
    simp only [Definitional.Formula.bind, forces_disj_l, forces_neg_l hE, forces_conj_l, Neg_d, ih, jh]
  | imp φ ψ ih jh =>
    simp only [Definitional.Formula.bind, forces_imp_l hE, Neg_d, ih, jh]
  | iff φ ψ ih jh =>
    simp only [Definitional.Formula.bind, forces_iff_l, forces_conj_l, forces_imp_l hE, Neg_d, ih, jh]
  | forallE φ ih =>
    simp only [Definitional.Formula.bind, forces_all_l hE, ih, Definitional.Semantics.substitute_lift]
  | existsE φ ih =>
    simp only [Definitional.Formula.bind, forces_exists_l, forces_neg_l hE, forces_all_l hE,
      Neg_d, ih, Definitional.Semantics.substitute_lift]

/-- 有限参数 schema 的实际实例化与力迫翻译交换。 -/
theorem forces_pred_l (hE : Extensional M) {k n} (φ : UnarySchema k) (ρ : Env M n)
    (e : Fin k → Term n) (s : Term n) (p : M.Domain) :
    Forces_d M B R z (pred_m φ e s) ρ p ↔
      Forces_d M B R z φ.body ((⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k).push (s.eval ρ)) p := by
  rw [pred_m, forces_bind_l hE]
  have he : Definitional.Env.substitute ρ (Fin.cases s e) =
      (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k).push (s.eval ρ) := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩
  rw [he]

/-- 自由闭合公式只依赖有限参数，不依赖默认自由赋值。 -/
theorem forces_env_l (hE : Extensional M) {a n} (φ : Formula a n) (hφ : φ.FreeClosed)
    (ρ η : Env M n) (he : ∀ i, ρ.bound i = η.bound i) (p : M.Domain) :
    Forces_d M B R z φ ρ p ↔ Forces_d M B R z φ η p := by
  have ht {n} {ρ η : Env M n} (h : ∀ i, ρ.bound i = η.bound i) (t : Term n)
      (hc : t.freeSupport = []) : t.eval ρ = t.eval η := by
    cases t with
    | free _ => simp at hc
    | bound i => exact h i
  have hp {n} {ρ η : Env M n} (h : ∀ i, ρ.bound i = η.bound i) (s : M.Domain) :
      ∀ i, (ρ.push s).bound i = (η.push s).bound i := Fin.cases rfl h
  induction φ generalizing p <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum => simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_falsum_iff]
  case truth => simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_truth_iff]
  case mem s t =>
    simp only [Forces_d, force_code_m, code_mem_l M hE, ht he s hφ.1, ht he t hφ.2]
  case atom r _ ts =>
    cases r
    · simp only [Forces_d, force_code_m, code_eq_l M hE, ht he (ts 0) (hφ 0), ht he (ts 1) (hφ 1)]
    · simp only [Forces_d, force_code_m, code_all_l M hE, imp_code_m, code_neg_l M hE, Neg_d,
        code_conj_l, code_mem_l M hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
        ht he (ts 0) (hφ 0), ht he (ts 1) (hφ 1)]
  case neg φ ih => simp only [forces_neg_l hE, Neg_d, ih hφ ρ η he]
  case conj φ ψ ih jh => simp only [forces_conj_l, ih hφ.1 ρ η he, jh hφ.2 ρ η he]
  case disj φ ψ ih jh =>
    simp only [forces_disj_l, forces_neg_l hE, forces_conj_l, Neg_d, ih hφ.1 ρ η he, jh hφ.2 ρ η he]
  case imp φ ψ ih jh => simp only [forces_imp_l hE, Neg_d, ih hφ.1 ρ η he, jh hφ.2 ρ η he]
  case iff φ ψ ih jh =>
    simp only [forces_iff_l, forces_conj_l, forces_imp_l hE, Neg_d, ih hφ.1 ρ η he, jh hφ.2 ρ η he]
  case forallE φ ih =>
    simp only [forces_all_l hE]
    exact forall_congr' fun s => imp_congr_right fun _ => ih hφ _ _ (hp he s) p
  case existsE φ ih =>
    simp only [forces_exists_l, forces_neg_l hE, forces_all_l hE, Neg_d]
    exact forall_congr' fun q => imp_congr_right fun _ => not_congr (forall_congr' fun s =>
      imp_congr_right fun _ => forall_congr' fun r => imp_congr_right fun _ => not_congr (ih hφ _ _ (hp he s) r))

private theorem regular_all_l {P : M.Domain → M.Domain → Prop}
    (h : ∀ t, Name_d M B t → Regular_d M B R z (P t)) :
    Regular_d M B R z (fun p => ∀ t, Name_d M B t → P t p) :=
  ⟨fun p q hp hq hP t ht => (h t ht).1 p q hp hq (hP t ht),
    fun p hp hn hd t ht => (h t ht).2 p hp hn (fun q hq =>
      (hd q hq).elim fun r hr => ⟨r, hr.1, hr.2 t ht⟩)⟩

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

/-- 任意名称赋值的力迫真值为正则向下闭集，不要求已有泛型。 -/
theorem forces_regular_l {a n} (φ : Formula a n) (ρ : Env M n)
    (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) : Regular_d M B R z (Forces_d M B R z φ ρ) := by
  have hn {P : M.Domain → Prop} (h : Regular_d M B R z P) := regular_neg_l O h.1
  have ha {n} {ρ : Env M n} (hρ : ∀ t : Term n, Name_d M B (t.eval ρ))
      {s} (hs : Name_d M B s) : ∀ t : Term (n + 1), Name_d M B (t.eval (ρ.push s)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i
  induction φ with
  | falsum =>
    simp only [Regular_d, Lower_d, Dense_d, Forces_d, force_code_m, Code_d, Formula.satisfies_falsum_iff]
    refine ⟨fun _ _ _ _ h => h, fun p hp hz hd => ?_⟩
    exact (hd p (below_refl_l O hp hz)).elim fun _ h => h.2
  | truth =>
    simp only [Regular_d, Lower_d, Dense_d, Forces_d, force_code_m, Code_d, Formula.satisfies_truth_iff]
    exact ⟨fun _ _ _ _ h => h, fun _ _ _ _ => trivial⟩
  | mem s t =>
    simpa only [Regular_d, Lower_d, Dense_d, Neg_d, Forces_d, force_code_m, code_mem_l M hZF.1] using regular_mem_l O (s.eval ρ) (t.eval ρ)
  | atom r _ ts =>
    cases r
    · simpa only [Regular_d, Lower_d, Dense_d, Neg_d, Forces_d, force_code_m, code_eq_l M hZF.1] using
        regular_eq_l O hZF (hρ (ts 0)) (hρ (ts 1))
    · simp only [Regular_d, Lower_d, Dense_d, Neg_d, Forces_d, force_code_m, code_all_l M hZF.1, imp_code_m, code_neg_l M hZF.1,
        code_conj_l, code_mem_l M hZF.1, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
      exact regular_all_l (fun t _ => hn (regular_conj_l (regular_mem_l O t _) (hn (regular_mem_l O t _))))
  | neg φ ih =>
    simpa only [Regular_d, Lower_d, Dense_d, Neg_d, forces_neg_l hZF.1] using hn (ih ρ hρ)
  | conj φ ψ ih jh =>
    simpa only [Regular_d, Lower_d, Dense_d, Neg_d, forces_conj_l] using regular_conj_l (ih ρ hρ) (jh ρ hρ)
  | disj φ ψ ih jh =>
    simpa only [Regular_d, Lower_d, Dense_d, Neg_d, forces_disj_l, forces_neg_l hZF.1, forces_conj_l] using hn (regular_conj_l (hn (ih ρ hρ)) (hn (jh ρ hρ)))
  | imp φ ψ ih jh =>
    simpa only [Regular_d, Lower_d, Dense_d, Neg_d, forces_imp_l hZF.1] using hn (regular_conj_l (ih ρ hρ) (hn (jh ρ hρ)))
  | iff φ ψ ih jh =>
    simpa only [Regular_d, Lower_d, Dense_d, Neg_d, forces_iff_l, forces_conj_l, forces_imp_l hZF.1] using
      regular_conj_l (hn (regular_conj_l (ih ρ hρ) (hn (jh ρ hρ)))) (hn (regular_conj_l (jh ρ hρ) (hn (ih ρ hρ))))
  | forallE φ ih =>
    simpa only [Regular_d, Lower_d, Dense_d, Neg_d, forces_all_l hZF.1] using regular_all_l (fun t ht => ih (ρ.push t) (ha hρ ht))
  | existsE φ ih =>
    simpa only [Regular_d, Lower_d, Dense_d, Neg_d, forces_exists_l, forces_neg_l hZF.1, forces_all_l hZF.1] using
      hn (regular_all_l (fun t ht => hn (ih (ρ.push t) (ha hρ ht))))

omit O hZF in
/-- 正则后件的局部蕴涵消去；前件只需向下闭性。 -/
theorem forces_mp_l (hE : Extensional M) {a n} {φ ψ : Formula a n} {ρ : Env M n} {p}
    (hφ : Lower_d M B R z (Forces_d M B R z φ ρ))
    (hψ : Regular_d M B R z (Forces_d M B R z ψ ρ))
    (hp : M.mem p B) (hz : p ≠ z)
    (h : Forces_d M B R z (.imp φ ψ) ρ p) (k : Forces_d M B R z φ ρ p) :
    Forces_d M B R z ψ ρ p := by
  apply hψ.2 p hp hz
  intro q hq
  classical
  apply Classical.byContradiction
  intro hn
  apply (forces_imp_l hE φ ψ ρ p).mp h q hq
  exact ⟨hφ p q hp hq k, fun r hr hψ => hn ⟨r, hr, hψ⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 局部等号替换与有界存在见证

先在一个条件以下逐公式证明等同名称的替换，再把存在见证移入目标名称的
内部闭支撑。这一步使二步迭代的稠密集证明保持为地模型中的集合论证明。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

private theorem mem_congr_l {p s t a b} (hs : Name_d M B s) (ht : Name_d M B t)
    (ha : Name_d M B a) (hb : Name_d M B b)
    (h : Eq_force_d M B R z p s a) (k : Eq_force_d M B R z p t b) :
    Mem_force_d M B R z p s t ↔ Mem_force_d M B R z p a b :=
  ⟨fun hm => mem_force_right_l O hZF ha ht hb k (mem_force_left_l O hZF hs ha ht h hm),
    fun hm => mem_force_right_l O hZF hs hb ht (eq_force_symm_l hZF ht hb k)
      (mem_force_left_l O hZF ha hs hb (eq_force_symm_l hZF hs ha h) hm)⟩

private theorem eq_congr_l {p s t a b} (hs : Name_d M B s) (ht : Name_d M B t)
    (ha : Name_d M B a) (hb : Name_d M B b)
    (h : Eq_force_d M B R z p s a) (k : Eq_force_d M B R z p t b) :
    Eq_force_d M B R z p s t ↔ Eq_force_d M B R z p a b :=
  ⟨fun he => eq_force_trans_l O hZF ha hs hb (eq_force_symm_l hZF hs ha h)
      (eq_force_trans_l O hZF hs ht hb he k),
    fun he => eq_force_trans_l O hZF hs ha ht h
      (eq_force_trans_l O hZF ha hb ht he (eq_force_symm_l hZF ht hb k))⟩

/-- 在 p 下，逐参数等号力迫允许替换任意原公式的名称赋值。 -/
theorem forces_congr_below_l {a n p} (φ : Formula a n) (ρ η : Env M n)
    (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) (hη : ∀ t : Term n, Name_d M B (t.eval η))
    (hp : M.mem p B) (he : ∀ t : Term n, Eq_force_d M B R z p (t.eval ρ) (t.eval η)) :
    ∀ q, Below_d M B R z q p → (Forces_d M B R z φ ρ q ↔ Forces_d M B R z φ η q) := by
  have hn {P Q : M.Domain → Prop} (h : ∀ q, Below_d M B R z q p → (P q ↔ Q q)) :
      ∀ q, Below_d M B R z q p → (Neg_d M B R z P q ↔ Neg_d M B R z Q q) :=
    fun q hq => forall_congr' fun r => imp_congr_right fun hr => not_congr (h r (below_trans_l O hp hr hq))
  have hc {P Q V W : M.Domain → Prop}
      (h : ∀ q, Below_d M B R z q p → (P q ↔ Q q))
      (k : ∀ q, Below_d M B R z q p → (V q ↔ W q)) :=
    fun q hq => and_congr (h q hq) (k q hq)
  have push {n} {ρ : Env M n} (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) {s} (hs : Name_d M B s) :
      ∀ t : Term (n+1), Name_d M B (t.eval (ρ.push s)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i
  induction φ with
  | falsum => intro q _; simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_falsum_iff]
  | truth => intro q _; simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_truth_iff]
  | mem s t =>
    intro q hq
    rw [forces_mem_l hZF.1, forces_mem_l hZF.1]
    exact mem_congr_l O hZF (hρ s) (hρ t) (hη s) (hη t)
      (eq_force_lower_l O hZF (hρ s) (hη s) p q hp hq (he s))
      (eq_force_lower_l O hZF (hρ t) (hη t) p q hp hq (he t))
  | atom r _ ts =>
    cases r
    · intro q hq
      simp only [Forces_d, force_code_m, code_eq_l M hZF.1]
      exact eq_congr_l O hZF (hρ (ts 0)) (hρ (ts 1)) (hη (ts 0)) (hη (ts 1))
        (eq_force_lower_l O hZF (hρ (ts 0)) (hη (ts 0)) p q hp hq (he (ts 0)))
        (eq_force_lower_l O hZF (hρ (ts 1)) (hη (ts 1)) p q hp hq (he (ts 1)))
    · intro q hq
      simp only [Forces_d, force_code_m, code_all_l M hZF.1, imp_code_m, code_neg_l M hZF.1,
        Neg_d, code_conj_l, code_mem_l M hZF.1, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
      apply forall_congr'
      intro s
      apply imp_congr_right
      intro hs
      have hm (t : Term _) (r : M.Domain) (hr : Below_d M B R z r p) :=
        mem_congr_l O hZF hs (hρ t) hs (hη t) (eq_force_refl_l O hZF hr.1 hs)
          (eq_force_lower_l O hZF (hρ t) (hη t) p r hp hr (he t))
      simpa only [Neg_d] using hn (hc (hm (ts 0)) (hn (hm (ts 1)))) q hq
  | neg φ ih =>
    simpa only [forces_neg_l hZF.1] using hn (ih ρ η hρ hη he)
  | conj φ ψ ih jh =>
    simpa only [forces_conj_l] using hc (ih ρ η hρ hη he) (jh ρ η hρ hη he)
  | disj φ ψ ih jh =>
    simpa only [forces_disj_l, forces_neg_l hZF.1, forces_conj_l, Neg_d] using
      hn (hc (hn (ih ρ η hρ hη he)) (hn (jh ρ η hρ hη he)))
  | imp φ ψ ih jh =>
    simpa only [forces_imp_l hZF.1, Neg_d] using hn (hc (ih ρ η hρ hη he) (hn (jh ρ η hρ hη he)))
  | iff φ ψ ih jh =>
    simpa only [forces_iff_l, forces_conj_l, forces_imp_l hZF.1, Neg_d] using
      hc (hn (hc (ih ρ η hρ hη he) (hn (jh ρ η hρ hη he))))
        (hn (hc (jh ρ η hρ hη he) (hn (ih ρ η hρ hη he))))
  | forallE φ ih =>
    intro q hq
    rw [forces_all_l hZF.1, forces_all_l hZF.1]
    refine forall_congr' fun s => imp_congr_right fun hs => ih (ρ.push s) (η.push s) (push hρ hs) (push hη hs) ?_ q hq
    intro t
    cases t with
    | free i => exact he (.free i)
    | bound i => exact Fin.cases (eq_force_refl_l O hZF hp hs) (fun i => he (.bound i)) i
  | existsE φ ih =>
    have hall : ∀ q, Below_d M B R z q p →
        ((∀ s, Name_d M B s → Neg_d M B R z (Forces_d M B R z φ (ρ.push s)) q) ↔
          ∀ s, Name_d M B s → Neg_d M B R z (Forces_d M B R z φ (η.push s)) q) := by
      intro q hq
      refine forall_congr' fun s => imp_congr_right fun hs => ?_
      apply hn (ih (ρ.push s) (η.push s) (push hρ hs) (push hη hs) ?_) q hq
      intro t
      cases t with
      | free i => exact he (.free i)
      | bound i => exact Fin.cases (eq_force_refl_l O hZF hp hs) (fun i => he (.bound i)) i
    simpa only [forces_exists_l, forces_neg_l hZF.1, forces_all_l hZF.1, Neg_d] using hn hall

/-- 隶属于 A 的任意名称见证可在加强后改用 A 的内部支撑中的代表。 -/
theorem bounded_witness_l {a n} (φ : Formula a (n + 1)) (ρ : Env M n)
    (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) {W A p t}
    (hA : M.mem A W) (hW : Supp_d M B W) (ht : Name_d M B t)
    (hm : Mem_force_d M B R z p t A) (hφ : Forces_d M B R z φ (ρ.push t) p) :
    Dense_d M B R z (fun q => ∃ s, M.mem s W ∧ Mem_force_d M B R z q s A ∧
      Forces_d M B R z φ (ρ.push s) q) p := by
  have push {s} (hs : Name_d M B s) : ∀ t : Term (n+1), Name_d M B (t.eval (ρ.push s)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i
  intro q hq
  obtain ⟨r, s, b, hr, hsA, hrb, he⟩ := hm.2 q hq
  obtain ⟨hsW, hb⟩ := supp_entry_l M hW hA hsA
  have hs : Name_d M B s := ⟨W, hsW, hW⟩
  have hφr := (forces_regular_l O hZF φ _ (push ht)).1 p r hm.1 (below_trans_l O hm.1 hr hq) hφ
  have hc := forces_congr_below_l O hZF φ (ρ.push t) (ρ.push s) (push ht) (push hs) hr.1
    (fun v => by
      cases v with
      | free i => exact eq_force_refl_l O hZF hr.1 (hρ (.free i))
      | bound i => exact Fin.cases he (fun i => eq_force_refl_l O hZF hr.1 (hρ (.bound i))) i)
  exact ⟨r, hr, s, hsW, mem_force_entry_l O hZF hr.1 hs hb hsA hrb,
    (hc r (below_refl_l O hr.1 hr.2.1)).mp hφr⟩

/-- 固定有限参数时，在原公式中替换一个被迫相等的名称；自由默认值无需名称假设。 -/
theorem forces_name_congr_l {n p s t} (φ : UnarySchema n) (ρ : Env M n)
    (hρ : ∀ i, Name_d M B (ρ.bound i)) (hs : Name_d M B s) (ht : Name_d M B t)
    (hp : M.mem p B) (hz : p ≠ z) (he : Eq_force_d M B R z p s t) :
    Forces_d M B R z φ.body (ρ.push s) p ↔ Forces_d M B R z φ.body (ρ.push t) p := by
  let η : Env M n := ⟨ρ.bound, fun _ => s⟩
  have push a (ha : Name_d M B a) : ∀ v : Term (n+1), Name_d M B (v.eval (η.push a)) := by
    intro v
    cases v with
    | free _ => exact hs
    | bound i => exact Fin.cases ha hρ i
  have hc := forces_congr_below_l O hZF φ.body (η.push s) (η.push t) (push s hs) (push t ht) hp (by
    intro v
    cases v with
    | free _ => exact eq_force_refl_l O hZF hp hs
    | bound i => exact Fin.cases he (fun i => eq_force_refl_l O hZF hp (hρ i)) i)
  exact (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push s) (η.push s) (fun _ => rfl) p).trans
    ((hc p (below_refl_l O hp hz)).trans
      (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push t) (η.push t) (fun _ => rfl) p).symm)

/-- 有界存在公式的全部见证密度由模型内名称支撑自动提供。 -/
theorem bounded_exists_l {a n} (φ : Formula a (n + 1)) (ρ : Env M n) (t : Term n)
    (hρ : ∀ v : Term n, Name_d M B (v.eval ρ)) {W p}
    (hW : Supp_d M B W) (ht : M.mem (t.eval ρ) W)
    (h : Forces_d M B R z (.existsE (.conj (.mem .newest t.weaken) φ)) ρ p) :
    Dense_d M B R z (fun q => ∃ s, M.mem s W ∧ Mem_force_d M B R z q s (t.eval ρ) ∧
      Forces_d M B R z φ (ρ.push s) q) p := by
  intro q hq
  obtain ⟨r, hr, s, hs, h⟩ := forces_exists_dense_l hZF.1 h q hq
  obtain ⟨hm, hφ⟩ := (forces_conj_l _ _ _ r).mp h
  have hm : Mem_force_d M B R z r s (t.eval ρ) := by
    simpa only [Definitional.Term.eval_newest, Definitional.Term.eval_weaken] using
      (forces_mem_l hZF.1 _ _ _ r).mp hm
  obtain ⟨v, hv, hw⟩ := bounded_witness_l O hZF φ ρ hρ ht hW hs hm hφ r (below_refl_l O hr.1 hr.2.1)
  exact ⟨v, below_trans_l O hq.1 hv hr, hw⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 条件域上的序关系决定全部名称力迫

域外条目不参与闭名称的带条件双模拟。先在共同闭支撑上搬运实际双模拟集合，
再由原公式归纳传递全部连接词和名称量词；不要求域外关系满足序律。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R S z : M.Domain}
variable (hR : ∀ p q, M.mem p B → M.mem q B → (Entry_d M p q R ↔ Entry_d M p q S))
include hR

theorem below_order_l {p q} (hp : M.mem p B) :
    Below_d M B R z q p ↔ Below_d M B S z q p :=
  and_congr_right fun hq => and_congr_right fun _ => hR q p hq hp

/-- 泛型性只依赖条件域内的关系边，两个方向均无需集合论公理。 -/
theorem generic_order_l (U : M.Domain → Prop) : Generic_d M B R z U ↔ Generic_d M B S z U := by
  have tr {R S} (hR : ∀ p q, M.mem p B → M.mem q B → (Entry_d M p q R ↔ Entry_d M p q S))
      (hU : Generic_d M B R z U) : Generic_d M B S z U := by
    refine ⟨hU.proper, hU.inhabited, ?_, ?_, ?_⟩
    · intro p q hp hq hpq
      exact hU.upward p q hp hq ((hR p q (hU.proper p hp).1 hq).mpr hpq)
    · intro p q hp hq
      obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
      exact ⟨r, hr, (hR r p (hU.proper r hr).1 (hU.proper p hp).1).mp hrp,
        (hR r q (hU.proper r hr).1 (hU.proper q hq).1).mp hrq⟩
    · intro p hp D hd
      apply hU.meets p hp D
      intro q hq
      obtain ⟨r, hr, hrD⟩ := hd q ((below_order_l hR (hU.proper p hp).1).mp hq)
      exact ⟨r, (below_order_l hR hq.1).mpr hr, hrD⟩
  exact ⟨tr hR, tr (fun p q hp hq => (hR p q hp hq).symm)⟩

variable (hZF : M.Models ZF)
include hZF

/-- 闭支撑上的最大双模拟可沿逐边对应直接搬运，无须外部良基归纳。 -/
theorem eq_force_order_l {s t p} (hs : Name_d M B s) (ht : Name_d M B t) :
    Eq_force_d M B R z p s t ↔ Eq_force_d M B S z p s t := by
  have tr {R S} (hR : ∀ p q, M.mem p B → M.mem q B → (Entry_d M p q R ↔ Entry_d M p q S))
      (he : Eq_force_d M B R z p s t) : Eq_force_d M B S z p s t := by
    obtain ⟨W, hsW, htW, hW⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
      (KP.exists_union (ZF.modelsKP hZF)) hs ht
    obtain ⟨X, hX⟩ := triple_carrier_l M hZF B W
    obtain ⟨F, hF⟩ := bisim_max_l M hZF B R z X
    have hf := (eq_force_local_l M hZF hW hX hF he.1 hsW htW).mp he
    refine ⟨he.1, F, ?_, hf⟩
    intro v a b hab
    obtain ⟨w, hw, hwF⟩ := hab
    obtain ⟨v', a', b', hv, ha, hb, hw'⟩ := (hX w).mp (hF.subset w hwF)
    obtain ⟨rfl, rfl, rfl⟩ := triple_inj_l M hw hw'
    have hm (k : Bool) {a b} (ha : M.mem a W) (hb : M.mem b W)
        (hm : Match_d M k B R z F v a b) : Match_d M k B S z F v a b := by
      intro c d hcd q hq hqd
      have hd := (supp_entry_l M hW ha hcd).2
      obtain ⟨r, e, f, hr, hef, hrf, hre⟩ := hm c d hcd q
        ((below_order_l hR hv).mpr hq) ((hR q d hq.1 hd).mpr hqd)
      exact ⟨r, e, f, (below_order_l hR hq.1).mp hr, hef,
        (hR r f hr.1 (supp_entry_l M hW hb hef).2).mp hrf, hre⟩
    have hh := hF.bisim v a b ⟨w, hw, hwF⟩
    exact ⟨hm false ha hb hh.1, hm true hb ha hh.2⟩
  exact ⟨tr hR, tr (fun p q hp hq => (hR p q hp hq).symm)⟩

theorem mem_force_order_l {s t p} (hs : Name_d M B s) (ht : Name_d M B t) :
    Mem_force_d M B R z p s t ↔ Mem_force_d M B S z p s t := by
  have tr {R S} (hR : ∀ p q, M.mem p B → M.mem q B → (Entry_d M p q R ↔ Entry_d M p q S))
      (he : Mem_force_d M B R z p s t) : Mem_force_d M B S z p s t := by
    refine ⟨he.1, fun q hq => ?_⟩
    obtain ⟨r, a, b, hr, hab, hrb, hea⟩ := he.2 q ((below_order_l hR he.1).mpr hq)
    have hn := name_entry_l M ht hab
    exact ⟨r, a, b, (below_order_l hR hq.1).mp hr, hab, (hR r b hr.1 hn.2).mp hrb,
      (eq_force_order_l hR hZF hs hn.1).mp hea⟩
  exact ⟨tr hR, tr (fun p q hp hq => (hR p q hp hq).symm)⟩

omit hZF in
private theorem neg_order_l {P Q : M.Domain → Prop}
    (h : ∀ p, M.mem p B → (P p ↔ Q p)) {p} (hp : M.mem p B) :
    Neg_d M B R z P p ↔ Neg_d M B S z Q p :=
  ⟨fun hn q hq hQ => hn q ((below_order_l hR hp).mpr hq) ((h q hq.1).mpr hQ),
    fun hn q hq hP => hn q ((below_order_l hR hp).mp hq) ((h q hq.1).mp hP)⟩

/-- 任意原公式的名称力迫在删除、加入或改写域外关系条目后保持不变。 -/
theorem forces_order_l {a n} (φ : Formula a n) (ρ : Env M n)
    (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) :
    ∀ p, M.mem p B → (Forces_d M B R z φ ρ p ↔ Forces_d M B S z φ ρ p) := by
  have hn := @neg_order_l M B R S z hR
  have hc {P Q V W : M.Domain → Prop}
      (h : ∀ p, M.mem p B → (P p ↔ Q p)) (k : ∀ p, M.mem p B → (V p ↔ W p)) :=
    fun p hp => and_congr (h p hp) (k p hp)
  have push {n} {ρ : Env M n} (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) {s} (hs : Name_d M B s) :
      ∀ t : Term (n+1), Name_d M B (t.eval (ρ.push s)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i
  induction φ with
  | falsum => intro p _; simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_falsum_iff]
  | truth => intro p _; simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_truth_iff]
  | mem s t =>
    intro p _
    rw [forces_mem_l hZF.1, forces_mem_l hZF.1]
    exact mem_force_order_l hR hZF (hρ s) (hρ t)
  | atom r _ ts =>
    cases r
    · intro p _
      simp only [Forces_d, force_code_m, code_eq_l M hZF.1]
      exact eq_force_order_l hR hZF (hρ (ts 0)) (hρ (ts 1))
    · intro p hp
      simp only [Forces_d, force_code_m, code_all_l M hZF.1, imp_code_m, code_neg_l M hZF.1,
        Neg_d, code_conj_l, code_mem_l M hZF.1, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
      refine forall_congr' fun s => imp_congr_right fun hs => ?_
      have hm (t : Term _) (q : M.Domain) (_ : M.mem q B) := mem_force_order_l (z := z) hR hZF (p := q) hs (hρ t)
      simpa only [Neg_d] using hn (hc (hm (ts 0)) (fun q hq => hn (hm (ts 1)) hq)) hp
  | neg φ ih =>
    intro p hp
    simpa only [forces_neg_l hZF.1] using hn (ih ρ hρ) hp
  | conj φ ψ ih jh =>
    simpa only [forces_conj_l] using hc (ih ρ hρ) (jh ρ hρ)
  | disj φ ψ ih jh =>
    intro p hp
    simpa only [forces_disj_l, forces_neg_l hZF.1, forces_conj_l, Neg_d] using
      hn (hc (fun q hq => hn (ih ρ hρ) hq) (fun q hq => hn (jh ρ hρ) hq)) hp
  | imp φ ψ ih jh =>
    intro p hp
    simpa only [forces_imp_l hZF.1, Neg_d] using hn (hc (ih ρ hρ) (fun q hq => hn (jh ρ hρ) hq)) hp
  | iff φ ψ ih jh =>
    intro p hp
    simpa only [forces_iff_l, forces_conj_l, forces_imp_l hZF.1, Neg_d] using
      and_congr (hn (hc (ih ρ hρ) (fun q hq => hn (jh ρ hρ) hq)) hp)
        (hn (hc (jh ρ hρ) (fun q hq => hn (ih ρ hρ) hq)) hp)
  | forallE φ ih =>
    intro p hp
    rw [forces_all_l hZF.1, forces_all_l hZF.1]
    exact forall_congr' fun s => imp_congr_right fun hs => ih (ρ.push s) (push hρ hs) p hp
  | existsE φ ih =>
    have hall p (hp : M.mem p B) :
        (∀ s, Name_d M B s → Neg_d M B R z (Forces_d M B R z φ (ρ.push s)) p) ↔
        ∀ s, Name_d M B s → Neg_d M B S z (Forces_d M B S z φ (ρ.push s)) p :=
      forall_congr' fun s => imp_congr_right fun hs => hn (ih (ρ.push s) (push hρ hs)) hp
    intro p hp
    simpa only [forces_exists_l, forces_neg_l hZF.1, forces_all_l hZF.1, Neg_d] using hn hall hp

end YesMetaZFC.Model.Forcing.Internal
