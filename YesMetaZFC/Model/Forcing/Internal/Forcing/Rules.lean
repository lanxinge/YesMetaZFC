import YesMetaZFC.Model.Forcing.Internal.Names.Construction

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
