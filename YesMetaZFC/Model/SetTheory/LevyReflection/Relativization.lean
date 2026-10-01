import YesMetaZFC.Model.SetTheory.LevyReflection.Closure

/-! # 有限子公式闭包与反射的语义证明

存在量词收集真见证，全称量词收集反例。对原公式作结构归纳，统一见证闭性
给出原真值与有界相对化真值的双向等价；定义原子保留原生产语义。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

def lr_queries_l : {n : Nat} → (φ : Formula 1 n) → φ.FreeClosed → Lr_family
  | _, .falsum, _ | _, .truth, _ | _, .mem _ _, _ | _, .atom _ _ _, _ => []
  | _, .neg φ, h => lr_queries_l φ (by simpa only [Definitional.Formula.FreeClosed] using h)
  | _, .conj φ ψ, h | _, .disj φ ψ, h | _, .imp φ ψ, h | _, .iff φ ψ, h => by
    have hh : φ.FreeClosed ∧ ψ.FreeClosed := by simpa only [Definitional.Formula.FreeClosed] using h
    exact lr_queries_l φ hh.1 ++ lr_queries_l ψ hh.2
  | _, .existsE φ, h => by
    have hh : φ.FreeClosed := by simpa only [Definitional.Formula.FreeClosed] using h
    exact ⟨_, ⟨φ, hh⟩⟩ :: lr_queries_l φ hh
  | _, .forallE φ, h => by
    have hh : φ.FreeClosed := by simpa only [Definitional.Formula.FreeClosed] using h
    exact ⟨_, ({ body := φ, freeClosed := hh } : UnarySchema _).neg⟩ :: lr_queries_l φ hh

def lr_rel_m : {n d : Nat} → Formula 1 n → Term d → (Fin n → Term d) → Formula 1 d
  | _, _, .falsum, _, _ => .falsum
  | _, _, .truth, _, _ => .truth
  | _, _, .mem s t, _, e => .mem (s.bind e) (t.bind e)
  | _, _, .atom r hr ts, _, e => .atom r hr (ts.bind e)
  | _, _, .neg φ, X, e => .neg (lr_rel_m φ X e)
  | _, _, .conj φ ψ, X, e => .conj (lr_rel_m φ X e) (lr_rel_m ψ X e)
  | _, _, .disj φ ψ, X, e => .disj (lr_rel_m φ X e) (lr_rel_m ψ X e)
  | _, _, .imp φ ψ, X, e => .imp (lr_rel_m φ X e) (lr_rel_m ψ X e)
  | _, _, .iff φ ψ, X, e => .iff (lr_rel_m φ X e) (lr_rel_m ψ X e)
  | _, _, .existsE φ, X, e => Formula.existsMem X (lr_rel_m φ X.weaken (Fin.cases .newest (fun i => (e i).weaken)))
  | _, _, .forallE φ, X, e => Formula.forallMem X (lr_rel_m φ X.weaken (Fin.cases .newest (fun i => (e i).weaken)))

@[simp] theorem lr_rel_closed_l {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed) (X : Term d) (e : Fin n → Term d)
    (hX : X.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) : (lr_rel_m φ X e).FreeClosed := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [lr_rel_m, Definitional.Formula.FreeClosed]
  case mem s t =>
    simp only [lr_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨(Definitional.Term.freeSupport_bind_of_closed e he s).trans hφ.1,
      (Definitional.Term.freeSupport_bind_of_closed e he t).trans hφ.2⟩
  case atom r hr ts =>
    simp only [lr_rel_m, Definitional.Formula.FreeClosed]
    exact (Definitional.TermVector.freeClosed_bind_iff_of_closed e he ts).mpr hφ
  case neg φ ih =>
    simp only [lr_rel_m, Definitional.Formula.FreeClosed]
    exact ih hφ X e hX he
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [lr_rel_m, Definitional.Formula.FreeClosed]
    exact ⟨ih hφ.1 X e hX he, jh hφ.2 X e hX he⟩
  case existsE φ ih | forallE φ ih =>
    simp only [lr_rel_m, Formula.existsMem, Formula.forallMem, Definitional.Formula.FreeClosed]
    exact ⟨⟨rfl, by simpa using hX⟩, ih hφ X.weaken _ (by simpa using hX)
      (Fin.cases rfl (fun i => by simpa using he i))⟩

theorem lr_reflect_core_l {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed) {X : M.Domain}
    (h : Lr_step_d (lr_queries_l φ hφ) X X) (ρ : Env M n) (θ : Env M d) (T : Term d) (e : Fin n → Term d)
    (hT : T.eval θ = X) (he : ∀ i, (e i).eval θ = ρ.bound i) (hρ : ∀ i, M.mem (ρ.bound i) X) :
    Formula.satisfies ρ φ ↔ Formula.satisfies θ (lr_rel_m φ T e) := by
  have term {n d} (ρ : Env M n) (θ : Env M d) (e : Fin n → Term d)
      (he : ∀ i, (e i).eval θ = ρ.bound i) (t : Term n) (ht : t.freeSupport = []) :
      (t.bind e).eval θ = t.eval ρ := by
    cases t with
    | free _ => simp at ht
    | bound i => exact he i
  revert hφ ρ θ T e hT he hρ
  induction φ generalizing d <;> intro hφ h ρ θ T e hT he hρ
    <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [lr_rel_m, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff]
  case mem s t _ => simp only [lr_rel_m, Formula.satisfies_mem_iff, term ρ θ e he s hφ.1, term ρ θ e he t hφ.2]
  case atom r hr ts _ =>
    cases r <;> simp only [lr_rel_m, Formula.satisfies_atom_extensionalEq_iff, Formula.satisfies_atom_subset_iff,
      Definitional.TermVector.get_bind, term ρ θ e he (ts 0) (hφ 0), term ρ θ e he (ts 1) (hφ 1)]
  case neg φ ih _ =>
    rw [lr_rel_m, Formula.satisfies_neg_iff, Formula.satisfies_neg_iff]
    exact not_congr (ih hφ h ρ θ T e hT he hρ)
  case conj φ ψ ih jh _ | disj φ ψ ih jh _ | imp φ ψ ih jh _ | iff φ ψ ih jh _ =>
    have hl := ih hφ.1 (fun q hq => h q (List.mem_append_left _ hq)) ρ θ T e hT he hρ
    have hr := jh hφ.2 (fun q hq => h q (List.mem_append_right _ hq)) ρ θ T e hT he hρ
    simp only [lr_rel_m, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, hl, hr]
  case existsE φ ih _ =>
    have hc := h ⟨_, ⟨φ, hφ⟩⟩ (List.mem_cons_self ..)
    have tr x (hx : M.mem x X) := ih hφ (fun q hq => h q (List.mem_cons_of_mem _ hq))
      (ρ.push x) (θ.push x) T.weaken (Fin.cases .newest (fun i => (e i).weaken))
      (by simpa using hT) (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken θ x (e i)).trans (he i))) (Fin.cases hx hρ)
    rw [lr_rel_m, Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff, hT]
    constructor
    · intro hx
      obtain ⟨x, hxX, hx⟩ := hc ρ hρ hx
      exact ⟨x, hxX, (tr x hxX).mp hx⟩
    · exact fun ⟨x, hxX, hx⟩ => ⟨x, (tr x hxX).mpr hx⟩
  case forallE φ ih _ =>
    classical
    have hc := h ⟨_, ({ body := φ, freeClosed := hφ } : UnarySchema _).neg⟩ (List.mem_cons_self ..)
    have tr x (hx : M.mem x X) := ih hφ (fun q hq => h q (List.mem_cons_of_mem _ hq))
      (ρ.push x) (θ.push x) T.weaken (Fin.cases .newest (fun i => (e i).weaken))
      (by simpa using hT) (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken θ x (e i)).trans (he i))) (Fin.cases hx hρ)
    rw [lr_rel_m, Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, hT]
    refine ⟨fun hx x hxX => (tr x hxX).mp (hx x), fun hx x => ?_⟩
    apply Classical.byContradiction
    intro hn
    obtain ⟨y, hyX, hy⟩ := hc ρ hρ ⟨x, (Formula.satisfies_neg_iff _ _).mpr hn⟩
    exact (Formula.satisfies_neg_iff _ _).mp hy ((tr y hyX).mpr (hx y hyX))

def Lr_reflect_d {n} (φ : Formula 1 n) (X : M.Domain) : Prop := ∀ ρ : Env M n,
  (∀ i, M.mem (ρ.bound i) X) → (Formula.satisfies ρ φ ↔
    Formula.satisfies (ρ.push X) (lr_rel_m φ .newest (fun i => .bound i.succ)))

end YesMetaZFC.SetTheory
