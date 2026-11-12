import YesMetaZFC.Model.SetTheory.LevyReflection.Relativization
import YesMetaZFC.Model.SetTheory.Source.Basic
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial

/-! # 任意集合载体上的原公式相对化

先展开等同、子集两个定义原子，再把量词限制到载体。因此这里无须传递性，
可以把实际内部结构的语义证书写成背景模型中的单个原公式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sr_rel_m : {n d : Nat} → Formula 1 n → Term d → (Fin n → Term d) → Formula 1 d
  | _, _, .falsum, _, _ => .falsum
  | _, _, .truth, _, _ => .truth
  | _, _, .mem s t, _, e => .mem (s.bind e) (t.bind e)
  | _, _, .atom .extensionalEq _ ts, X, e => Formula.forallMem X
      (.iff (.mem .newest ((ts 0).bind e).weaken) (.mem .newest ((ts 1).bind e).weaken))
  | _, _, .atom .subset _ ts, X, e => Formula.forallMem X
      (.imp (.mem .newest ((ts 0).bind e).weaken) (.mem .newest ((ts 1).bind e).weaken))
  | _, _, .neg φ, X, e => .neg (sr_rel_m φ X e)
  | _, _, .conj φ ψ, X, e => .conj (sr_rel_m φ X e) (sr_rel_m ψ X e)
  | _, _, .disj φ ψ, X, e => .disj (sr_rel_m φ X e) (sr_rel_m ψ X e)
  | _, _, .imp φ ψ, X, e => .imp (sr_rel_m φ X e) (sr_rel_m ψ X e)
  | _, _, .iff φ ψ, X, e => .iff (sr_rel_m φ X e) (sr_rel_m ψ X e)
  | _, _, .existsE φ, X, e => Formula.existsMem X (sr_rel_m φ X.weaken (Fin.cases .newest (fun i => (e i).weaken)))
  | _, _, .forallE φ, X, e => Formula.forallMem X (sr_rel_m φ X.weaken (Fin.cases .newest (fun i => (e i).weaken)))

@[simp] theorem sr_rel_closed_l {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed) (X : Term d) (e : Fin n → Term d)
    (hX : X.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) : (sr_rel_m φ X e).FreeClosed := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => trivial
  case mem s t =>
    exact ⟨(Definitional.Term.freeSupport_bind_of_closed e he s).trans hφ.1,
      (Definitional.Term.freeSupport_bind_of_closed e he t).trans hφ.2⟩
  case atom r hr ts =>
    have h0 := (Definitional.Term.freeSupport_bind_of_closed e he (ts 0)).trans (hφ 0)
    have h1 := (Definitional.Term.freeSupport_bind_of_closed e he (ts 1)).trans (hφ 1)
    cases r <;> simp -implicitDefEqProofs [sr_rel_m, Formula.forallMem, Definitional.Formula.FreeClosed, hX, h0, h1]
  case neg φ ih => exact ih hφ X e hX he
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    exact ⟨ih hφ.1 X e hX he, jh hφ.2 X e hX he⟩
  case existsE φ ih | forallE φ ih =>
    exact ⟨⟨rfl, by simpa using hX⟩, ih hφ X.weaken _ (by simpa using hX)
      (Fin.cases rfl (fun i => by simpa using he i))⟩

theorem sr_rel_sat_l {X : M.Domain} (nx : Nonempty {x // M.mem x X}) {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env (rt_model_l X nx) n) (θ : Env M d) (T : Term d) (e : Fin n → Term d)
    (hT : T.eval θ = X) (he : ∀ i, (e i).eval θ = (ρ.bound i).val) :
    Formula.satisfies θ (sr_rel_m φ T e) ↔ Formula.satisfies ρ φ := by
  have term {n d} (ρ : Env (rt_model_l X nx) n) (θ : Env M d) (e : Fin n → Term d)
      (he : ∀ i, (e i).eval θ = (ρ.bound i).val) (t : Term n) (ht : t.freeSupport = []) :
      (t.bind e).eval θ = (t.eval ρ).val := by
    cases t with
    | free _ => simp at ht
    | bound i => exact he i
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [sr_rel_m, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff]
  case mem s t =>
    simp only [sr_rel_m, Formula.satisfies_mem_iff, term ρ θ e he s hφ.1, term ρ θ e he t hφ.2]
    rfl
  case atom r hr ts =>
    cases r <;> simp only [sr_rel_m, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_atom_extensionalEq_iff,
      Formula.satisfies_atom_subset_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
      term ρ θ e he (ts 0) (hφ 0), term ρ θ e he (ts 1) (hφ 1), hT]
    all_goals exact ⟨fun h x => h x.val x.property, fun h x hx => h ⟨x, hx⟩⟩
  case neg φ ih => exact not_congr (ih hφ ρ θ T e hT he)
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    simp only [sr_rel_m, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, ih hφ.1 ρ θ T e hT he, jh hφ.2 ρ θ T e hT he]
  case existsE φ ih | forallE φ ih =>
    have tr (x : (rt_model_l X nx).Domain) := ih hφ (ρ.push x) (θ.push x.val) T.weaken
      (Fin.cases .newest (fun i => (e i).weaken)) (by simpa using hT)
      (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken θ x.val (e i)).trans (he i)))
    first
    | rw [sr_rel_m, Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, hT]
      exact ⟨fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, (tr ⟨x, hx⟩).mp h⟩,
        fun ⟨x, h⟩ => ⟨x.val, x.property, (tr x).mpr h⟩⟩
    | rw [sr_rel_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, hT]
      exact ⟨fun h x => (tr x).mp (h x.val x.property), fun h x hx => (tr ⟨x, hx⟩).mpr (h ⟨x, hx⟩)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 内部不可达判断的背景原公式

完整展开定义原子后，相对化适用于任意真实载体；此处不偷加源模型传递性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_inaccessible_raw_m {d} (ω X κ : Term d) : Formula 1 d := .conj (.mem ω X) (.conj (.mem κ X)
  (sr_rel_m (sc_inaccessible_m (.bound 1 : Term 2) .newest) X (Fin.cases κ (fun _ => ω))))

@[simp] theorem sc_inaccessible_raw_closed_l {d} (ω X κ : Term d)
    (hw : ω.freeSupport = []) (hX : X.freeSupport = []) (hk : κ.freeSupport = []) :
    (sc_inaccessible_raw_m ω X κ).FreeClosed := by
  exact ⟨⟨hw, hX⟩, ⟨⟨hk, hX⟩, sr_rel_closed_l _ (sc_inaccessible_m_freeClosed _ _ rfl rfl)
    X _ hX (Fin.cases hk (fun _ => hw))⟩⟩

theorem sc_inaccessible_raw_sat_l {d} (ρ : Env M d) (ω X κ : Term d) :
    Formula.satisfies ρ (sc_inaccessible_raw_m ω X κ) ↔
      Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (κ.eval ρ) := by
  simp only [sc_inaccessible_raw_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Sc_inaccessible_d]
  have read (hw : M.mem (ω.eval ρ) (X.eval ρ)) (hk : M.mem (κ.eval ρ) (X.eval ρ)) :=
    sr_rel_sat_l ⟨⟨ω.eval ρ, hw⟩⟩ (sc_inaccessible_m (.bound 1 : Term 2) .newest)
      (sc_inaccessible_m_freeClosed _ _ rfl rfl)
      ⟨Fin.cases ⟨κ.eval ρ, hk⟩ (fun _ => ⟨ω.eval ρ, hw⟩), fun _ => ⟨ω.eval ρ, hw⟩⟩
      ρ X (Fin.cases κ (fun _ => ω)) rfl (Fin.cases rfl (fun _ => rfl))
  exact ⟨fun ⟨hw, hk, h⟩ => ⟨hw, hk, (read hw hk).mp h⟩,
    fun ⟨hw, hk, h⟩ => ⟨hw, hk, (read hw hk).mpr h⟩⟩

end YesMetaZFC.SetTheory.Internal
