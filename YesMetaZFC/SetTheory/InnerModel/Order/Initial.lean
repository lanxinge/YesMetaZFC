import YesMetaZFC.SetTheory.InnerModel.Order.InternalState

/-! # Jensen 序的精确初段及其层内集合化

含端点的微层已经包含全部前驱。读取它的实际关系表后，只需 Δ₀ 分离；
局部状态证书同时给出所有分离参数的层内传递界。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Js_pred_d (U R x I : M.Domain) : Prop := ∀ y, M.mem y I ↔ M.mem y U ∧ Rd_entry_d y x R
def Js_initial_d (x I : M.Domain) : Prop := L_d x ∧ ∀ y, M.mem y I ↔ Js_lt_d y x

def js_pred_m {n} (U R x I : Term n) : Formula 1 n :=
  .conj (Formula.forallMem I (.conj (.mem .newest U.weaken) (rd_entry0_m .newest x.weaken R.weaken)))
    (Formula.forallMem U (.imp (rd_entry0_m .newest x.weaken R.weaken) (.mem .newest I.weaken)))
derive_free_closed js_pred_m
theorem js_pred_delta_l {n} (U R x I : Term n) : (js_pred_m U R x I).IsDelta0 :=
  .conj (.forallMem _ (.conj (.mem _ _) (rd_entry0_delta_l ..)))
    (.forallMem _ (.imp (rd_entry0_delta_l ..) (.mem _ _)))

theorem js_pred_sat_l (hE : Extensional M) {n} (ρ : Env M n) (U R x I : Term n) :
    Formula.satisfies ρ (js_pred_m U R x I) ↔ Js_pred_d (U.eval ρ) (R.eval ρ) (x.eval ρ) (I.eval ρ) := by
  simp only [js_pred_m, Js_pred_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨h, g⟩ y => ⟨h y, fun hy => g y hy.1 hy.2⟩,
    fun h => ⟨fun y => (h y).mp, fun y hy hxy => (h y).mpr ⟨hy, hxy⟩⟩⟩

theorem js_initial_at_l (hM : M.Models KPi) {a U R x I : M.Domain} (ha : M.IsOrdinal a)
    (h : Js_value_d a U R) (hx : M.mem x U) : Js_initial_d x I ↔ Js_pred_d U R x I := by
  have slice y : Js_lt_d y x ↔ M.mem y U ∧ Rd_entry_d y x R :=
    ⟨fun hy => let hyU := js_less_initial_l hM ha h hx hy
      ⟨hyU, (js_less_at_l hM ha h hyU hx).mp hy⟩,
     fun ⟨hy, hyx⟩ => (js_less_at_l hM ha h hy hx).mpr hyx⟩
  exact ⟨fun hi y => (hi.2 y).trans (slice y), fun hi =>
    ⟨l_transitive_l hM (js_value_constructible_l hM ha h).1 hx, fun y => (hi y).trans (slice y).symm⟩⟩

theorem js_initial_unique_l (hE : Extensional M) {x I K : M.Domain}
    (hi : Js_initial_d x I) (hk : Js_initial_d x K) : I = K :=
  hE.eq_of_same_members I K (fun y => (hi.2 y).trans (hk.2 y).symm)

/-- 可见微层内作分离，得到的是真正全局初段；输出本身属于所选闭包。 -/
theorem js_initial_in_l (hM : M.Models KPi) {C x : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hx : Js_access_d C x) : ∃ I, M.mem I C ∧ Js_initial_d x I := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨a, U, R, ha, hu, hUC, hx⟩ := hx
  obtain ⟨p, hp, hpUR⟩ := hu
  obtain ⟨T, hTC, ht, hpT, _⟩ := js_state_in_l hM hC hc (js_env_l x) ha hp hpUR hUC
  have bounds := po_pair_bound_l ht hpT hpUR
  let φ : Delta0UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2), delta0 := rd_entry0_delta_l .. }
  let ρ := ((js_env_l x).push R).push x
  obtain ⟨I, hIC, hi⟩ := rd_separation_l hKP hC hc hTC ht φ ρ
    (Fin.cases (ht U bounds.1 x hx) (Fin.cases bounds.2 (fun i => Fin.elim0 i))) bounds.1
  have pred : Js_pred_d U R x I := fun y => (hi y).trans
    (and_congr_right fun _ => rd_entry0_sat_l hKP.1 (ρ.push y) .newest (.bound 1) (.bound 2))
  exact ⟨I, hIC, (js_initial_at_l hM ha ⟨p, hp, hpUR⟩ hx).mpr pred⟩

/-- 每个端点的全局前驱集合留在包含该端点的每一个原 J 层中。 -/
theorem jh_initial_in_l (hM : M.Models KPi) {a C x : M.Domain} (ha : M.IsOrdinal a)
    (h : Jh_value_d a C) (hx : M.mem x C) : ∃ I, M.mem I C ∧ Js_initial_d x I :=
  js_initial_in_l hM (jh_value_closed_l hM ha h) (jh_value_transitive_l hM h)
    (js_rep_access_l hM (jh_value_closed_l hM ha h) (jh_order_rep_l hM ha h) x hx)

theorem js_initial_exists_l (hM : M.Models KPi) {x : M.Domain} (hx : L_d x) : ∃ I, L_d I ∧ Js_initial_d x I := by
  obtain ⟨a, C, ha, hx⟩ := hx
  obtain ⟨I, hi, hI⟩ := jh_initial_in_l hM ha.1 ha.2 hx
  exact ⟨I, ⟨a, C, ha, hi⟩, hI⟩

end YesMetaZFC.SetTheory.InnerModel
