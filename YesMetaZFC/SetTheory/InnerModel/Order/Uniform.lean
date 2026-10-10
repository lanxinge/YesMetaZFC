import YesMetaZFC.SetTheory.InnerModel.Order.Macro

/-! # J 层上的统一局部 Σ₁ 良序

固定公式只猜测一个较早有序微层的完整递归证书。微层端延拓保证比较结果
无关乎所选层；局部历史定理保证所需证书存在于正在解释公式的原 J 层中。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Js_lt_d (x y : M.Domain) : Prop := ∃ a U R,
  M.IsOrdinal a ∧ Js_value_d a U R ∧ M.mem x U ∧ M.mem y U ∧ Rd_entry_d x y R

def Js_lt_cert_d (ρ : Env M 0) (T x y : M.Domain) : Prop :=
  ∃ a, M.mem a T ∧ ∃ p, M.mem p T ∧ ∃ U, M.mem U T ∧ ∃ R, M.mem R T ∧
    M.IsOrdinal a ∧ KPair_d M p U R ∧
    Formula.satisfies (((ρ.push a).push p).push T) (rc_value_s rw_op_s).matrix.body ∧
    M.mem x U ∧ M.mem y U ∧ Rd_entry_d x y R

/-- 无参数的同一 Σ₁ 二元公式，用于背景和每个非空 J 层。 -/
def js_less_s : S1_binary 0 where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (Formula.existsMem (.bound 2) (Formula.existsMem (.bound 3)
        (.conj (KP.ord0_m (.bound 3)) (.conj (kpair0_m (.bound 2) (.bound 1) .newest)
          (.conj (js_wit_m (.bound 3) (.bound 2) (.bound 4))
            (.conj (.mem (.bound 6) (.bound 1)) (.conj (.mem (.bound 5) (.bound 1))
              (rd_entry0_m (.bound 6) (.bound 5) .newest)))))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (KP.ord0_delta_l _) (.conj (kpair0_delta_l ..) (.conj (js_wit_delta_l ..)
        (.conj (.mem _ _) (.conj (.mem _ _) (rd_entry0_delta_l ..))))))))) }

theorem js_less_matrix_l (hKP : M.Models KP) (ρ : Env M 0) (x y T : M.Domain) :
    Formula.satisfies (((ρ.push x).push y).push T) js_less_s.matrix.body ↔ Js_lt_cert_d ρ T x y := by
  simp only [js_less_s, Js_lt_cert_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    KP.ord0_sat_l hKP, kpair0_sat_l hKP.1, js_wit_sat_l ρ, Formula.satisfies_mem_iff, rd_entry0_sat_l hKP.1]; rfl

theorem Js_lt_cert_d.sound_l {ρ : Env M 0} {T x y : M.Domain} (h : Js_lt_cert_d ρ T x y) : Js_lt_d x y := by
  obtain ⟨a, _, p, _, U, _, R, _, ha, hp, hm, hx, hy, hxy⟩ := h
  exact ⟨a, U, R, ha, ⟨p, (js_state_env_l ρ a p).mp ((S1_binary.sat_l _ ρ a p).mpr ⟨T, hm⟩), hp⟩, hx, hy, hxy⟩

theorem js_less_witness_l (hKP : M.Models KP) {ρ : Env M 0} {a p U R x y T : M.Domain}
    (ha : M.IsOrdinal a) (hp : KPair_d M p U R) (hx : M.mem x U) (hy : M.mem y U) (hxy : Rd_entry_d x y R)
    (h : Formula.satisfies (((ρ.push a).push p).push T) (rc_value_s rw_op_s).matrix.body) : Js_lt_cert_d ρ T x y := by
  obtain ⟨A, F, hf, haA, hap⟩ := (rc_matrix_sat_l hKP.1 rw_op_s ρ a p T).mp h
  have hpT := (hf.function.bound_l hap).2
  have bounds := po_pair_bound_l hf.trans hpT hp
  exact ⟨a, hf.trans A hf.domain a haA, p, hpT, U, bounds.1, R, bounds.2, ha, hp, h, hx, hy, hxy⟩

theorem js_less_sat_l (hKP : M.Models KP) (ρ : Env M 0) (x y : M.Domain) :
    js_less_s.schema.denote ρ x y ↔ Js_lt_d x y := by
  rw [S1_binary.sat_l]; simp only [js_less_matrix_l hKP]
  constructor
  · exact fun ⟨_, h⟩ => h.sound_l
  · rintro ⟨a, U, R, ha, ⟨p, hp, hpUR⟩, hx, hy, hxy⟩
    obtain ⟨T, hm⟩ := (S1_binary.sat_l _ ρ a p).mp ((js_state_env_l ρ a p).mpr hp)
    exact ⟨T, js_less_witness_l hKP ha hpUR hx hy hxy hm⟩

theorem js_less_at_l (hM : M.Models KPi) {a U R x y : M.Domain} (ha : M.IsOrdinal a)
    (h : Js_value_d a U R) (hx : M.mem x U) (hy : M.mem y U) : Js_lt_d x y ↔ Rd_entry_d x y R := by
  constructor
  · rintro ⟨b, V, S, hb, hv, hxV, hyV, hxy⟩
    exact (js_comparable_l hM ha hb h hv).elim
      (fun he => ((he.2 x y hy).mp hxy).2) (fun he => (he.2 x y hyV).mpr ⟨hxV, hxy⟩)
  · exact fun hxy => ⟨a, U, R, ha, h, hx, hy, hxy⟩

/-- 任意微层都是全局序的初段，而不只是其上的比较结果一致。 -/
theorem js_less_initial_l (hM : M.Models KPi) {a U R x y : M.Domain} (ha : M.IsOrdinal a)
    (h : Js_value_d a U R) (hy : M.mem y U) (hxy : Js_lt_d x y) : M.mem x U := by
  obtain ⟨b, V, S, hb, hv, hxV, _, hxy⟩ := hxy
  exact (js_comparable_l hM ha hb h hv).elim
    (fun he => ((he.2 x y hy).mp hxy).1) (fun he => he.1 x hxV)

/-- 适用于已有实例的传递 rud 闭包：较早微层覆盖保证所有比较见证均可内置。 -/
theorem js_less_local_l (hM : M.Models KPi) {C : M.Domain} (hC : Rd_closed_d C) (hc : M.TransitiveSet C)
    (cover : ∀ x, M.mem x C → Js_access_d C x) (hn : Nonempty {x : M.Domain // M.mem x C})
    (ρ : Env (rt_model_l C hn) 0) (x y : (rt_model_l C hn).Domain) :
    js_less_s.schema.denote ρ x y ↔ Js_lt_d x.val y.val := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let η := image_env_l Subtype.val ρ
  have matrix (T : (rt_model_l C hn).Domain) :
      Formula.satisfies (((ρ.push x).push y).push T) js_less_s.matrix.body ↔ Js_lt_cert_d η T.val x.val y.val := by
    apply (rt_model_delta_l hc hn js_less_s.matrix.delta0 _).trans
    apply Iff.trans ?_ (js_less_matrix_l hKP η x.val y.val T.val)
    exact Formula.closed_env_l _ js_less_s.matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  rw [S1_binary.sat_l]; simp only [matrix]
  constructor
  · exact fun ⟨_, h⟩ => h.sound_l
  · intro hxy
    obtain ⟨a, U, R, ha, hu, hUC, hx, hy⟩ := js_access_pair_l hM (cover x.val x.property) (cover y.val y.property)
    have entry := (js_less_at_l hM ha hu hx hy).mp hxy
    obtain ⟨p, hp, hpUR⟩ := hu
    obtain ⟨T, hTC, _, _, ht⟩ := js_state_in_l hM hC hc η ha hp hpUR hUC
    exact ⟨⟨T, hTC⟩, js_less_witness_l hKP ha hpUR hx hy entry ht⟩

/-- 统一局部定义：原 Jₐ 无需可容许性，也不要求背景的 ω 或序数外部标准。 -/
theorem jh_local_sigma1_l (hM : M.Models KPi) {a C : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) (ρ : Env (rt_model_l C hn) 0) (x y : (rt_model_l C hn).Domain) :
    js_less_s.schema.denote ρ x y ↔ Js_lt_d x.val y.val :=
  js_less_local_l hM (jh_value_closed_l hM ha h) (jh_value_transitive_l hM h)
    (js_rep_access_l hM (jh_value_closed_l hM ha h) (jh_order_rep_l hM ha h)) hn ρ x y

theorem jh_order_initial_l (hM : M.Models KPi) {a C x y : M.Domain} (ha : M.IsOrdinal a)
    (h : Jh_value_d a C) (hy : M.mem y C) (hxy : Js_lt_d x y) : M.mem x C := by
  obtain ⟨b, R, hb, hr⟩ := jh_order_rep_l hM ha h
  exact js_less_initial_l hM hb hr hy hxy

/-- 良序与局部定义合并；空的 J₀ 也有空良序，非空层再给出其结构内的解释。 -/
theorem jh_local_wellorder_l (hM : M.Models KPi) {a C : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C) :
    ∃ R, M.IsSetCodedWellOrder (kp_pair_l (KPi.models_iff_l.mp hM).1) R C ∧
      (∀ x y, M.mem x C → M.mem y C → (Js_lt_d x y ↔ Rd_entry_d x y R)) ∧
      ∀ hn : Nonempty {x : M.Domain // M.mem x C}, ∀ ρ : Env (rt_model_l C hn) 0,
        ∀ x y : (rt_model_l C hn).Domain, js_less_s.schema.denote ρ x y ↔ Rd_entry_d x.val y.val R := by
  obtain ⟨b, R, hb, hr⟩ := jh_order_rep_l hM ha h
  exact ⟨R, (js_coherence_l hM hb hr).2.1, fun _ _ hx hy => js_less_at_l hM hb hr hx hy,
    fun hn ρ x y => (jh_local_sigma1_l hM ha h hn ρ x y).trans (js_less_at_l hM hb hr x.property y.property)⟩

end YesMetaZFC.SetTheory.InnerModel
