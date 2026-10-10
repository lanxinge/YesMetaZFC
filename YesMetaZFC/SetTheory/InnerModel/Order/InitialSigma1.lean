import YesMetaZFC.SetTheory.InnerModel.Order.Initial

/-! # 初段函数的统一局部 Σ₁ 图

猜测完整微层状态后，用有界的双向成员条件检查整个初段。状态证书的局部性
保证同一公式在每个原 J 层内既可靠又完备，输出也是该层中的实际集合。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Js_initial_cert_d (ρ : Env M 0) (T x I : M.Domain) : Prop :=
  ∃ a, M.mem a T ∧ ∃ p, M.mem p T ∧ ∃ U, M.mem U T ∧ ∃ R, M.mem R T ∧
    M.IsOrdinal a ∧ KPair_d M p U R ∧
    Formula.satisfies (((ρ.push a).push p).push T) (rc_value_s rw_op_s).matrix.body ∧
    M.mem x U ∧ Js_pred_d U R x I

def js_initial_s : S1_binary 0 where
  matrix := {
    -- 量词后的槽位为 R,U,p,a,T,I,x；完整输出 I 由双向有界成员条件核验。
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (Formula.existsMem (.bound 2) (Formula.existsMem (.bound 3)
        (.conj (KP.ord0_m (.bound 3)) (.conj (kpair0_m (.bound 2) (.bound 1) .newest)
          (.conj (js_wit_m (.bound 3) (.bound 2) (.bound 4))
            (.conj (.mem (.bound 6) (.bound 1)) (js_pred_m (.bound 1) .newest (.bound 6) (.bound 5)))))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (KP.ord0_delta_l _) (.conj (kpair0_delta_l ..) (.conj (js_wit_delta_l ..)
        (.conj (.mem _ _) (js_pred_delta_l ..)))))))) }

theorem js_initial_matrix_l (hKP : M.Models KP) (ρ : Env M 0) (x I T : M.Domain) :
    Formula.satisfies (((ρ.push x).push I).push T) js_initial_s.matrix.body ↔ Js_initial_cert_d ρ T x I := by
  simp only [js_initial_s, Js_initial_cert_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    KP.ord0_sat_l hKP, kpair0_sat_l hKP.1, js_wit_sat_l ρ, Formula.satisfies_mem_iff, js_pred_sat_l hKP.1]; rfl

theorem Js_initial_cert_d.sound_l (hM : M.Models KPi) {ρ : Env M 0} {T x I : M.Domain}
    (h : Js_initial_cert_d ρ T x I) : Js_initial_d x I := by
  obtain ⟨a, _, p, _, U, _, R, _, ha, hp, hm, hx, hi⟩ := h
  have state := (js_state_env_l ρ a p).mp ((S1_binary.sat_l _ ρ a p).mpr ⟨T, hm⟩)
  exact (js_initial_at_l hM ha ⟨p, state, hp⟩ hx).mpr hi

theorem js_initial_cert_in_l (hM : M.Models KPi) {C x I : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (hx : Js_access_d C x) (hi : Js_initial_d x I) (ρ : Env M 0) :
    ∃ T, M.mem T C ∧ Js_initial_cert_d ρ T x I := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨a, U, R, ha, hu, hUC, hx⟩ := hx
  have pred := (js_initial_at_l hM ha hu hx).mp hi
  obtain ⟨p, hp, hpUR⟩ := hu
  obtain ⟨T, hTC, ht, hpT, hm⟩ := js_state_in_l hM hC hc ρ ha hp hpUR hUC
  obtain ⟨A, F, hf, haA, _⟩ := (rc_matrix_sat_l hKP.1 rw_op_s ρ a p T).mp hm
  have bounds := po_pair_bound_l ht hpT hpUR
  exact ⟨T, hTC, a, ht A hf.domain a haA, p, hpT, U, bounds.1, R, bounds.2, ha, hpUR, hm, hx, pred⟩

theorem js_initial_sat_l (hM : M.Models KPi) (ρ : Env M 0) (x I : M.Domain) :
    js_initial_s.schema.denote ρ x I ↔ Js_initial_d x I := by
  rw [S1_binary.sat_l]; simp only [js_initial_matrix_l (KPi.models_iff_l.mp hM).1]
  refine ⟨fun ⟨_, h⟩ => h.sound_l hM, fun hi => ?_⟩
  obtain ⟨a, C, ha, hx⟩ := hi.1
  have hC := jh_value_closed_l hM ha.1 ha.2
  obtain ⟨T, _, ht⟩ := js_initial_cert_in_l hM hC (jh_value_transitive_l hM ha.2)
    (js_rep_access_l hM hC (jh_order_rep_l hM ha.1 ha.2) x hx) hi ρ
  exact ⟨T, ht⟩

theorem js_initial_local_l (hM : M.Models KPi) {C : M.Domain} (hC : Rd_closed_d C)
    (hc : M.TransitiveSet C) (cover : ∀ x, M.mem x C → Js_access_d C x)
    (hn : Nonempty {x : M.Domain // M.mem x C}) (ρ : Env (rt_model_l C hn) 0)
    (x I : (rt_model_l C hn).Domain) : js_initial_s.schema.denote ρ x I ↔ Js_initial_d x.val I.val := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let η := image_env_l Subtype.val ρ
  have matrix (T : (rt_model_l C hn).Domain) :
      Formula.satisfies (((ρ.push x).push I).push T) js_initial_s.matrix.body ↔ Js_initial_cert_d η T.val x.val I.val := by
    apply (rt_model_delta_l hc hn js_initial_s.matrix.delta0 _).trans
    apply Iff.trans ?_ (js_initial_matrix_l hKP η x.val I.val T.val)
    exact Formula.closed_env_l _ js_initial_s.matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  rw [S1_binary.sat_l]; simp only [matrix]
  refine ⟨fun ⟨_, h⟩ => h.sound_l hM, fun hi => ?_⟩
  obtain ⟨T, hTC, ht⟩ := js_initial_cert_in_l hM hC hc (cover x.val x.property) hi η
  exact ⟨⟨T, hTC⟩, ht⟩

/-- 端点和输出属于 Jₐ 时，层内公式等价于背景中的完整全局初段规格。 -/
theorem jh_initial_local_l (hM : M.Models KPi) {a C : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) (ρ : Env (rt_model_l C hn) 0) (x I : (rt_model_l C hn).Domain) :
    js_initial_s.schema.denote ρ x I ↔ Js_initial_d x.val I.val :=
  js_initial_local_l hM (jh_value_closed_l hM ha h) (jh_value_transitive_l hM h)
    (js_rep_access_l hM (jh_value_closed_l hM ha h) (jh_order_rep_l hM ha h)) hn ρ x I

/-- 单层内部的初段图是实际总函数；不要求该层满足任何收集模式。 -/
theorem jh_initial_function_l (hM : M.Models KPi) {a C : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) (ρ : Env (rt_model_l C hn) 0) (x : (rt_model_l C hn).Domain) :
    ∃ I : (rt_model_l C hn).Domain, js_initial_s.schema.denote ρ x I ∧
      ∀ K, js_initial_s.schema.denote ρ x K → K = I := by
  obtain ⟨I, hIC, hi⟩ := jh_initial_in_l hM ha h x.property
  refine ⟨⟨I, hIC⟩, (jh_initial_local_l hM ha h hn ρ x ⟨I, hIC⟩).mpr hi, fun K hk => ?_⟩
  exact Subtype.ext (js_initial_unique_l (KPi.models_iff_l.mp hM).1.1 ((jh_initial_local_l hM ha h hn ρ x K).mp hk) hi)

end YesMetaZFC.SetTheory.InnerModel
