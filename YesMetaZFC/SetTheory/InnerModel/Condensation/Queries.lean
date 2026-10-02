import YesMetaZFC.SetTheory.InnerModel.Condensation.Recognition
import YesMetaZFC.Model.SetTheory.Sigma1Substructure

/-! # 凝聚所需的实际 Σ₁ 见证查询

只传输两类存在式：十三项 rud 运算的输出，以及包含指定对象的完整微层
证书。它们在每个 J 层中都有见证；在传递坍塌中分别恢复 rud 闭性和微层覆盖。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def jc_rud_s (k : Rd_sym) : Delta0UnarySchema 3 where
  body := rd_graph_m k (.bound 1) (.bound 2) (.bound 3) .newest
  delta0 := rd_graph_delta_l ..

theorem jc_rud_total_l (hKP : M.Models KP) {C : M.Domain} (hc : M.TransitiveSet C) (hC : Rd_closed_d C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) (k : Rd_sym) (ρ : Env (rt_model_l C hn) 3) :
    ∃ y, (jc_rud_s k).toUnarySchema.denote ρ y := by
  obtain ⟨y, hy⟩ := rd_fun_exists_l hKP k (ρ.bound 0).val (ρ.bound 1).val (ρ.bound 2).val
  have hYC := hC k _ _ _ (ρ.bound 0).property (ρ.bound 1).property (ρ.bound 2).property y hy
  refine ⟨⟨y, hYC⟩, (rt_model_delta_l hc hn (jc_rud_s k).delta0 (ρ.push ⟨y, hYC⟩)).mpr ?_⟩
  exact (rd_graph_sat_l hKP _ k _ _ _ _).mpr hy

theorem jc_rud_closed_l (hKP : M.Models KP) {B : M.Domain} (hb : M.TransitiveSet B)
    (hn : Nonempty {x : M.Domain // M.mem x B})
    (ht : ∀ k, ∀ ρ : Env (rt_model_l B hn) 3, ∃ y, (jc_rud_s k).toUnarySchema.denote ρ y) : Rd_closed_d B := by
  intro k x y z hx hy hz v hv
  let ρ : Env (rt_model_l B hn) 3 :=
    ⟨Fin.cases ⟨x, hx⟩ (Fin.cases ⟨y, hy⟩ (fun _ => ⟨z, hz⟩)), fun _ => ⟨x, hx⟩⟩
  obtain ⟨w, hw⟩ := ht k ρ
  have hr := (rd_graph_sat_l hKP _ k _ _ _ _).mp ((rt_model_delta_l hb hn (jc_rud_s k).delta0 (ρ.push w)).mp hw)
  have eq := rd_fun_unique_l hKP.1 hv hr
  exact eq.symm ▸ w.property

def jc_cover_s : Delta0UnarySchema 1 where
  body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
    (Formula.existsMem (.bound 2) (Formula.existsMem (.bound 3)
      (.conj (KP.ord0_m (.bound 3)) (.conj (kpair0_m (.bound 2) (.bound 1) .newest)
        (.conj (js_wit_m (.bound 3) (.bound 2) (.bound 4)) (.mem (.bound 5) (.bound 1))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (KP.ord0_delta_l _) (.conj (kpair0_delta_l ..) (.conj (js_wit_delta_l ..) (.mem _ _)))))))

theorem jc_cover_sat_l (hKP : M.Models KP) (ρ : Env M 1) (T : M.Domain) :
    jc_cover_s.toUnarySchema.denote ρ T ↔ ∃ a, M.mem a T ∧ ∃ p, M.mem p T ∧
      ∃ U, M.mem U T ∧ ∃ R, M.mem R T ∧ M.IsOrdinal a ∧ KPair_d M p U R ∧
        Formula.satisfies ((((js_env_l (ρ.bound 0)).push a).push p).push T) (rc_value_s rw_op_s).matrix.body ∧ M.mem (ρ.bound 0) U := by
  simp only [UnarySchema.denote, jc_cover_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    KP.ord0_sat_l hKP, kpair0_sat_l hKP.1, js_wit_sat_l (js_env_l (ρ.bound 0)), Formula.satisfies_mem_iff]; rfl

theorem jc_cover_total_l (hM : M.Models KPi) {a C : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) (ρ : Env (rt_model_l C hn) 1) :
    ∃ T, jc_cover_s.toUnarySchema.denote ρ T := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have hc := jh_value_transitive_l hM h
  have hC := jh_value_closed_l hM ha h
  obtain ⟨b, U, R, hb, hu, hUC, hx⟩ := js_rep_access_l hM hC (jh_order_rep_l hM ha h) (ρ.bound 0).val (ρ.bound 0).property
  obtain ⟨p, hp, hpUR⟩ := hu
  obtain ⟨T, hTC, ht, hpT, hm⟩ := js_state_in_l hM hC hc (js_env_l (ρ.bound 0).val) hb hp hpUR hUC
  obtain ⟨A, F, hf, hbA, _⟩ := (rc_matrix_sat_l hKP.1 rw_op_s _ b p T).mp hm
  have bounds := po_pair_bound_l ht hpT hpUR
  refine ⟨⟨T, hTC⟩, (rt_model_delta_l hc hn jc_cover_s.delta0 (ρ.push ⟨T, hTC⟩)).mpr ?_⟩
  apply (Formula.closed_env_l _ jc_cover_s.freeClosed
    (ρ := image_env_l (M := rt_model_l C hn) (N := M) Subtype.val (ρ.push ⟨T, hTC⟩))
    (η := (image_env_l (M := rt_model_l C hn) (N := M) Subtype.val ρ).push T)
    (funext (Fin.cases rfl (fun _ => rfl)))).mpr
  exact (jc_cover_sat_l hKP _ T).mpr
    ⟨b, ht A hf.domain b hbA, p, hpT, U, bounds.1, R, bounds.2, hb, hpUR, hm, hx⟩

theorem jc_cover_sound_l (hKP : M.Models KP) {B : M.Domain} (hb : M.TransitiveSet B)
    (hn : Nonempty {x : M.Domain // M.mem x B})
    (ht : ∀ ρ : Env (rt_model_l B hn) 1, ∃ T, jc_cover_s.toUnarySchema.denote ρ T) :
    ∀ x, M.mem x B → Js_access_d B x := by
  intro x hx
  let ρ : Env (rt_model_l B hn) 1 := ⟨fun _ => ⟨x, hx⟩, fun _ => ⟨x, hx⟩⟩
  obtain ⟨T, hT⟩ := ht ρ
  have hm := (rt_model_delta_l hb hn jc_cover_s.delta0 (ρ.push T)).mp hT
  have hm' : jc_cover_s.toUnarySchema.denote (image_env_l (M := rt_model_l B hn) (N := M) Subtype.val ρ) T.val :=
    (Formula.closed_env_l _ jc_cover_s.freeClosed (funext (Fin.cases rfl (fun _ => rfl)))).mp hm
  obtain ⟨a, _, p, _, U, hUT, R, _, ha, hp, hw, hxU⟩ := (jc_cover_sat_l hKP _ T.val).mp hm'
  have state := (js_state_env_l (js_env_l x) a p).mp ((S1_binary.sat_l _ _ a p).mpr ⟨T.val, hw⟩)
  exact ⟨a, U, R, ha, ⟨p, state, hp⟩, hb T.val T.property U hUT, hxU⟩

end YesMetaZFC.SetTheory.InnerModel
