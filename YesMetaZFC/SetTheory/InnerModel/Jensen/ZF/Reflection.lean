import YesMetaZFC.SetTheory.InnerModel.Jensen.Constructibility
import YesMetaZFC.Model.SetTheory.LevyReflection.Closure

/-! # 从背景反射层取得 J 的有限见证闭包

反射层先对后继、J 层值和构造证书封闭，再证明其中的 J 部分恰为一个 J 极限层。
任意有限族的 J 见证查询同时纳入背景反射，因而无需重新选择或外部迭代模型对象。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def jl_successor_s : UnarySchema 1 := { body := KP.succ0_m .newest (.bound 1) }
def jl_stage_s : UnarySchema 1 := { body := jh_value_m (.bound 1) .newest }
def jl_certificate_s : UnarySchema 1 := { body := l0_m .newest (.bound 1) }
def jl_cut_queries_l : Lr_family := [⟨1, jl_successor_s⟩, ⟨1, jl_stage_s⟩, ⟨1, jl_certificate_s⟩]

theorem jl_cut_l (hM : M.Models KPi) {V : M.Domain} (ht : M.TransitiveSet V)
    (he : ∃ e, (∀ x, ¬ M.mem x e) ∧ M.mem e V) (hc : Lr_step_d jl_cut_queries_l V V) :
    ∃ a U, J_d a U ∧ ∀ x, M.mem x U ↔ M.mem x V ∧ L_d x := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let φ : Delta0UnarySchema 0 := { body := KP.ord0_m .newest, delta0 := KP.ord0_delta_l _ }
  obtain ⟨a, ha'⟩ := KP.separation_exists_d hKP φ (jh_env_l V) V
  have ha b : M.mem b a ↔ M.mem b V ∧ M.IsOrdinal b :=
    (ha' b).trans (and_congr_right fun _ => KP.ord0_sat_l hKP _ _)
  have hta : M.TransitiveSet a := fun b hb c hcb =>
    (ha c).mpr ⟨ht b ((ha b).mp hb).1 c hcb, ((ha b).mp hb).2.mem hcb⟩
  have hoa := KP.ordinal_of_transitive_l hKP hta (fun b hb => ((ha b).mp hb).2)
  have hs b (hb : M.mem b a) : ∃ s, M.mem s a ∧ M.mem b s := by
    obtain ⟨s, ho, hs⟩ := KP.ordinal_successor_l hKP ((ha b).mp hb).2
    let ρ := rd_seed_env_l b
    obtain ⟨t, htV, hp⟩ := hc ⟨1, jl_successor_s⟩ (by simp [jl_cut_queries_l]) ρ
      (fun _ => ((ha b).mp hb).1) ⟨s, (KP.succ0_sat_l hKP.1 (ρ.push s) .newest (.bound 1)).mpr hs⟩
    have hts := (KP.succ0_sat_l hKP.1 (ρ.push t) .newest (.bound 1)).mp hp
    change M.SuccessorOf t b at hts
    have heq := Structure.SuccessorOf.eq hKP.1 hts hs
    exact ⟨t, (ha t).mpr ⟨htV, heq.symm ▸ ho⟩, hts.predecessor_mem⟩
  obtain ⟨e, hem, heV⟩ := he
  have hl : M.IsLimitOrdinal a := ⟨hoa, ⟨e, (ha e).mpr ⟨heV, Structure.IsOrdinal.of_no_members hem⟩⟩, hs⟩
  have stage b (hb : M.mem b V) : ∃ Y, M.mem Y V ∧ Jh_value_d b Y := by
    obtain ⟨Y, hy⟩ := jh_value_exists_l hM b
    let ρ := rd_seed_env_l b
    obtain ⟨Z, hz, hp⟩ := hc ⟨1, jl_stage_s⟩ (by simp [jl_cut_queries_l]) ρ (fun _ => hb)
      ⟨Y, (jh_value_sat_l (ρ.push Y) (.bound 1) .newest).mpr hy⟩
    exact ⟨Z, hz, (jh_value_sat_l (ρ.push Z) (.bound 1) .newest).mp hp⟩
  obtain ⟨U, hu⟩ := jh_value_exists_l hM a
  refine ⟨a, U, ⟨hoa, hu⟩, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨b, hb, Y, hy, hx⟩ := (jh_limit_l hM hl hu x).mp hx
    obtain ⟨Z, hz, hp⟩ := stage b ((ha b).mp hb).1
    have hyV : M.mem Y V := (jh_value_unique_l hM hy hp).symm ▸ hz
    exact ⟨ht Y hyV x hx, b, Y, ⟨((ha b).mp hb).2, hy⟩, hx⟩
  · rintro ⟨hxV, hx⟩
    obtain ⟨T, hT⟩ := (l_witness_l hKP.1 x).mp hx
    let ρ := rd_seed_env_l x
    obtain ⟨W, hwV, hp⟩ := hc ⟨1, jl_certificate_s⟩ (by simp [jl_cut_queries_l]) ρ (fun _ => hxV)
      ⟨T, (l0_sat_l hKP (ρ.push T) .newest (.bound 1)).mpr hT⟩
    obtain ⟨b, Y, hb, _, ho, hxY, A, F, hf, hA, hF⟩ :=
      (l0_sat_l hKP (ρ.push W) .newest (.bound 1)).mp hp
    exact (jh_limit_l hM hl hu x).mpr ⟨b, (ha b).mpr ⟨ht W hwV b hb, ho⟩, Y,
      (rc_value_sat_l hKP.1 ..).mpr ⟨W, A, F, hf, hA, hF⟩, hxY⟩

def jl_query_s {n} (φ : UnarySchema n) : UnarySchema n := {
  body := .conj (l_m .newest) (l_rel_m φ.body)
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, φ.freeClosed] }
def jl_queries_l (Φ : Lr_family) : Lr_family := Φ.map (fun q => ⟨q.1, jl_query_s q.2⟩)

theorem jl_query_sat_l (hKP : M.Models KP) {n} (φ : UnarySchema n) (ρ : Env M n) (x : M.Domain) :
    (jl_query_s φ).denote ρ x ↔ L_d x ∧ Formula.satisfies (ρ.push x) (l_rel_m φ.body) := by
  simp only [jl_query_s, UnarySchema.denote, Formula.satisfies_conj_iff, l_sat_l hKP,
    Definitional.Term.eval_newest]

theorem jl_step_transfer_l (hM : M.Models KPi) {V : M.Domain} {U : (l_model_l hM).Domain}
    (hcut : ∀ x, M.mem x U.val ↔ M.mem x V ∧ L_d x) {Φ : Lr_family}
    (hc : Lr_step_d (jl_queries_l Φ) V V) : Lr_step_d (M := l_model_l hM) Φ U U := by
  intro q hq ρ hρ hx
  let η := image_env_l (M := l_model_l hM) (N := M) Subtype.val ρ
  have tr (x : (l_model_l hM).Domain) : q.2.denote ρ x ↔ Formula.satisfies (η.push x.val) (l_rel_m q.2.body) := by
    have h := l_rel_sat_l hM q.2.body (ρ.push x)
    rw [image_env_push_l (M := l_model_l hM) (N := M) Subtype.val ρ x] at h
    exact h
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hyV, hy⟩ := hc ⟨q.1, jl_query_s q.2⟩ (List.mem_map.mpr ⟨q, hq, rfl⟩) η
    (fun i => ((hcut _).mp (hρ i)).1)
    ⟨x.val, (jl_query_sat_l (KPi.models_iff_l.mp hM).1 q.2 η x.val).mpr ⟨x.property, (tr x).mp hx⟩⟩
  have hy := (jl_query_sat_l (KPi.models_iff_l.mp hM).1 q.2 η y).mp hy
  exact ⟨⟨y, hy.1⟩, (hcut y).mpr ⟨hyV, hy.1⟩, (tr ⟨y, hy.1⟩).mpr hy.2⟩

/-- 任意有限原公式见证族都在包含指定 J 对象的实际 J 层上闭合。 -/
theorem jl_closed_layer_l (hZF : M.Models ZF) (Φ : Lr_family)
    (A : (l_model_l (ZF.models_kpi_l hZF)).Domain) :
    ∃ a, ∃ U : (l_model_l (ZF.models_kpi_l hZF)).Domain, J_d a U.val ∧
      (l_model_l (ZF.models_kpi_l hZF)).mem A U ∧ Lr_step_d Φ U U := by
  let hM := ZF.models_kpi_l hZF
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  obtain ⟨P, hp⟩ := KP.exists_pair hKP A.val e
  obtain ⟨_, V, hv, hpV, hc⟩ := ZF.lr_closed_layer_l I hZF hω (jl_cut_queries_l ++ jl_queries_l Φ) P
  have ht := ZF.v_transitive_l I hZF hv
  obtain ⟨a, U, ha, hcut⟩ := jl_cut_l hM ht ⟨e, he, ht P hpV e ((hp e).mpr (Or.inr rfl))⟩
    (fun q hq => hc q (List.mem_append_left _ hq))
  let W : (l_model_l hM).Domain := ⟨U, l_layer_l hM ha⟩
  exact ⟨a, W, ha, (hcut A.val).mpr ⟨ht P hpV A.val ((hp A.val).mpr (Or.inl rfl)), A.property⟩,
    jl_step_transfer_l hM (U := W) hcut (fun q hq => hc q (List.mem_append_right _ hq))⟩

end YesMetaZFC.SetTheory.InnerModel
