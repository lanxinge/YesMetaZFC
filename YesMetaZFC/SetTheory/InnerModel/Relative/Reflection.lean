import YesMetaZFC.SetTheory.InnerModel.Relative.Relativization
import YesMetaZFC.Model.SetTheory.LevyReflection.Closure

/-! # 相对 J 层上的有限公式反射

背景反射同时封闭后继、带基集的层值和成员的层号见证。反射域的相对 J 部分
由同一递归唯一性识别为实际极限层；基集始终作为内部参数保留。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (S : M.Domain)

def ja_succ_s : UnarySchema 1 := { body := KP.succ0_m .newest (.bound 1) }
def ja_stage_s : UnarySchema 2 := { body := ja_value_m (.bound 2) (.bound 1) .newest }
def ja_index_query_s : UnarySchema 2 := { body := ja_index_s.body, freeClosed := ja_index_s.freeClosed }
def ja_cut_queries_l : Lr_family := [⟨1, ja_succ_s⟩, ⟨2, ja_stage_s⟩, ⟨2, ja_index_query_s⟩]

theorem ja_cut_l (hM : M.Models KPi) {V} (ht : M.TransitiveSet V) (hSV : M.mem S V)
    (he : ∃ e, (∀ x, ¬ M.mem x e) ∧ M.mem e V) (hc : Lr_step_d ja_cut_queries_l V V) :
    ∃ a U, Ja_d S a U ∧ ∀ x, M.mem x U ↔ M.mem x V ∧ La_d S x := by
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
    obtain ⟨t, htV, hp⟩ := hc ⟨1, ja_succ_s⟩ (by simp [ja_cut_queries_l]) ρ
      (fun _ => ((ha b).mp hb).1) ⟨s, (KP.succ0_sat_l hKP.1 (ρ.push s) .newest (.bound 1)).mpr hs⟩
    have hts := (KP.succ0_sat_l hKP.1 (ρ.push t) .newest (.bound 1)).mp hp
    change M.SuccessorOf t b at hts
    have eq := Structure.SuccessorOf.eq hKP.1 hts hs
    exact ⟨t, (ha t).mpr ⟨htV, eq.symm ▸ ho⟩, hts.predecessor_mem⟩
  obtain ⟨e, hem, heV⟩ := he
  have hl : M.IsLimitOrdinal a := ⟨hoa, ⟨e, (ha e).mpr ⟨heV, Structure.IsOrdinal.of_no_members hem⟩⟩, hs⟩
  have stage b (hb : M.mem b V) : ∃ Y, M.mem Y V ∧ Ja_value_d S b Y := by
    obtain ⟨Y, hy⟩ := ja_value_exists_l S hM b
    let ρ := (ja_env_l S).push b
    obtain ⟨Z, hz, hp⟩ := hc ⟨2, ja_stage_s⟩ (by simp [ja_cut_queries_l]) ρ
      (Fin.cases hb (fun _ => hSV)) ⟨Y, (ja_value_sat_l (ρ.push Y) (.bound 2) (.bound 1) .newest).mpr hy⟩
    exact ⟨Z, hz, (ja_value_sat_l (ρ.push Z) (.bound 2) (.bound 1) .newest).mp hp⟩
  obtain ⟨U, hu⟩ := ja_value_exists_l S hM a
  refine ⟨a, U, ⟨hoa, hu⟩, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨b, hb, Y, hy, hx⟩ := (ja_limit_l S hM hl hu x).mp hx
    obtain ⟨Z, hz, hp⟩ := stage b ((ha b).mp hb).1
    have hyV : M.mem Y V := (ja_value_unique_l S hM hy hp).symm ▸ hz
    exact ⟨ht Y hyV x hx, b, Y, ⟨((ha b).mp hb).2, hy⟩, hx⟩
  · rintro ⟨hxV, b, Y, hb, hxY⟩
    let ρ := (ja_env_l S).push x
    obtain ⟨c, hcV, hp⟩ := hc ⟨2, ja_index_query_s⟩ (by simp [ja_cut_queries_l]) ρ
      (Fin.cases hxV (fun _ => hSV)) ⟨b, (ja_index_sat_l hKP (ja_env_l S) x b).mpr ⟨Y, hb, hxY⟩⟩
    obtain ⟨Z, hz, hx⟩ := (ja_index_sat_l hKP (ja_env_l S) x c).mp hp
    exact (ja_limit_l S hM hl hu x).mpr ⟨c, (ha c).mpr ⟨hcV, hz.1⟩, Z, hz.2, hx⟩

def ja_query_s {n} (φ : UnarySchema n) : UnarySchema (n+1) := {
  body := .conj (la_m (.bound 1) .newest)
    (la_rel_m φ.body (.bound 1) (Fin.cases .newest (fun i => .bound ⟨i.val+2, by omega⟩)))
  freeClosed := by
    simp only [Definitional.Formula.FreeClosed]
    exact ⟨la_m_freeClosed _ _ rfl rfl,
      la_rel_closed_l _ φ.freeClosed _ _ rfl (Fin.cases rfl (fun _ => rfl))⟩ }
def ja_queries_l (Φ : Lr_family) : Lr_family := Φ.map (fun q => ⟨q.1+1, ja_query_s q.2⟩)

theorem ja_query_sat_l (hM : M.Models KPi) (hS : M.TransitiveSet S) {n} (φ : UnarySchema n)
    (ρ : Env (la_model_l S hM) n) (x : (la_model_l S hM).Domain) :
    (ja_query_s φ).denote ((image_env_l (N := M) Subtype.val ρ).push S) x.val ↔ φ.denote ρ x := by
  let η := (image_env_l (N := M) Subtype.val ρ).push S
  let e : Fin (n+1) → Term (n+2) := Fin.cases .newest (fun i => .bound ⟨i.val+2, by omega⟩)
  have tr := la_rel_sat_l hM S hS φ.body φ.freeClosed (ρ.push x) (η.push x.val) (.bound 1) e
    rfl (Fin.cases rfl (fun _ => rfl))
  rw [ja_query_s, UnarySchema.denote, Formula.satisfies_conj_iff, la_sat_l (KPi.models_iff_l.mp hM).1]
  exact (and_iff_right x.property).trans tr

theorem ja_closed_layer_l (hZF : M.Models ZF) (hS : M.TransitiveSet S) (Φ : Lr_family)
    (A : (la_model_l S (ZF.models_kpi_l hZF)).Domain) :
    ∃ a, ∃ U : (la_model_l S (ZF.models_kpi_l hZF)).Domain, Ja_d S a U.val ∧
      M.mem A.val U.val ∧ Lr_step_d Φ U U := by
  let hM := ZF.models_kpi_l hZF
  let hKP := ZF.modelsKP hZF
  let N := la_model_l S hM
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  obtain ⟨P, hp⟩ := kp_finite_cover_l hKP [A.val, S, e]
  obtain ⟨_, V, hv, hpV, hc⟩ := ZF.lr_closed_layer_l (kp_pair_l hKP) hZF hω
    (ja_cut_queries_l ++ ja_queries_l Φ) P
  have ht := ZF.v_transitive_l (kp_pair_l hKP) hZF hv
  have hSV := ht P hpV S (hp S (by simp)).2
  obtain ⟨a, U, ha, hcut⟩ := ja_cut_l S hM ht hSV
    ⟨e, he, ht P hpV e (hp e (by simp)).2⟩ (fun q hq => hc q (List.mem_append_left _ hq))
  let W : N.Domain := ⟨U, la_layer_l S hM ha⟩
  refine ⟨a, W, ha, (hcut A.val).mpr ⟨ht P hpV A.val (hp A.val (by simp)).2, A.property⟩, ?_⟩
  intro q hq ρ hρ hx
  let η := (image_env_l (M := N) (N := M) Subtype.val ρ).push S
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hyV, hy⟩ := hc ⟨q.1+1, ja_query_s q.2⟩
    (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)) η
    (Fin.cases hSV (fun i => ((hcut _).mp (hρ i)).1))
    ⟨x.val, (ja_query_sat_l S hM hS q.2 ρ x).mpr hx⟩
  have hyL : La_d S y := by
    have h := (Formula.satisfies_conj_iff _ _ _).mp hy
    exact (la_sat_l hKP (η.push y) (.bound 1) .newest).mp h.1
  exact ⟨⟨y, hyL⟩, (hcut y).mpr ⟨hyV, hyL⟩, (ja_query_sat_l S hM hS q.2 ρ ⟨y, hyL⟩).mp hy⟩

end YesMetaZFC.SetTheory.InnerModel.Relative
