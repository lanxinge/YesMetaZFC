import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Types.FlatTypePredecessor

/-! # 任意较低秩层中完整类型的原公式

公式在外层构造常量域和全部原查询，在指定较低层中逐查询读取真值。
解码层独立于指定常量 δ；整个候选类型无需降入较低层或其幂集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tf_lower_type_s : UnarySchema 7 where
  body := set[8] ⟪∃ B, ⌜v_m FlatPairing.convention⌝ₚ(⌜(.bound 5 : Term 8)⌝ₛ, B) ∧
    (∃ U ∈ ⌜(.bound 6 : Term 8)⌝ₛ, ∃ D ∈ ⌜(.bound 6 : Term 8)⌝ₛ,
      ⌜tt_constants0_m⌝ₚ(⌜(.bound 5 : Term 8)⌝ₛ, B, U) ∧
      ⌜tt_pool0_m⌝ₚ(⌜(.bound 7 : Term 8)⌝ₛ, ⌜(.bound 6 : Term 8)⌝ₛ, ⌜(.bound 4 : Term 8)⌝ₛ, U, D) ∧
      ⌜(.newest : Term 8)⌝ₛ ⊆ D ∧ (∀ p ∈ D, p ∈ ⌜(.newest : Term 8)⌝ₛ ↔
        ⌜tf_query_m⌝ₚ(⌜(.bound 7 : Term 8)⌝ₛ, ⌜(.bound 3 : Term 8)⌝ₛ, ⌜(.bound 6 : Term 8)⌝ₛ,
          ⌜(.bound 4 : Term 8)⌝ₛ, ⌜(.bound 2 : Term 8)⌝ₛ, ⌜(.bound 1 : Term 8)⌝ₛ, p)))⟫

def tf_lower_type_m {d} (ω C τ n A h δ t : Term d) : Formula 1 d :=
  pred_m tf_lower_type_s (Fin.cases δ (Fin.cases h (Fin.cases A (Fin.cases n (Fin.cases τ
    (Fin.cases C (fun _ => ω))))))) t

@[simp] theorem tf_lower_type_closed_l {d} (ω C τ n A h δ t : Term d)
    (hw : ω.freeSupport = []) (hc : C.freeSupport = []) (ht : τ.freeSupport = []) (hn : n.freeSupport = [])
    (ha : A.freeSupport = []) (hh : h.freeSupport = []) (hd : δ.freeSupport = []) (hu : t.freeSupport = []) :
    (tf_lower_type_m ω C τ n A h δ t).FreeClosed :=
  pred_m_freeClosed tf_lower_type_s _ _ (Fin.cases hd (Fin.cases hh (Fin.cases ha
    (Fin.cases hn (Fin.cases ht (Fin.cases hc (fun _ => hw))))))) hu

variable (hZF : M.Models ZF) {ω η Y : M.Domain} (hω : M.IsOmega ω)
  (hY : V_d (kp_pair_l (ZF.modelsKP hZF)) η Y) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "ny" => Nonempty.intro (Subtype.mk ω hωY)
local notation "N" => rt_model_l Y ny
local notation "J" => fp_rank_interpretation_l Q hZF hω hY hωY

include hω hY in
private theorem tf_lower_type_values_l (C τ n A h δ t : (N).Domain) {ξ ν B U D c R s : M.Domain}
    (hC : V_d Q ξ C.val) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ) (hτξ : M.mem τ.val ξ)
    (hA : V_d Q ν A.val) (hων : M.MemberSubset ω ν) (hτA : M.mem τ.val A.val)
    (hB : V_d Q τ.val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = τ.val)
    (pool : Tt_pool_d Q ω n.val U D) (hm : Smem_d Q c A.val R) (hn : M.mem n.val ω)
    (tuple : Fn0_d n.val A.val s) (point : M.mem δ.val A.val) (agree : Sx_graph_d Q K s h.val) :
    Formula.satisfies (⟨Fin.cases t (Fin.cases δ (Fin.cases h (Fin.cases A (Fin.cases n (Fin.cases τ
      (Fin.cases C (fun _ => ⟨ω, hωY⟩))))))), fun _ => h⟩ : Env N 8) tf_lower_type_s.body ↔
        Tt_truth_d Q ω c n.val s δ.val D t.val := by
  let ρ : Env N 8 := ⟨Fin.cases t (Fin.cases δ (Fin.cases h (Fin.cases A (Fin.cases n (Fin.cases τ
    (Fin.cases C (fun _ => ⟨ω, hωY⟩))))))), fun _ => h⟩
  have ht := v_transitive_l Q hY
  have ct := v_transitive_l Q hC
  have hwC := ZF.v_ordinal_mem_l Q hZF hC hωξ
  have huC := tt_constants_rank_l hZF hC hξ hτξ hB constants
  have hdC := pool.rank_mem_l (ZF.modelsKP hZF) hω hC hξ hwC hn huC
  have ba := ZF.v_mono_l Q hZF hB hA ((v_ordinal_l Q hA).transitive τ.val (ZF.v_ordinal_height_l hZF hA (v_ordinal_l Q hB) hτA))
  have ua : M.MemberSubset U A.val := fun x hx => ((constants x).mp hx).elim (ba x) (fun eq => eq.symm ▸ hτA)
  have const (B' U' D' : (N).Domain) :
      Formula.satisfies (((ρ.push B').push U').push D') (tt_constants0_m (.bound 8) (.bound 2) (.bound 1)) ↔
      ∀ x, M.mem x U'.val ↔ M.mem x B'.val ∨ x = τ.val :=
    (rt_model_delta_l ht ny (tt_constants0_delta_l ..) _).trans (tt_constants0_sat_l hZF.1 _ _ _ _)
  have pools (B' U' D' : (N).Domain) (hu : M.mem U'.val C.val) :
      Formula.satisfies (((ρ.push B').push U').push D') (tt_pool0_m (.bound 10) (.bound 9) (.bound 7) (.bound 1) .newest) ↔
      Tt_pool_d Q ω n.val U'.val D'.val :=
    (rt_model_delta_l ht ny (tt_pool0_delta_l ..) _).trans
      (tt_pool0_rank_l hZF _ _ _ _ _ _ hω hC hξ hwC hn hu)
  have query (B' U' D' p : (N).Domain) (hp : M.mem p.val D) :=
    tf_query_source_l hZF hω hY hωY ((((ρ.push B').push U').push D').push p)
      (.bound 11) (.bound 7) (.bound 10) (.bound 8) (.bound 6) (.bound 5) .newest rfl
      hA hων hC hξ hωξ hm hn tuple point ua pool hp (ct D hdC p.val hp) agree
  simp only [tf_lower_type_s, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_existsMem_iff, v_sat_l J (rt_model_ext_l hZF.1 ht ny),
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff]
  constructor
  · rintro ⟨B', hb, U', hu, D', _, hc, hd, sub, truth⟩
    have eb := ZF.v_unique_l Q hZF ((rt_fp_v_l Q hZF hω hY hωY τ B').mp hb) hB
    have eu := hZF.1.eq_of_same_members U'.val U (fun x => (eb ▸ (const B' U' D').mp hc x).trans (constants x).symm)
    have ed := (eu ▸ (pools B' U' D' hu).mp hd).unique_l hZF.1 Q pool
    intro p
    constructor
    · intro hp
      let p' : (N).Domain := ⟨p, ht t.val t.property p hp⟩
      have hd : M.mem p D := ed ▸ (show M.mem p D'.val from sub p' hp)
      exact ⟨hd, (query B' U' D' p' hd).mp ((truth p' (sub p' hp)).mp hp)⟩
    · rintro ⟨hp, hq⟩
      let p' : (N).Domain := ⟨p, ht C.val C.property p (ct D hdC p hp)⟩
      have hd : M.mem p D'.val := ed.symm ▸ hp
      exact (truth p' hd).mpr ((query B' U' D' p' hp).mpr hq)
  · intro truth
    let B' : (N).Domain := ⟨B, ht C.val C.property B (ZF.v_mem_l Q hZF hB hC hτξ)⟩
    let U' : (N).Domain := ⟨U, ht C.val C.property U huC⟩
    let D' : (N).Domain := ⟨D, ht C.val C.property D hdC⟩
    exact ⟨B', (rt_fp_v_l Q hZF hω hY hωY τ B').mpr hB, U', huC, D', hdC,
      (const B' U' D').mpr constants, (pools B' U' D' huC).mpr pool,
      fun p hp => ((truth p.val).mp hp).1,
      fun p hp => (truth p.val).trans ((and_iff_right hp).trans (query B' U' D' p hp).symm)⟩

include hω hY in
theorem tf_lower_type_source_l {d} (ρ : Env N d) (w C τ n A h δ t : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {ξ ν B U D c R s : M.Domain}
    (hC : V_d Q ξ (C.eval ρ).val) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ) (hτξ : M.mem (τ.eval ρ).val ξ)
    (hA : V_d Q ν (A.eval ρ).val) (hων : M.MemberSubset ω ν) (hτA : M.mem (τ.eval ρ).val (A.eval ρ).val)
    (hB : V_d Q (τ.eval ρ).val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = (τ.eval ρ).val)
    (pool : Tt_pool_d Q ω (n.eval ρ).val U D) (hm : Smem_d Q c (A.eval ρ).val R) (hn : M.mem (n.eval ρ).val ω)
    (tuple : Fn0_d (n.eval ρ).val (A.eval ρ).val s) (point : M.mem (δ.eval ρ).val (A.eval ρ).val)
    (agree : Sx_graph_d Q K s (h.eval ρ).val) : Formula.satisfies ρ (tf_lower_type_m w C τ n A h δ t) ↔
      Tt_truth_d Q ω c (n.eval ρ).val s (δ.eval ρ).val D (t.eval ρ).val := by
  have env : (Definitional.Env.substitute ρ (Fin.cases t (Fin.cases δ (Fin.cases h (Fin.cases A (Fin.cases n (Fin.cases τ
      (Fin.cases C (fun _ => w))))))))).bound =
      (⟨Fin.cases (t.eval ρ) (Fin.cases (δ.eval ρ) (Fin.cases (h.eval ρ) (Fin.cases (A.eval ρ) (Fin.cases (n.eval ρ)
        (Fin.cases (τ.eval ρ) (Fin.cases (C.eval ρ) (fun _ => ⟨ω, hωY⟩))))))), fun _ => h.eval ρ⟩ : Env N 8).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw))))))) i
  exact (Formula.satisfies_bind _ _ _).trans ((Formula.closed_env_l tf_lower_type_s.body tf_lower_type_s.freeClosed env).trans
    (tf_lower_type_values_l hZF hω hY hωY (C.eval ρ) (τ.eval ρ) (n.eval ρ) (A.eval ρ) (h.eval ρ) (δ.eval ρ) (t.eval ρ)
      hC hξ hωξ hτξ hA hων hτA hB constants pool hm hn tuple point agree))

end YesMetaZFC.SetTheory.Internal
