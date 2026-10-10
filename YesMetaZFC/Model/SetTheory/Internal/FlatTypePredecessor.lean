import YesMetaZFC.Model.SetTheory.Internal.FlatTypeQuery
import YesMetaZFC.Model.SetTheory.Internal.TransitiveRecursion

/-! # 由当前最大序数自动读取完整前驱类型

原公式自行找到前一层与规范解码层。候选类型以原查询域为界，
所有查询均使用同一个平坦实现元组，包括全部内部非标准公式码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tf_prev_s : UnarySchema 4 where
  body := set[5] ⟪∃ ν X Z, ⌜sv_max_m⌝ₚ(ν) ∧ ⌜v_m FlatPairing.convention⌝ₚ(ν, X) ∧
    ⌜v_m FlatPairing.convention⌝ₚ(⌜(.bound 3 : Term 5)⌝ₛ, Z) ∧
    ⌜tf_query_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, X, Z, ⌜(.bound 2 : Term 5)⌝ₛ,
      ⌜(.bound 1 : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ, ⌜(.newest : Term 5)⌝ₛ)⟫

def tf_prev_m {d} (ω δ n h p : Term d) : Formula 1 d :=
  pred_m tf_prev_s (Fin.cases h (Fin.cases n (Fin.cases δ (fun _ => ω)))) p

@[simp] theorem tf_prev_closed_l {d} (ω δ n h p : Term d)
    (hω : ω.freeSupport = []) (hδ : δ.freeSupport = []) (hn : n.freeSupport = [])
    (hh : h.freeSupport = []) (hp : p.freeSupport = []) : (tf_prev_m ω δ n h p).FreeClosed :=
  pred_m_freeClosed tf_prev_s _ _ (Fin.cases hh (Fin.cases hn (Fin.cases hδ (fun _ => hω)))) hp

variable (hZF : M.Models ZF) {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω)
  (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) ν X) (hW : V_d (kp_pair_l (ZF.modelsKP hZF)) μ Y)
  (hs : M.SuccessorOf μ ν) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "T" => ZF.v_transitive_l Q hZF hW
local notation "nz" => Nonempty.intro (Subtype.mk ω hωY)
local notation "N" => rt_model_l Y nz
local notation "J" => fp_rank_interpretation_l Q hZF hω hW hωY

include hω hV hW hs in
private theorem tf_prev_values_l (n h δ p : (N).Domain) {Z c R s U D : M.Domain}
    (hZ : V_d Q δ.val Z) (hδ : M.IsLimitOrdinal δ.val) (hωδ : M.mem ω δ.val)
    (hm : Smem_d Q c X R) (hn : M.mem n.val ω) (tuple : Fn0_d n.val X s)
    (point : M.mem δ.val X) (constants : M.MemberSubset U X)
    (pool : Tt_pool_d Q ω n.val U D) (hp : M.mem p.val D) (hpZ : M.mem p.val Z)
    (agree : Sx_graph_d Q K s h.val) :
    tf_prev_s.denote (⟨Fin.cases h (Fin.cases n (Fin.cases δ (fun _ => ⟨ω, hωY⟩))), fun _ => h⟩ : Env N 4) p ↔
      Tt_query_d Q ω c n.val s δ.val p.val := by
  let ρ : Env N 5 := ⟨Fin.cases p (Fin.cases h (Fin.cases n (Fin.cases δ (fun _ => ⟨ω, hωY⟩)))), fun _ => h⟩
  change Formula.satisfies ρ tf_prev_s.body ↔ _
  simp only [tf_prev_s, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, sv_max_sat_l,
    v_sat_l J (rt_model_ext_l hZF.1 T nz)]
  constructor
  · rintro ⟨η, A, B, greatest, layer, decode, truth⟩
    have eqη := (sv_max_rank_l Q hZF hV hW hs hωY η).mp greatest
    have layer' := (rt_fp_v_l Q hZF hω hW hωY hV hs η A).mp layer
    have eqA := ZF.v_unique_l Q hZF (eqη ▸ layer') hV
    have decode' := (rt_fp_v_l Q hZF hω hW hωY hV hs δ B).mp decode
    have eqB := ZF.v_unique_l Q hZF decode' hZ
    exact (tf_query_source_l hZF hω hW hs hωY (((ρ.push η).push A).push B)
      (.bound 7) (.bound 1) .newest (.bound 5) (.bound 4) (.bound 6) (.bound 3) rfl
      (eqA.symm ▸ hV) decode' hδ hωδ (eqA.symm ▸ hm) hn (eqA.symm ▸ tuple)
      (eqA.symm ▸ point) (eqA.symm ▸ constants) pool hp (eqB.symm ▸ hpZ) agree).mp truth
  · intro truth
    let η : (N).Domain := ⟨ν, ZF.v_ordinal_mem_l Q hZF hW hs.predecessor_mem⟩
    let A : (N).Domain := ⟨X, (ZF.v_successor_l Q hZF hV hW hs X).mpr (fun _ h => h)⟩
    let B : (N).Domain := ⟨Z, ZF.v_mem_l Q hZF hZ hW (ZF.v_ordinal_height_l hZF hW hδ.1 δ.property)⟩
    exact ⟨η, A, B, (sv_max_rank_l Q hZF hV hW hs hωY η).mpr rfl,
      (rt_fp_v_l Q hZF hω hW hωY hV hs η A).mpr hV,
      (rt_fp_v_l Q hZF hω hW hωY hV hs δ B).mpr hZ,
      (tf_query_source_l hZF hω hW hs hωY (((ρ.push η).push A).push B)
        (.bound 7) (.bound 1) .newest (.bound 5) (.bound 4) (.bound 6) (.bound 3) rfl
        hV hZ hδ hωδ hm hn tuple point constants pool hp hpZ agree).mpr truth⟩

include hω hV hW hs in
theorem tf_prev_source_l {d} (ρ : Env N d) (w δ n h p : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {Z c R s U D : M.Domain} (hZ : V_d Q (δ.eval ρ).val Z)
    (hδ : M.IsLimitOrdinal (δ.eval ρ).val) (hωδ : M.mem ω (δ.eval ρ).val)
    (hm : Smem_d Q c X R) (hn : M.mem (n.eval ρ).val ω) (tuple : Fn0_d (n.eval ρ).val X s)
    (point : M.mem (δ.eval ρ).val X) (constants : M.MemberSubset U X)
    (pool : Tt_pool_d Q ω (n.eval ρ).val U D) (hp : M.mem (p.eval ρ).val D) (hpZ : M.mem (p.eval ρ).val Z)
    (agree : Sx_graph_d Q K s (h.eval ρ).val) : Formula.satisfies ρ (tf_prev_m w δ n h p) ↔
      Tt_query_d Q ω c (n.eval ρ).val s (δ.eval ρ).val (p.eval ρ).val := by
  have env : (Definitional.Env.substitute ρ (Fin.cases p (Fin.cases h (Fin.cases n (Fin.cases δ (fun _ => w)))))).bound =
      ((⟨Fin.cases (h.eval ρ) (Fin.cases (n.eval ρ) (Fin.cases (δ.eval ρ) (fun _ => ⟨ω, hωY⟩))),
        fun _ => h.eval ρ⟩ : Env N 4).push (p.eval ρ)).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw)))) i
  exact (Formula.satisfies_bind _ _ _).trans
    ((Formula.closed_env_l tf_prev_s.body tf_prev_s.freeClosed env).trans
      (tf_prev_values_l hZF hω hV hW hs hωY (n.eval ρ) (h.eval ρ) (δ.eval ρ) (p.eval ρ)
        hZ hδ hωδ hm hn tuple point constants pool hp hpZ agree))

def tf_type_m {d} (ω δ n h D t : Term d) : Formula 1 d := set[d] ⟪
  ⌜t⌝ₛ ⊆ ⌜D⌝ₛ ∧ (∀ p ∈ ⌜D⌝ₛ, p ∈ ⌜t⌝ₛ ↔ ⌜tf_prev_m⌝ₚ(⌜ω⌝ₛ, ⌜δ⌝ₛ, ⌜n⌝ₛ, ⌜h⌝ₛ, p))⟫
derive_free_closed tf_type_m

include hω hV hW hs in
theorem tf_type_source_l {d} (ρ : Env N d) (w δ n h D t : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {Z c R s U : M.Domain} (hZ : V_d Q (δ.eval ρ).val Z)
    (hδ : M.IsLimitOrdinal (δ.eval ρ).val) (hωδ : M.mem ω (δ.eval ρ).val)
    (hm : Smem_d Q c X R) (hn : M.mem (n.eval ρ).val ω) (tuple : Fn0_d (n.eval ρ).val X s)
    (point : M.mem (δ.eval ρ).val X) (constants : M.MemberSubset U X)
    (pool : Tt_pool_d Q ω (n.eval ρ).val U (D.eval ρ).val) (hD : M.mem (D.eval ρ).val Z)
    (agree : Sx_graph_d Q K s (h.eval ρ).val) : Formula.satisfies ρ (tf_type_m w δ n h D t) ↔
      Tt_truth_d Q ω c (n.eval ρ).val s (δ.eval ρ).val (D.eval ρ).val (t.eval ρ).val := by
  have read (p : (N).Domain) (hp : M.mem p.val (D.eval ρ).val) :
      Formula.satisfies (ρ.push p) (tf_prev_m w.weaken δ.weaken n.weaken h.weaken .newest) ↔
        Tt_query_d Q ω c (n.eval ρ).val s (δ.eval ρ).val p.val := by
    have q := tf_prev_source_l hZF hω hV hW hs hωY (ρ.push p) w.weaken δ.weaken n.weaken h.weaken .newest
    simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at q
    exact q hw hZ hδ hωδ hm hn tuple point constants pool hp
      (ZF.v_transitive_l Q hZF hZ (D.eval ρ).val hD p.val hp) agree
  simp only [tf_type_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨sub, matrix⟩ p
    constructor
    · intro hp
      let q : (N).Domain := ⟨p, T (t.eval ρ).val (t.eval ρ).property p hp⟩
      have hpD := sub q hp
      exact ⟨hpD, (read q hpD).mp ((matrix q hpD).mp hp)⟩
    · rintro ⟨hpD, truth⟩
      let q : (N).Domain := ⟨p, T (D.eval ρ).val (D.eval ρ).property p hpD⟩
      exact (matrix q hpD).mpr ((read q hpD).mpr truth)
  · intro truth
    exact ⟨fun p hp => ((truth p.val).mp hp).1, fun p hp =>
      (truth p.val).trans ((and_iff_right hp).trans (read p hp).symm)⟩

end YesMetaZFC.SetTheory.Internal
