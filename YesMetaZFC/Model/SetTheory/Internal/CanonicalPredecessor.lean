import YesMetaZFC.Model.SetTheory.Internal.CanonicalFlat
import YesMetaZFC.Model.SetTheory.Internal.FlatPredecessor
import YesMetaZFC.Model.SetTheory.Internal.CanonicalSatisfaction

/-! # 原自然数公式码在前一秩层中的统一真值

公式只接收 ω、极限序数 δ、原自然数码及平坦赋值。它自行构造 Vδ，
在其中解码原程序，再于当前层的前一秩层求值；没有额外解码表参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_prev_s : UnarySchema 3 where
  body := .conj (.mem (.bound 1) (.bound 3)) (set[4] ⟪
  ∃ Z, ⌜v_m FlatPairing.convention⌝ₚ(⌜(.bound 2 : Term 4)⌝ₛ, Z) ∧
    (∃ G ∈ Z, ∃ n ∈ Z, ∃ r ∈ Z,
      ⌜sc_flat_local_m⌝ₚ(Z, ⌜(.bound 3 : Term 4)⌝ₛ, ⌜(.bound 1 : Term 4)⌝ₛ, G, n, r) ∧
      ⌜ft_prev_m⌝ₚ(⌜(.bound 3 : Term 4)⌝ₛ, G, n, r, ⌜(.newest : Term 4)⌝ₛ))⟫)

def sc_prev_m {d} (ω δ z f : Term d) : Formula 1 d :=
  pred_m sc_prev_s (Fin.cases z (Fin.cases δ (fun _ => ω))) f
@[simp] theorem sc_prev_m_freeClosed {d} (ω δ z f : Term d)
    (hω : ω.freeSupport = []) (hδ : δ.freeSupport = []) (hz : z.freeSupport = [])
    (hf : f.freeSupport = []) : (sc_prev_m ω δ z f).FreeClosed :=
  pred_m_freeClosed sc_prev_s _ _ (Fin.cases hz (Fin.cases hδ (fun _ => hω))) hf

variable (hZF : M.Models ZF) {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
variable (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) ν X)
  (hW : V_d (kp_pair_l (ZF.modelsKP hZF)) μ Y) (hs : M.SuccessorOf μ ν) (hωY : M.mem ω Y)
local notation "T" => ZF.v_transitive_l Q hZF hW
local notation "nz" => Nonempty.intro (Subtype.mk ω hωY)
local notation "N" => rt_model_l Y nz
local notation "J" => fp_rank_interpretation_l Q hZF hω hW hωY

include hω hV hW hs in
private theorem sc_prev_values_l (δ z g : (N).Domain) (hδ : M.IsLimitOrdinal δ.val)
    (hωδ : M.mem ω δ.val) (hz : M.mem z.val ω) {c R f : M.Domain}
    (hm : Smem_d Q c X R) (hf : M.IsSetFunctionFromTo Q f ω X)
    (hg : M.IsSetFunctionFromTo K g.val ω X) (agree : Sx_graph_d Q K f g.val) :
    sc_prev_s.denote (⟨Fin.cases z (Fin.cases δ (fun _ => ⟨ω, hωY⟩)), fun _ => g⟩ : Env N 3) g ↔
      Sc_sat_d Q ω c z.val f := by
  let ρ : Env N 4 := ⟨Fin.cases g (Fin.cases z (Fin.cases δ (fun _ => ⟨ω, hωY⟩))), fun _ => g⟩
  have hων : M.MemberSubset ω ν := by
    rcases (hs ω).mp (ZF.v_ordinal_height_l hZF hW (hω.isOrdinal hZF) hωY) with lt | eq
    · exact (v_ordinal_l Q hV).transitive ω lt
    · exact fun i hi => (eq i).mp hi
  obtain ⟨b, S, _, _, model⟩ := fp_model_rank_l Q hZF hω hV hW hs hων
  -- 有界解码公式先穿过外层 Y，再由实际 Vδ 的绝对性恢复原规范编码。
  have decode (A G n r : (N).Domain) (layer : V_d Q δ.val A.val)
      (hG : M.mem G.val A.val) (hn : M.mem n.val A.val) (hr : M.mem r.val A.val) :
      Formula.satisfies ((((ρ.push A).push G).push n).push r)
        (sc_flat_local_m (.bound 3) (.bound 7) (.bound 5) (.bound 2) (.bound 1) .newest) ↔
          Sc_flat_d Q K ω z.val G.val n.val r.val := by
    have hw := ZF.v_ordinal_mem_l Q hZF layer hωδ
    exact (rt_model_delta_l T nz (sc_flat_local_delta_l ..) _).trans
      (sc_flat_local_sat_l hZF hω hδ layer hw _ _ _ _ _ _ _ rfl rfl
        (ZF.v_transitive_l Q hZF layer ω hw z.val hz) hG hn hr)
  change Formula.satisfies ρ sc_prev_s.body ↔ _
  simp only [sc_prev_s, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff,
    v_sat_l J (rt_model_ext_l hZF.1 T nz), ft_prev_sat_l J (rt_model_ext_l hZF.1 T nz),
    Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨_, A, layer, G, hG, n, hn, r, hr, code, truth⟩
    have layer' := (rt_fp_v_l Q hZF hω hW hωY hV hs δ A).mp layer
    obtain ⟨a, F, num, form, recode⟩ := (decode A G n r layer' hG hn hr).mp code
    obtain ⟨v, hv⟩ := (K).total G.val r.val
    have flat : Sformula_d K ω v n.val G.val r.val := ⟨hv, recode.program_l Q K form.2.1, form.2.2⟩
    exact ⟨a, num, (recode.satisfies_l Q K hZF hm model form hv hf hg agree).mpr
      ((ft_prev_source_l Q hZF hω hV hW hs hων hωY G n r g model flat hg).mp truth)⟩
  · rintro ⟨a, num, truth⟩
    have data := num
    obtain ⟨n, F, r, _, _, form, _⟩ := data
    obtain ⟨G, recode⟩ := sx_program_exists_l Q K hZF hω form.2.1
    obtain ⟨A, layer⟩ := ZF.v_exists_l Q hZF hδ.1
    have hA := ZF.v_mem_l Q hZF layer hW (ZF.v_ordinal_height_l hZF hW hδ.1 δ.property)
    have hw := ZF.v_ordinal_mem_l Q hZF layer hωδ
    have hn := ZF.v_transitive_l Q hZF layer ω hw n form.2.1.1
    have hr := ZF.v_transitive_l Q hZF layer n hn r form.2.2
    have hG := fp_program_mem_l Q hZF hω layer hw (recode.program_l Q K form.2.1)
    let A' : (N).Domain := ⟨A, hA⟩
    let G' : (N).Domain := ⟨G, T A hA G hG⟩
    let n' : (N).Domain := ⟨n, T A hA n hn⟩
    let r' : (N).Domain := ⟨r, T A hA r hr⟩
    obtain ⟨v, hv⟩ := (K).total G r
    have flat : Sformula_d K ω v n G r := ⟨hv, recode.program_l Q K form.2.1, form.2.2⟩
    exact ⟨hz, A', (rt_fp_v_l Q hZF hω hW hωY hV hs δ A').mpr layer, G', hG, n', hn, r', hr,
      (decode A' G' n' r' layer hG hn hr).mpr ⟨a, F, num, form, recode⟩,
      (ft_prev_source_l Q hZF hω hV hW hs hων hωY G' n' r' g model flat hg).mpr
        ((recode.satisfies_l Q K hZF hm model form hv hf hg agree).mp truth)⟩

include hω hV hW hs in
/-- 任意参数环境下的同一公式模板；量词块可以自由增加额外绑定槽位。 -/
theorem sc_prev_source_l {d} (ρ : Env N d) (w δ z g : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    (hδ : M.IsLimitOrdinal (δ.eval ρ).val) (hωδ : M.mem ω (δ.eval ρ).val)
    (hz : M.mem (z.eval ρ).val ω) {c R f : M.Domain}
    (hm : Smem_d Q c X R) (hf : M.IsSetFunctionFromTo Q f ω X)
    (hg : M.IsSetFunctionFromTo K (g.eval ρ).val ω X) (agree : Sx_graph_d Q K f (g.eval ρ).val) :
    Formula.satisfies ρ (sc_prev_m w δ z g) ↔ Sc_sat_d Q ω c (z.eval ρ).val f := by
  have env : (Definitional.Env.substitute ρ (Fin.cases g (Fin.cases z (Fin.cases δ (fun _ => w))))).bound =
      ((⟨Fin.cases (z.eval ρ) (Fin.cases (δ.eval ρ) (fun _ => ⟨ω, hωY⟩)),
        fun _ => g.eval ρ⟩ : Env N 3).push (g.eval ρ)).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw))) i
  exact (Formula.satisfies_bind _ _ _).trans
    ((Formula.closed_env_l sc_prev_s.body sc_prev_s.freeClosed env).trans
      (sc_prev_values_l hZF hω hV hW hs hωY (δ.eval ρ) (z.eval ρ) (g.eval ρ) hδ hωδ hz hm hf hg agree))

def sc_prev_local_m {d} (Y ω δ z f : Term d) : Formula 1 d :=
  lr_rel_m (sc_prev_m (.bound 3) (.bound 2) (.bound 1) (.newest : Term 4)) Y
    (Fin.cases f (Fin.cases z (Fin.cases δ (fun _ => ω))))

@[simp] theorem sc_prev_local_closed_l {d} (Y ω δ z f : Term d)
    (hY : Y.freeSupport = []) (hω : ω.freeSupport = []) (hδ : δ.freeSupport = [])
    (hz : z.freeSupport = []) (hf : f.freeSupport = []) : (sc_prev_local_m Y ω δ z f).FreeClosed :=
  lr_rel_closed_l _ (sc_prev_m_freeClosed _ _ _ _ rfl rfl rfl rfl) Y _ hY
    (Fin.cases hf (Fin.cases hz (Fin.cases hδ (fun _ => hω))))

/-- 原自然数码直接接入前驱满足公式；候选自然数不必预先是合法公式码。 -/
theorem sc_predecessor_rank_l {d} (ρ : Env M d) (Y ω δ z g : Term d) {ν μ X c R f : M.Domain}
    (hω : M.IsOmega (ω.eval ρ)) (hδ : M.IsLimitOrdinal (δ.eval ρ)) (hωδ : M.mem (ω.eval ρ) (δ.eval ρ))
    (hδν : M.MemberSubset (δ.eval ρ) ν) (hV : V_d Q ν X) (hW : V_d Q μ (Y.eval ρ)) (hs : M.SuccessorOf μ ν)
    (hz : M.mem (z.eval ρ) (ω.eval ρ)) (hm : Smem_d Q c X R) (hf : M.IsSetFunctionFromTo Q f (ω.eval ρ) X)
    (hg : M.IsSetFunctionFromTo K (g.eval ρ) (ω.eval ρ) X) (agree : Sx_graph_d Q K f (g.eval ρ)) :
    Formula.satisfies ρ (sc_prev_local_m Y ω δ z g) ↔ Sc_sat_d Q (ω.eval ρ) c (z.eval ρ) f := by
  have hδμ := ordinal_down_l (ZF.modelsKP hZF) hδ.1 (v_ordinal_l Q hW) hδν hs.predecessor_mem
  have hδY := ZF.v_ordinal_mem_l Q hZF hW hδμ
  have hw := ZF.v_ordinal_mem_l Q hZF hW ((v_ordinal_l Q hW).transitive (δ.eval ρ) hδμ (ω.eval ρ) hωδ)
  have hων : M.MemberSubset (ω.eval ρ) ν := fun i hi => hδν i (hδ.1.transitive (ω.eval ρ) hωδ i hi)
  have nat : M.MemberSubset (ω.eval ρ) X := fun i hi => ZF.v_ordinal_mem_l Q hZF hV (hων i hi)
  have hG := (ZF.v_successor_l Q hZF hV hW hs (g.eval ρ)).mpr (fp_function_rank_l Q hZF hω hV hων nat hg)
  have trans := ZF.v_transitive_l Q hZF hW
  let nz' : Nonempty {x // M.mem x (Y.eval ρ)} := ⟨⟨ω.eval ρ, hw⟩⟩
  let P := rt_model_l (Y.eval ρ) nz'
  let w : P.Domain := ⟨ω.eval ρ, hw⟩
  let t : P.Domain := ⟨δ.eval ρ, hδY⟩
  let q : P.Domain := ⟨z.eval ρ, trans (ω.eval ρ) hw (z.eval ρ) hz⟩
  let a : P.Domain := ⟨g.eval ρ, hG⟩
  let η : Env P 4 := ⟨Fin.cases a (Fin.cases q (Fin.cases t (fun _ => w))), fun _ => a⟩
  let φ := sc_prev_m (.bound 3) (.bound 2) (.bound 1) (.newest : Term 4)
  obtain ⟨b, S, hb, hS⟩ := smdl_membership_l Q hZF ⟨ω.eval ρ, hw⟩
  exact (sc_relative_sat_l Q ⟨hb, hS⟩ trans nz' φ (sc_prev_m_freeClosed _ _ _ _ rfl rfl rfl rfl)
    η ρ Y (Fin.cases g (Fin.cases z (Fin.cases δ (fun _ => ω)))) rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))).trans
      (sc_prev_source_l hZF hω hV hW hs hw η (.bound 3) (.bound 2) (.bound 1) .newest rfl hδ hωδ hz hm hf hg agree)

include hω hV hW hs in
/-- 一个实际平坦赋值同时服务于全部原自然数公式码，重编码见证由 ZF 自动构造。 -/
theorem sc_predecessor_recode_l {δ c R f : M.Domain} (hδ : M.IsLimitOrdinal δ)
    (hωδ : M.mem ω δ) (hδν : M.MemberSubset δ ν) (hm : Smem_d Q c X R)
    (hf : M.IsSetFunctionFromTo Q f ω X) : ∃ g, M.IsSetFunctionFromTo K g ω X ∧ Sx_graph_d Q K f g ∧
      ∀ z, M.mem z ω → (Formula.satisfies (⟨Fin.cases g (Fin.cases z
        (Fin.cases δ (Fin.cases ω (fun _ => Y)))), fun _ => g⟩ : Env M 5)
          (sc_prev_local_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) ↔ Sc_sat_d Q ω c z f) := by
  obtain ⟨g, hg, agree⟩ := fn_recode_l Q K hZF hf
  exact ⟨g, hg, agree, fun z hz => sc_predecessor_rank_l hZF _ _ _ _ _ _
    hω hδ hωδ hδν hV hW hs hz hm hf hg agree⟩

end YesMetaZFC.SetTheory.Internal
