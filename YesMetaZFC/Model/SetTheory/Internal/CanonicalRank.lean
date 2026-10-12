import YesMetaZFC.Model.SetTheory.Internal.CanonicalFlat
import YesMetaZFC.Model.SetTheory.Internal.LowerSatisfaction
import YesMetaZFC.Model.SetTheory.Internal.CanonicalSatisfaction

/-! # 任意较低秩层中的原自然数公式码

规范解码留在给定的极限秩层 C，真值求值仅在较低层 A 的幂集内进行。
两个层分别指定，故查询码不必属于 A，而 A 也不必是外层的前驱。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def sc_lower_s : UnarySchema 4 where
  body := .conj (.mem (.bound 1) (.bound 4)) (set[5] ⟪
    ∃ G ∈ ⌜(.bound 3 : Term 5)⌝ₛ, ∃ n ∈ ⌜(.bound 3 : Term 5)⌝ₛ, ∃ r ∈ ⌜(.bound 3 : Term 5)⌝ₛ,
      ⌜sc_flat_local_m⌝ₚ(⌜(.bound 3 : Term 5)⌝ₛ, ⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 1 : Term 5)⌝ₛ, G, n, r) ∧
      ⌜ft_lower_m⌝ₚ(⌜(.bound 2 : Term 5)⌝ₛ, ⌜(.bound 4 : Term 5)⌝ₛ, G, n, r, ⌜(.newest : Term 5)⌝ₛ)⟫)

def sc_lower_m {d} (ω C A z f : Term d) : Formula 1 d :=
  pred_m sc_lower_s (Fin.cases z (Fin.cases A (Fin.cases C (fun _ => ω)))) f

@[simp] theorem sc_lower_closed_l {d} (ω C A z f : Term d)
    (hw : ω.freeSupport = []) (hc : C.freeSupport = []) (ha : A.freeSupport = [])
    (hz : z.freeSupport = []) (hf : f.freeSupport = []) : (sc_lower_m ω C A z f).FreeClosed :=
  pred_m_freeClosed sc_lower_s _ _ (Fin.cases hz (Fin.cases ha (Fin.cases hc (fun _ => hw)))) hf

variable (hZF : M.Models ZF) {ω η Y : M.Domain} (hω : M.IsOmega ω)
  (hY : V_d (kp_pair_l (ZF.modelsKP hZF)) η Y) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "ny" => Nonempty.intro (Subtype.mk ω hωY)
local notation "N" => rt_model_l Y ny

include hω hY in
private theorem sc_lower_values_l (C A z g : (N).Domain) {ξ ν c R f : M.Domain}
    (hC : V_d Q ξ C.val) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ)
    (hA : V_d Q ν A.val) (hων : M.MemberSubset ω ν) (hz : M.mem z.val ω)
    (hm : Smem_d Q c A.val R) (hf : M.IsSetFunctionFromTo Q f ω A.val)
    (hg : M.IsSetFunctionFromTo K g.val ω A.val) (agree : Sx_graph_d Q K f g.val) :
    Formula.satisfies (⟨Fin.cases g (Fin.cases z (Fin.cases A (Fin.cases C (fun _ => ⟨ω, hωY⟩)))),
      fun _ => g⟩ : Env N 5) sc_lower_s.body ↔ Sc_sat_d Q ω c z.val f := by
  let ρ : Env N 5 := ⟨Fin.cases g (Fin.cases z (Fin.cases A (Fin.cases C (fun _ => ⟨ω, hωY⟩)))), fun _ => g⟩
  have ht := ZF.v_transitive_l Q hZF hY
  have ct := ZF.v_transitive_l Q hZF hC
  have hwC := ZF.v_ordinal_mem_l Q hZF hC hωξ
  obtain ⟨e, _, heω⟩ := hω.1.1
  obtain ⟨b, S, model⟩ := smdl_membership_l K hZF ⟨e, ZF.v_ordinal_mem_l Q hZF hA (hων e heω)⟩
  have decode (G n r : (N).Domain) (hG : M.mem G.val C.val) (hn : M.mem n.val C.val) (hr : M.mem r.val C.val) :
      Formula.satisfies (((ρ.push G).push n).push r) (sc_flat_local_m (.bound 6) (.bound 7) (.bound 4) (.bound 2) (.bound 1) .newest) ↔
        Sc_flat_d Q K ω z.val G.val n.val r.val :=
    (rt_model_delta_l ht ny (sc_flat_local_delta_l ..) _).trans
      (sc_flat_local_sat_l hZF hω hξ hC hwC _ _ _ _ _ _ _ rfl rfl (ct ω hwC z.val hz) hG hn hr)
  have read (G n r : (N).Domain) {a : M.Domain} (form : Sformula_d K ω a n.val G.val r.val) :=
    ft_lower_source_l hZF hY ny (((ρ.push G).push n).push r)
      (.bound 5) (.bound 7) (.bound 2) (.bound 1) .newest (.bound 3) hω hA hων model form hg
  simp only [sc_lower_s, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff]
  constructor
  · rintro ⟨_, G, hG, n, hn, r, hr, code, truth⟩
    obtain ⟨a, F, num, form, recode⟩ := (decode G n r hG hn hr).mp code
    obtain ⟨v, hv⟩ := (K).total G.val r.val
    have flat : Sformula_d K ω v n.val G.val r.val := ⟨hv, recode.program_l Q K form.2.1, form.2.2⟩
    exact ⟨a, num, (recode.satisfies_l Q K hZF hm model form hv hf hg agree).mpr ((read G n r flat).mp truth)⟩
  · rintro ⟨a, num, truth⟩
    have data := num
    obtain ⟨n, F, r, _, _, form, _⟩ := data
    obtain ⟨G, recode⟩ := sx_program_exists_l Q K hZF hω form.2.1
    have hn := ct ω hwC n form.2.1.1
    have hr := ct n hn r form.2.2
    have hG := fp_program_mem_l Q hZF hω hC hwC (recode.program_l Q K form.2.1)
    let G' : (N).Domain := ⟨G, ht C.val C.property G hG⟩
    let n' : (N).Domain := ⟨n, ht C.val C.property n hn⟩
    let r' : (N).Domain := ⟨r, ht C.val C.property r hr⟩
    obtain ⟨v, hv⟩ := (K).total G r
    have flat : Sformula_d K ω v n G r := ⟨hv, recode.program_l Q K form.2.1, form.2.2⟩
    exact ⟨hz, G', hG, n', hn, r', hr, (decode G' n' r' hG hn hr).mpr ⟨a, F, num, form, recode⟩,
      (read G' n' r' flat).mpr ((recode.satisfies_l Q K hZF hm model form hv hf hg agree).mp truth)⟩

include hω hY in
theorem sc_lower_source_l {d} (ρ : Env N d) (w C A z g : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {ξ ν c R f : M.Domain} (hC : V_d Q ξ (C.eval ρ).val) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ)
    (hA : V_d Q ν (A.eval ρ).val) (hων : M.MemberSubset ω ν) (hz : M.mem (z.eval ρ).val ω)
    (hm : Smem_d Q c (A.eval ρ).val R) (hf : M.IsSetFunctionFromTo Q f ω (A.eval ρ).val)
    (hg : M.IsSetFunctionFromTo K (g.eval ρ).val ω (A.eval ρ).val) (agree : Sx_graph_d Q K f (g.eval ρ).val) :
    Formula.satisfies ρ (sc_lower_m w C A z g) ↔ Sc_sat_d Q ω c (z.eval ρ).val f := by
  have env : (Definitional.Env.substitute ρ (Fin.cases g (Fin.cases z (Fin.cases A (Fin.cases C (fun _ => w)))))).bound =
      (⟨Fin.cases (g.eval ρ) (Fin.cases (z.eval ρ) (Fin.cases (A.eval ρ)
        (Fin.cases (C.eval ρ) (fun _ => ⟨ω, hωY⟩)))), fun _ => g.eval ρ⟩ : Env N 5).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw)))) i
  exact (Formula.satisfies_bind _ _ _).trans ((Formula.closed_env_l sc_lower_s.body sc_lower_s.freeClosed env).trans
    (sc_lower_values_l hZF hω hY hωY (C.eval ρ) (A.eval ρ) (z.eval ρ) (g.eval ρ) hC hξ hωξ hA hων hz hm hf hg agree))

end YesMetaZFC.SetTheory.Internal
