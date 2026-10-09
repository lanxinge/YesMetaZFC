import YesMetaZFC.Model.SetTheory.Internal.RankLargest
import YesMetaZFC.Model.SetTheory.Internal.RankSatisfaction
import YesMetaZFC.SetTheory.FlatPairing.StructureSource

/-! # 最大序数以下的完整满足关系

同一条原公式自行识别最大序数、前一秩层及其隶属结构，再运行平坦真值表。
前一层、结构码和真值表均为量化见证，不占用类型查询的常量名。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ft_prev_d (J : FlatPairing.convention.Interpretation M) (ω F n r f : M.Domain) : Prop :=
  ∃ ν X c R, Sv_max_d ν ∧ V_d J ν X ∧ Smem_d J c X R ∧ Ft_sat_d J ω X R F n r f

def ft_prev_m {d} (ω F n r f : Term d) : Formula 1 d := set[d] ⟪∃ ν X c R,
  ⌜sv_max_m⌝ₚ(ν) ∧ ⌜v_m FlatPairing.convention⌝ₚ(ν, X) ∧
  ⌜smem_m (𝒞 := FlatPairing.convention)⌝ₚ(c, X, R) ∧
  ⌜ft_sat_m (𝒞 := FlatPairing.convention)⌝ₚ(⌜ω⌝ₛ, X, R, ⌜F⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, ⌜f⌝ₛ)⟫
derive_free_closed ft_prev_m

theorem ft_prev_sat_l (J : FlatPairing.convention.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω F n r f : Term d) :
    Formula.satisfies ρ (ft_prev_m ω F n r f) ↔ Ft_prev_d J (ω.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ) (f.eval ρ) := by
  simp only [ft_prev_m, Ft_prev_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sv_max_sat_l, v_sat_l J hE, smem_sat_l J, ft_sat_sat_l J hE, Definitional.Term.eval_weaken]; rfl

variable {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
  {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω) (hV : V_d I ν X) (hW : V_d I μ Y)
  (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν) (hωY : M.mem ω Y)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY
include hV hs hων in
theorem ft_prev_source_l (F n r f : (N).Domain) {c R a : M.Domain}
    (hm : Smem_d K c X R) (ha : Sformula_d K ω a n.val F.val r.val)
    (hf : M.IsSetFunctionFromTo K f.val ω X) :
    Ft_prev_d J ⟨ω, hωY⟩ F n r f ↔ Satisfies_d K ω c a f.val := by
  constructor
  · rintro ⟨η, A, b, S, greatest, layer, model, truth⟩
    have eqη := (sv_max_rank_l I hZF hV hW hs hωY η).mp greatest
    have hA := (rt_fp_v_l I hZF hω hW hωY hV hs η A).mp layer
    have eqA := ZF.v_unique_l Q hZF (eqη ▸ hA) ((v_pairing_l I Q hZF).mp hV)
    have code := (rt_fp_smem_l I hZF hω hW hωY b A S).mp model
    have code' : Smem_d K b.val X S.val := eqA ▸ code
    have eqc := (smem_unique_l K hZF.1 code' hm).1
    exact eqc ▸ (ft_source_satisfaction_l I hZF hω hW hωY A S F n r f
      (eqA.symm ▸ hV) hs hων code.1 ha (eqA.symm ▸ hf)).mp truth
  · intro truth
    obtain ⟨b, S, hb, hS, model⟩ := fp_model_rank_l I hZF hω hV hW hs hων
    obtain ⟨eqb, eqS⟩ := smem_unique_l K hZF.1 model hm
    subst b S
    let η : (N).Domain := ⟨ν, ZF.v_ordinal_mem_l I hZF hW hs.predecessor_mem⟩
    let A : (N).Domain := ⟨X, (ZF.v_successor_l I hZF hV hW hs X).mpr (fun _ h => h)⟩
    let c' : (N).Domain := ⟨c, hb⟩
    let R' : (N).Domain := ⟨R, hS⟩
    exact ⟨η, A, c', R', (sv_max_rank_l I hZF hV hW hs hωY η).mpr rfl,
      (rt_fp_v_l I hZF hω hW hωY hV hs η A).mpr ((v_pairing_l I Q hZF).mp hV),
      (rt_fp_smem_l I hZF hω hW hωY c' A R').mpr hm,
      (ft_source_satisfaction_l I hZF hω hW hωY A R' F n r f hV hs hων hm.1 ha hf).mpr truth⟩

def ft_prev_local_m {d} (Y ω F n r f : Term d) : Formula 1 d :=
  lr_rel_m (ft_prev_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 5)) Y
    (Fin.cases f (Fin.cases r (Fin.cases n (Fin.cases F (fun _ => ω)))))

@[simp] theorem ft_prev_local_closed_l {d} (Y ω F n r f : Term d)
    (hY : Y.freeSupport = []) (hω : ω.freeSupport = []) (hF : F.freeSupport = [])
    (hn : n.freeSupport = []) (hr : r.freeSupport = []) (hf : f.freeSupport = []) :
    (ft_prev_local_m Y ω F n r f).FreeClosed :=
  lr_rel_closed_l _ (ft_prev_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl) Y _ hY
    (Fin.cases hf (Fin.cases hr (Fin.cases hn (Fin.cases hF (fun _ => hω)))))

/-- 只交付原程序与实际赋值，统一公式自动完成前一秩层的完整满足判断。 -/
theorem ft_predecessor_rank_l {d} (ρ : Env M d) (Y ω F n r f : Term d)
    {ν μ X c R a : M.Domain} (hω : M.IsOmega (ω.eval ρ)) (hV : V_d I ν X)
    (hW : V_d I μ (Y.eval ρ)) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset (ω.eval ρ) ν)
    (hm : Smem_d K c X R) (ha : Sformula_d K (ω.eval ρ) a (n.eval ρ) (F.eval ρ) (r.eval ρ))
    (hf : M.IsSetFunctionFromTo K (f.eval ρ) (ω.eval ρ) X) :
    Formula.satisfies ρ (ft_prev_local_m Y ω F n r f) ↔ Satisfies_d K (ω.eval ρ) c a (f.eval ρ) := by
  have pow := ZF.v_successor_l I hZF hV hW hs
  have nat : M.MemberSubset (ω.eval ρ) X := fun i hi => ZF.v_ordinal_mem_l I hZF hV (hων i hi)
  have hw := (pow (ω.eval ρ)).mpr nat
  have hF := (pow (F.eval ρ)).mpr (fp_program_rank_l I hZF hω hV hων ha.2.1)
  have hg := (pow (f.eval ρ)).mpr (fp_function_rank_l I hZF hω hV hων nat hf)
  have trans := ZF.v_transitive_l I hZF hW
  have hn := trans (ω.eval ρ) hw (n.eval ρ) ha.2.1.1
  have hr := trans (n.eval ρ) hn (r.eval ρ) ha.2.2
  let T := rt_model_l (Y.eval ρ) ⟨⟨ω.eval ρ, hw⟩⟩
  let J' := fp_rank_interpretation_l I hZF hω hW hw
  let w : T.Domain := ⟨ω.eval ρ, hw⟩
  let G : T.Domain := ⟨F.eval ρ, hF⟩
  let l : T.Domain := ⟨n.eval ρ, hn⟩
  let k : T.Domain := ⟨r.eval ρ, hr⟩
  let g : T.Domain := ⟨f.eval ρ, hg⟩
  let η : Env T 5 := ⟨Fin.cases g (Fin.cases k (Fin.cases l (Fin.cases G (fun _ => w)))), fun _ => w⟩
  let φ := ft_prev_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 5)
  obtain ⟨v, S, hv, hS⟩ := smdl_membership_l Q hZF ⟨ω.eval ρ, hw⟩
  have rel := sc_relative_sat_l Q ⟨hv, hS⟩ trans ⟨⟨ω.eval ρ, hw⟩⟩ φ
    (ft_prev_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl) η ρ Y
    (Fin.cases f (Fin.cases r (Fin.cases n (Fin.cases F (fun _ => ω))))) rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  exact rel.trans ((ft_prev_sat_l J' (rt_model_ext_l hZF.1 trans ⟨⟨ω.eval ρ, hw⟩⟩) η
    (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).trans
    (ft_prev_source_l I hZF hω hV hW hs hων hw G l k g hm ha hf))

end YesMetaZFC.SetTheory.Internal
