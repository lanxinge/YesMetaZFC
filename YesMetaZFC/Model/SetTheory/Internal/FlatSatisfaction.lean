import YesMetaZFC.Model.SetTheory.Internal.FlatTruthSource
import YesMetaZFC.Model.SetTheory.Internal.Satisfaction

/-! # 在一个后继秩层中表达完整内部满足关系

单一公式量化坐标界、前缀及平坦真值表。坐标界由程序自动产生，其余见证
由实际秩界自动回收；与原满足关系的等价覆盖所有内部程序，包含非标准长度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ft_sat_d (ω X R F n r f : M.Domain) : Prop := M.IsSetFunctionFromTo I f ω X ∧
  ∃ b p T, Fs_code_d I ω X f b p ∧ Ft_eval_d I ω X R b F n T ∧ M.PairMember I r p T

def ft_sat_m {d} (ω X R F n r f : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 f ω X)
  (.existsE (.existsE (.existsE (.conj
    (fs_code_m (𝒞 := 𝒞) ω.weaken.weaken.weaken X.weaken.weaken.weaken f.weaken.weaken.weaken (.bound 2) (.bound 1))
    (.conj (ft_eval_m (𝒞 := 𝒞) ω.weaken.weaken.weaken X.weaken.weaken.weaken R.weaken.weaken.weaken (.bound 2)
      F.weaken.weaken.weaken n.weaken.weaken.weaken .newest)
      (Formula.orderedPairMem 𝒞 r.weaken.weaken.weaken (.bound 1) .newest))))))
derive_free_closed ft_sat_m

theorem ft_sat_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R F n r f : Term d) :
    Formula.satisfies ρ (ft_sat_m (𝒞 := 𝒞) ω X R F n r f) ↔
      Ft_sat_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ) (f.eval ρ) := by
  simp only [ft_sat_m, Ft_sat_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_exists_iff, fs_code_sat_l I hE, ft_eval_sat_l I hE,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF) {ω μ Y : M.Domain} (hω : M.IsOmega ω) (hW : V_d I μ Y) (hωY : M.mem ω Y)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY

theorem ft_sat_source_l (A R F n r f : (N).Domain) {ν E : M.Domain}
    (hV : V_d I ν A.val) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hF : Sfm_d K ω n.val F.val) (hr : M.mem r.val n.val)
    (hE : M.IsFunctionSpace K E ω A.val) (hf : M.IsSetFunctionFromTo K f.val ω A.val) :
    Ft_sat_d J ⟨ω, hωY⟩ A R F n r f ↔ Ssat_d K A.val R.val E F.val n.val r.val f.val := by
  have entry := rt_fp_entry_l I hZF hω hW hωY
  have trans := ZF.v_transitive_l I hZF hW
  constructor
  · rintro ⟨_, b, p, T, code, eval, truth⟩
    have code' := (rt_fs_code_l I hZF hω hW hωY A f b p hV hs hων).mp code
    have eval' := (rt_ft_eval_l I hZF hω hW hωY A R b F n T hV hs hων hF).mp eval
    exact (eval'.correct_l I hZF hω hV hων hF hE hr ((hE f.val).mpr hf) code').mp ((entry r p T).mp truth)
  · intro truth
    obtain ⟨b, hb, bound⟩ := sbound_exists_l K hZF hω hF
    obtain ⟨p, hp, code⟩ := fp_finite_rank_l I hZF hω hV hων hf hb
    obtain ⟨T, ht, eval⟩ := ft_eval_rank_l I hZF hω hV hW hs hων hF bound hE
    let b' : (N).Domain := ⟨b, trans ω hωY b hb⟩
    let p' : (N).Domain := ⟨p, trans A.val A.property p hp⟩
    let T' : (N).Domain := ⟨T, ht⟩
    exact ⟨(rt_fp_function_from_l I hZF hω hW hωY f ⟨ω, hωY⟩ A).mpr hf, b', p', T',
      (rt_fs_code_l I hZF hω hW hωY A f b' p' hV hs hων).mpr code,
      (rt_ft_eval_l I hZF hω hW hωY A R b' F n T' hV hs hων hF).mpr eval,
      (entry r p' T').mpr ((eval.correct_l I hZF hω hV hων hF hE hr ((hE f.val).mpr hf) code).mpr truth)⟩

/-- 自动构造赋值空间，并把源内单一原公式接回已有统一满足关系。 -/
theorem ft_source_satisfaction_l (A R F n r f : (N).Domain) {ν c a : M.Domain}
    (hV : V_d I ν A.val) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hc : Smdl_d K c A.val R.val) (ha : Sformula_d K ω a n.val F.val r.val)
    (hf : M.IsSetFunctionFromTo K f.val ω A.val) :
    Ft_sat_d J ⟨ω, hωY⟩ A R F n r f ↔ Satisfies_d K ω c a f.val := by
  obtain ⟨E, hE, _⟩ := senv_space_l K hZF ω hc.2.1
  exact (ft_sat_source_l I hZF hω hW hωY A R F n r f hV hs hων ha.2.1 ha.2.2 hE hf).trans
    (satisfies_decode_l K hZF.1 hc ha hE).symm

end YesMetaZFC.SetTheory.Internal
