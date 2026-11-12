import YesMetaZFC.SetTheory.LargeCardinal.Absorption.CounterPayoff
import YesMetaZFC.Model.SetTheory.Images.GameCanonicalImage

/-! # 真类 Woodin 推出 L(ℝ) 满足 AD

反例的两层 hull、完整吸收列和高度提升由原大基数假设构造。高派生
模型中的决定收益与原反例逐对象相同；规范局面编号对齐后，赢家的
实数编码及完整有界获胜条件传回同一实数族，排除原非决定性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem wd_lr_ad_l (proper : Wd_proper_d I) : M.SatisfiesSentence Axioms.lr_ad := by
  apply Classical.byContradiction
  intro bad
  obtain ⟨Ω,hw,_,_,_,_,_,P,_,_,_,_,_,_,y,_,eyω,_,_,finite,data,number,no,
    D,native,e,ei,ef,w,b,_,T,_,_,A,ew,eb,_,_,_,eA,seed,space,_,det⟩ :=
    wd_counterexample_payoff_l hZFC proper bad
  have parity : Gs_parity_d Ω (y 8) := eyω ▸ data.base.2.2
  have win := det_canonical_image_l native hZF e ei ef seed.1 space (ew.symm ▸ hw)
    (ew.symm ▸ finite) (ew.symm ▸ number) (ew.symm ▸ parity) det
  apply no
  simpa only [ew,eb,eA] using win

end YesMetaZFC.SetTheory.LargeCardinal
