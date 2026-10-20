import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceWellFounded

/-! # 内部所属判断自动生成实际良基超幂与坍塌

该入口读取所属模型中的原短扩展器公式，构造施加源的全部实际分量、定向
极限及传递坍塌。每个良基性见证均来自源内共同约束，未要求背景短扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.limit_l {ω κ K X R K' Y S L F V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y S)
    (branches : Sc_branch_d ω X) (cover : Sc_cover_d X) (power : Sc_power_d X)
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (owner_branches : Sc_branch_d ω Y) (hV : M.mem V Y) (owner_power : FilterZF.Source_d Y K' V)
    (loc : It_local_d ω Y κ L F) : Ep_limit_d hZF ω κ L X R F := by
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory owner.finite hV owner_power)).transfer_l reverse
  obtain ⟨J, O, Z, A, p, T, U, q, c, C, W, system, limit, model, elementary⟩ :=
    loc.apply_l hZFC source owner hV owner_power reverse
  have wf := loc.source_wf_l hZF source owner (ZFC.dc_l I hZFC source.omega) branches cover power
    inside agree owner_branches hV owner_power system limit model elementary
  exact ⟨J, O, Z, A, p, T, U, q, c, C, W, system, limit, model, wf, elementary,
    ep_collapse_l hZF source family system limit model elementary wf⟩

end YesMetaZFC.SetTheory.LargeCardinal
