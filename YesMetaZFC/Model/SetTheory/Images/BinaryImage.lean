import YesMetaZFC.SetTheory.Descriptive.Coding.RelationCode
import YesMetaZFC.Model.SetTheory.ProjectBounded

/-! # 成员满嵌入保持规范二值编码

二值性和方块内解码是 Δ₀。先实际构造源中的规范序数方块，沿满嵌入
运输它的有界证书，再由两侧规范配对唯一性恢复原全局解码关系。
因此有限泛型扩张中的编码在较大扩张中仍解码为同一个查询点。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
  (e : M.Domain → N.Domain) (ei : Function.Injective e)
  (ef : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
include ei ef

theorem oc_square_image_l (hM : M.Models KP) (hN : N.Models KP) {ω X η F : M.Domain} :
    Oc_square_d ω X η F ↔ Oc_square_d (e ω) (e X) (e η) (e F) := by
  let ρ : Env M 4 := ⟨fun i => [ω,X,η,F].get i,fun _ => ω⟩
  exact (oc_square_sat_l hM ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3)).symm.trans
    ((delta0_image_l e ei ef (oc_square_delta_l ..) ρ).trans (oc_square_sat_l hN _ _ _ _ _))

theorem bc_binary_image_l (hM : Extensional M) (hN : Extensional N) {ω b : M.Domain} :
    Bc_binary_d ω b ↔ Bc_binary_d (e ω) (e b) := by
  let ρ : Env M 2 := ⟨Fin.cases ω (fun _ => b),fun _ => ω⟩
  exact (bc_binary_sat_l hM ρ (.bound 0) (.bound 1)).symm.trans
    ((delta0_image_l e ei ef (bc_binary_delta_l ..) ρ).trans (bc_binary_sat_l hN _ _ _))

theorem bc_graph_image_l (hM : Extensional M) (hN : Extensional N) {ω X F b r : M.Domain} :
    Bc_graph_d ω X F b r ↔ Bc_graph_d (e ω) (e X) (e F) (e b) (e r) := by
  let ρ : Env M 5 := ⟨fun i => [ω,X,F,b,r].get i,fun _ => ω⟩
  exact (bc_graph_sat_l hM ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).symm.trans
    ((delta0_image_l e ei ef (bc_graph_delta_l ..) ρ).trans (bc_graph_sat_l hN _ _ _ _ _ _))

/-- 不要求全初等性或相同实数集；规范编号由实际方块证书识别。 -/
theorem bc_read_image_l (hM : M.Models ZF) (hN : N.Models ZF) {ω b r : M.Domain}
    (hw : M.IsOrdinal ω) : Bc_read_d (kp_pair_l (ZF.modelsKP hM)) ω b r ↔
      Bc_read_d (kp_pair_l (ZF.modelsKP hN)) (e ω) (e b) (e r) := by
  obtain ⟨X,product⟩ := ZF.exists_cartesianProduct hM (kp_pair_l (ZF.modelsKP hM)) ω ω
  obtain ⟨η,F,square⟩ := oc_square_exists_l hM hw product
  have target := (oc_square_image_l e ei ef (ZF.modelsKP hM) (ZF.modelsKP hN)).mp square
  exact (bc_graph_read_l hM square).symm.trans
    ((bc_graph_image_l e ei ef hM.1 hN.1).trans (bc_graph_read_l hN target))

end YesMetaZFC.SetTheory
