import YesMetaZFC.SetTheory.LargeCardinal.TypeGameTransfer
import YesMetaZFC.Model.Forcing.Internal.Ground.Prefix

/-! # 扩张反例分支的真实地有限节点

树的第二坐标为原 ω。先按原三元字母表读出两条支撑列，再逐个内部长度
回收三张旧前缀及同一个旧树节点；无限分支本身不要求属于地模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem tg_join_targets_l {ω A B C P Y f t g q : M.Domain}
    (prod : M.IsCartesianProduct I P B C) (letters : M.IsCartesianProduct I Y A P)
    (fq : M.IsSetFunctionFromTo I q ω Y) (ft : Tg_graph_d I ω t) (fg : Tg_graph_d I ω g)
    (join : Tg_join_d I ω f t g q) : M.IsSetFunctionFromTo I t ω B ∧ M.IsSetFunctionFromTo I g ω C := by
  have vals i (hi : M.mem i ω) : ∃ y z, M.mem y B ∧ M.mem z C ∧ Rd_entry_d i y t ∧ Rd_entry_d i z g := by
    obtain ⟨x, y, z, v, p, _, iy, iz, cv, cp, ip⟩ := join.2 i hi
    obtain ⟨x', _, v', hv, cp'⟩ := (letters p).mp (fq.output_mem_of_pairMember ip)
    obtain ⟨rfl, rfl⟩ := (I).injective cp cp'
    obtain ⟨y', hy, z', hz, cv'⟩ := (prod v).mp hv
    obtain ⟨rfl, rfl⟩ := (I).injective cv cv'
    exact ⟨y, z, hy, hz, iy, iz⟩
  exact ⟨⟨ft.1, ft.2, fun i hi => (vals i hi).elim fun y h => h.elim fun z h => ⟨y, h.1, h.2.2.1⟩⟩,
    fg.1, fg.2, fun i hi => (vals i hi).elim fun y h => h.elim fun z h => ⟨z, h.2.1, h.2.2.2⟩⟩

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tg_projection_d.ground_nodes_l {ω A Γ P Y T S : M.Domain} {f : N.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) (space : Fseq_space_d I ω Y T)
    (prod : M.IsCartesianProduct I P ω Γ) (letters : M.IsCartesianProduct I Y A P)
    (ff : N.IsSetFunctionFromTo J f (e ω) (e A)) (branch : Tg_projection_d hN (e ω) (e Y) (e T) (e S) f) :
    ∃ t g, N.IsSetFunctionFromTo J t (e ω) (e ω) ∧ N.IsSetFunctionFromTo J g (e ω) (e Γ) ∧
      ∀ k, M.mem k ω → ∃ s t₀ g₀, Fn0_d k A s ∧ Fn0_d k ω t₀ ∧ Fn0_d k Γ g₀ ∧ Tg_node_d I k S s t₀ g₀ ∧
        N.IsRestrictionOf J (e s) f (e k) ∧ N.IsRestrictionOf J (e t₀) t (e k) ∧ N.IsRestrictionOf J (e g₀) g (e k) := by
  obtain ⟨q, t, g, fq, tree, ft, fg, join⟩ := branch
  have fq := fn0_function_l (ZF.modelsKP hN) fq
  obtain ⟨ft, fg⟩ := tg_join_targets_l hN (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he prod)
    (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he letters) fq ft fg join
  refine ⟨t, g, ft, fg, fun k hk => ?_⟩
  obtain ⟨s, fs, rs⟩ := ground_prefix_l hM hN e hi he hw hw' ff hk
  obtain ⟨t₀, ft₀, rt⟩ := ground_prefix_l hM hN e hi he hw hw' ft hk
  obtain ⟨g₀, fg₀, rg⟩ := ground_prefix_l hM hN e hi he hw hw' fg hk
  obtain ⟨q₀, fq₀, rq⟩ := ground_prefix_l hM hN e hi he hw hw' fq hk
  have fq₀' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fq₀
  have hqS := (image_member_l e hi he).mp (tree (e q₀)
    ((image_member_l e hi he).mpr ((space q₀).mpr ⟨k, hk, fq₀⟩)) ((ds_restrict_iff_l J fq₀' fq.1).mp rq))
  refine ⟨s, t₀, g₀, fn0_of_function_l (ZF.modelsKP hM) fs, fn0_of_function_l (ZF.modelsKP hM) ft₀,
    fn0_of_function_l (ZF.modelsKP hM) fg₀, ⟨⟨fs.1, fs.2.1⟩, ⟨ft₀.1, ft₀.2.1⟩, ⟨fg₀.1, fg₀.2.1⟩,
      q₀, hqS, ⟨fq₀.1, fq₀.2.1⟩, fun i hik => ?_⟩, rs, rt, rg⟩
  obtain ⟨x, _, ix⟩ := fs.2.2 i hik
  obtain ⟨y, _, iy⟩ := ft₀.2.2 i hik
  obtain ⟨z, _, iz⟩ := fg₀.2.2 i hik
  have ix' := ((rs.2 (e i) (e x)).mp ((image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i x s).mp ix)).2
  have iy' := ((rt.2 (e i) (e y)).mp ((image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i y t₀).mp iy)).2
  have iz' := ((rg.2 (e i) (e z)).mp ((image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i z g₀).mp iz)).2
  obtain ⟨x', y', z', v', p', jx, jy, jz, cv', cp', ip⟩ := join.2 (e i)
    ((image_member_l e hi he).mpr (hw.transitive hM k hk i hik))
  have eq := ff.1.2 (e i) x' (e x) jx ix'; subst x'
  have eq := ft.1.2 (e i) y' (e y) jy iy'; subst y'
  have eq := fg.1.2 (e i) z' (e z) jz iz'; subst z'
  obtain ⟨v, cv⟩ := (I).total y z
  obtain ⟨p, cp⟩ := (I).total x v
  have eq := (J).unique cv' (image_kpair_l e he cv); subst v'
  have eq := (J).unique cp' (image_kpair_l e he cp); subst p'
  exact ⟨x, y, z, v, p, ix, iy, iz, cv, cp,
    (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i p q₀).mpr
      ((rq.2 (e i) (e p)).mpr ⟨(image_member_l e hi he).mpr hik, ip⟩)⟩

end YesMetaZFC.SetTheory.LargeCardinal
