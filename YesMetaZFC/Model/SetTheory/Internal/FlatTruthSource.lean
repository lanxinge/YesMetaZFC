import YesMetaZFC.Model.SetTheory.Internal.FlatProgram
import YesMetaZFC.Model.SetTheory.Internal.FlatTruth
import YesMetaZFC.SetTheory.FlatPairing.AssignmentSource

/-! # 平坦真值方程在后继秩层中的绝对性

存在量词的对象、更新赋值和新前缀均有已经实现的秩界；把这些见证收回源内，
便得到四种逻辑构造的双向相对化，不假设后继秩层是 ZF 模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
  {ω μ Y : M.Domain} (hω : M.IsOmega ω) (hW : V_d I μ Y) (hωY : M.mem ω Y)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY

theorem rt_ft_arg_l (k : Nat) (A R b T f p i j : (N).Domain) {ν : M.Domain}
    (hV : V_d I ν A.val) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hf : M.IsSetFunctionFromTo K f.val ω A.val) (hi : M.mem i.val ω) :
    Ft_arg_d J k ⟨ω, hωY⟩ A R b T f p i j ↔
      Ft_arg_d K k ω A.val R.val b.val T.val f.val p.val i.val j.val := by
  have entry := rt_fp_entry_l I hZF hω hW hωY
  have trans := ZF.v_transitive_l I hZF hW
  rcases k with _ | (_ | (_ | k))
  · refine ⟨fun ⟨x, y, hx, hy, hR⟩ => ⟨x.val, y.val, (entry i x f).mp hx,
      (entry j y f).mp hy, (entry x y R).mp hR⟩, ?_⟩
    rintro ⟨x, y, hx, hy, hR⟩
    let x' : (N).Domain := ⟨x, (rt_fp_coordinates_l I hZF hω hW f.property hx).2⟩
    let y' : (N).Domain := ⟨y, (rt_fp_coordinates_l I hZF hω hW f.property hy).2⟩
    exact ⟨x', y', (entry i x' f).mpr hx, (entry j y' f).mpr hy, (entry x' y' R).mpr hR⟩
  · refine ⟨fun ⟨x, hx, hy⟩ => ⟨x.val, (entry i x f).mp hx, (entry j x f).mp hy⟩, ?_⟩
    rintro ⟨x, hx, hy⟩
    let x' : (N).Domain := ⟨x, (rt_fp_coordinates_l I hZF hω hW f.property hx).2⟩
    exact ⟨x', (entry i x' f).mpr hx, (entry j x' f).mpr hy⟩
  · exact not_congr (or_congr (entry i p T) (entry j p T))
  · constructor
    · rintro ⟨x, g, q, hx, update, code, truth⟩
      exact ⟨x.val, g.val, q.val, hx, (rt_fp_update_l I hZF hω hW hωY f i x g).mp update,
        (rt_fs_code_l I hZF hω hW hωY A g b q hV hων).mp code, (entry j q T).mp truth⟩
    · rintro ⟨x, g, q, hx, update, code, truth⟩
      have hg := update.function_l K hf hi hx
      have bound := fp_function_rank_l I hZF hω hV hων
        (fun t ht => ZF.v_ordinal_mem_l I hZF hV (hων t ht)) hg
      let x' : (N).Domain := ⟨x, trans A.val A.property x hx⟩
      let g' : (N).Domain := ⟨g, (ZF.v_successor_l I hZF hV hW hs g).mpr bound⟩
      let q' : (N).Domain := ⟨q, trans A.val A.property q (code.bound_l K).2⟩
      exact ⟨x', g', q', hx, (rt_fp_update_l I hZF hω hW hωY f i x' g').mpr update,
        (rt_fs_code_l I hZF hω hW hωY A g' b q' hV hων).mpr code, (entry j q' T).mpr truth⟩

theorem rt_ft_node_l (A R b T c f p : (N).Domain) {ν r : M.Domain}
    (hV : V_d I ν A.val) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hf : M.IsSetFunctionFromTo K f.val ω A.val) (hr : M.mem r ω) (hc : Sfm_node_d K ω r c.val) :
    Ft_node_d J ⟨ω, hωY⟩ A R b T c f p ↔ Ft_node_d K ω A.val R.val b.val T.val c.val f.val p.val := by
  constructor
  · rintro ⟨k, i, j, code, arg⟩
    have code' := (rt_fp_sop_l I hZF hω hW hωY k.val c i j).mp code
    have hi := (sfm_node_naturals_l K hZF hω hr hc code').1
    exact ⟨k, i.val, j.val, code', (rt_ft_arg_l I hZF hω hW hωY k.val A R b T f p i j hV hs hων hf hi).mp arg⟩
  · rintro ⟨k, i, j, code, arg⟩
    have ij := fp_sop_coordinates_l I hZF hω hW c.property code
    let i' : (N).Domain := ⟨i, ij.1⟩
    let j' : (N).Domain := ⟨j, ij.2⟩
    have hi := (sfm_node_naturals_l K hZF hω hr hc code).1
    exact ⟨k, i', j', (rt_fp_sop_l I hZF hω hW hωY k.val c i' j').mpr code,
      (rt_ft_arg_l I hZF hω hW hωY k.val A R b T f p i' j' hV hs hων hf hi).mpr arg⟩

theorem rt_ft_eval_l (A R b F n T : (N).Domain) {ν : M.Domain}
    (hV : V_d I ν A.val) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hF : Sfm_d K ω n.val F.val) :
    Ft_eval_d J ⟨ω, hωY⟩ A R b F n T ↔ Ft_eval_d K ω A.val R.val b.val F.val n.val T.val := by
  have entry := rt_fp_entry_l I hZF hω hW hωY
  have fn f := rt_fp_function_from_l I hZF hω hW hωY f ⟨ω, hωY⟩ A
  have code f p := rt_fs_code_l I hZF hω hW hωY A f b p hV hων
  have trans := ZF.v_transitive_l I hZF hW
  have own f (hf : M.IsSetFunctionFromTo K f ω A.val) : M.mem f Y :=
    (ZF.v_successor_l I hZF hV hW hs f).mpr (fp_function_rank_l I hZF hω hV hων
      (fun t ht => ZF.v_ordinal_mem_l I hZF hV (hων t ht)) hf)
  have row r c (hc : M.PairMember K r c F.val) : M.mem r ω :=
    hω.transitive hZF n.val hF.1 r ((hF.2.1.2.2 r).mpr ⟨c, hc⟩)
  constructor
  · rintro ⟨rel, bound, eval⟩
    refine ⟨(rt_fp_relation_l I hZF hω hW hωY T).mp rel, ?_, ?_⟩
    · intro r p hp
      have rp := rt_fp_coordinates_l I hZF hω hW T.property hp
      let r' : (N).Domain := ⟨r, rp.1⟩
      let p' : (N).Domain := ⟨p, rp.2⟩
      obtain ⟨hr, f, hf, cp⟩ := bound r' p' ((entry r' p' T).mpr hp)
      exact ⟨hr, f.val, (fn f).mp hf, (code f p').mp cp⟩
    · intro r c f p hc hf cp
      have rc := rt_fp_coordinates_l I hZF hω hW F.property hc
      let r' : (N).Domain := ⟨r, rc.1⟩
      let c' : (N).Domain := ⟨c, rc.2⟩
      let f' : (N).Domain := ⟨f, own f hf⟩
      let p' : (N).Domain := ⟨p, trans A.val A.property p (cp.bound_l K).2⟩
      exact (entry r' p' T).symm.trans ((eval r' c' f' p' ((entry r' c' F).mpr hc)
        ((fn f').mpr hf) ((code f' p').mpr cp)).trans
        (rt_ft_node_l I hZF hω hW hωY A R b T c' f' p' hV hs hων hf (row r c hc) (hF.2.2 r c hc)))
  · rintro ⟨rel, bound, eval⟩
    refine ⟨(rt_fp_relation_l I hZF hω hW hωY T).mpr rel, ?_, ?_⟩
    · intro r p hp
      obtain ⟨hr, f, hf, cp⟩ := bound r.val p.val ((entry r p T).mp hp)
      let f' : (N).Domain := ⟨f, own f hf⟩
      exact ⟨hr, f', (fn f').mpr hf, (code f' p).mpr cp⟩
    · intro r c f p hc hf cp
      have hc' := (entry r c F).mp hc
      have hf' := (fn f).mp hf
      exact (entry r p T).trans ((eval r.val c.val f.val p.val hc' hf' ((code f p).mp cp)).trans
        (rt_ft_node_l I hZF hω hW hωY A R b T c f p hV hs hων hf'
          (row r.val c.val hc') (hF.2.2 r.val c.val hc')).symm)

end YesMetaZFC.SetTheory.Internal
