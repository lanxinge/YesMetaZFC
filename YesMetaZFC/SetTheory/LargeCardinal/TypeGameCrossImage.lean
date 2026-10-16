import YesMetaZFC.SetTheory.LargeCardinal.TypeGameImageRead
import YesMetaZFC.SetTheory.LargeCardinal.IterationWorkingApply
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplyReflect

/-! # 反射回答沿共同秩段进入跨模型树边

证书中的小超幂与前驱完整源的超幂共有同一个极限秩段中的有界代表。塌缩唯一性
识别两侧的原类型像，故读取的规则 (7) 属于实际加入 nice 树的那条边。
前驱的反射上下文也沿这条边搬运，为后续新参数保留原全称更新句子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X η C : M.Domain} (nc : Nonempty {x // M.mem x C}) {s}
  (ρ : Env (rt_model_l C nc) s)
  (o κ δ l n U D u τ Q w b z r q h : Term s) (σ : Fin 7 → Term s)
local notation "v" => (fun (t : Term s) => Subtype.val (Definitional.Term.eval ρ t))

theorem Tg_context_d.tree_image_l {c₀ α ξ T J G E H k c d R Y S K K' ζ V η₀ C₀ : M.Domain}
    (context : Tg_context_d ω X η C) (prior : Tg_context_d ω Y η₀ C₀)
    (owner : Ic_model_d hZF ω (v κ) K X R) (source : Ic_model_d hZF ω (v κ) K' Y S)
    (tree : It_pnice_d hZF ω c₀ α T J G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c J) (hd : Rd_entry_d k d J) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (hw : v o = ω) (hδ : M.IsLimitOrdinal (v δ)) (regular : Sc_regular_d X (v δ))
    (hV : M.mem V X) (rank : Vr_d X ζ V)
    (hV' : M.mem V Y) (rank' : Vr_d Y ζ V) (hζ : M.IsLimitOrdinal ζ)
    (hVC : M.mem V C₀) (hb : M.mem (v b) ω) (hz : M.mem (v z) ω) (hσ : ∀ i, M.mem (v (σ i)) ω)
    (hζδ : M.mem ζ (v δ)) (hκV : M.mem (v κ) V)
    (hU : M.mem (v U) V) (hD : M.mem (v D) V) (hu : M.mem (v u) V)
    (above : ∀ i μ, Rd_entry_d i μ H → M.mem μ (v τ))
    (valid : Formula.satisfies ρ (tg_image_m o κ δ l n U D u τ Q w b z r q h σ)) :
    ∃ β T' J' G' E' H' d' j N R' K₀ L F κ' U' D' u' η' C' W,
      It_pnice_d hZF ω c₀ β T' J' G' E' H' ∧ It_extension_d α ξ k T J G E β T' J' G' E' ∧
      Rd_entry_d α d' J' ∧ It_map_d G' k α j ∧ Smem_d I d' N R' ∧ Ic_model_d hZF ω L K₀ N R' ∧
      It_ultra_d hZF ω (v κ) L F d d' j ∧ Wd_crit_d I Y j (v κ) κ' ∧
      (∃ p, Rd_entry_d ξ p E' ∧ It_payload_d p (v κ) L F) ∧
      M.IsLimitOrdinal L ∧ M.mem (v τ) L ∧ M.MemberSubset L κ' ∧
      (∀ i μ, Rd_entry_d i μ H' → M.mem μ κ' ∨ μ = κ') ∧
      Rd_entry_d (v U) U' j ∧ Rd_entry_d (v D) D' j ∧ Rd_entry_d (v u) u' j ∧
      Tg_reply_d I ω (v l) (v n) κ' (v τ) U' D' (v Q) u' (v w) (v b) (fun i => v (σ i))
        (v z) ⟨v r, v q, v h⟩ ∧
      Rd_entry_d η₀ η' j ∧ Rd_entry_d C₀ C' j ∧ Tg_context_d ω N η' C' ∧
      Tg_reply_in_d ω (v l) (v n) κ' (v τ) U' D' (v Q) u' (v w) (v b) (v z)
        (v r) (v q) (v h) (fun i => v (σ i)) C' ∧
      M.mem W X ∧ M.mem W C ∧ Vr_d X L W ∧ Er_level_d N L W ∧ M.mem (v Q) W ∧ M.mem (v w) W ∧
      (∀ μ, M.mem μ L → Ea_agree_d ω μ X N) ∧
      ∃ V₀, M.mem V₀ Y ∧ Vr_d Y (v κ) V₀ ∧ M.mem V₀ N ∧ Vr_d N (v κ) V₀ ∧
        ∀ x, M.mem x V₀ → Rd_entry_d x x j := by
  obtain ⟨A, K₁, R₁, L, F, a, a', B, S₁, f, κ', U', D', u', hA, cut, small,
    _, hκL, hτL, queryRank, loc, inacc, strength, ma, mb, smallUltra, crit, _, limit, iU, iD, iu, reply⟩ :=
    tg_image_read_l hZFC owner.source owner.power context nc ρ o κ δ l n U D u τ Q w b z r q h σ hw hδ regular valid
  have hL := inacc.limit_l (ZF.modelsKP hZF) small.transitive small.theory.algebra.pair
  obtain ⟨β, T', J', G', E', H', d', j, N, R', K₀, W, κ₀,
    next, extension, target, edge, mn, ready, ultra, critical, bound, payload, heights, hW, common, level, agreement, same₀, fixed⟩ :=
    it_working_image_l hZFC tree succ hc hd mx my owner source hA cut hδ small ma mb smallUltra loc strength inacc
      hκL hV rank hV' rank' hζ hζδ hκV
      (fun i μ hm => hL.1.transitive (v τ) hτL μ (above i μ hm))
  have same {x y} (hx : M.mem x V) (entry : Rd_entry_d x y f) : Rd_entry_d x y j := same₀ x y hx entry
  obtain ⟨W₀, hW₀, hWC, rankW₀, hQW₀⟩ := queryRank
  have eW := rankW₀.unique_l hZF owner.source.transitive hW₀ hW common
  subst W₀
  have eq := (ultra.elementary_l hZF my.1 mn.1).1.1.1.2 (v κ) κ₀ κ' critical.image (same hκV crit.image)
  subst κ₀
  obtain ⟨η', C', iη, iC, context'⟩ := prior.map_l hZF source.source.omega source.source.transitive
    ready.source.transitive my mn (ultra.elementary_l hZF my.1 mn.1)
  have hj := ultra.elementary_l hZF my.1 mn.1
  have inner x (hx : M.mem x V) := (prior.read_l hZF source.source).1.transitive V hVC x hx
  have inU := (hj.member_l I hZF source.source.omega my mn (same hU iU) iC).mp (inner _ hU)
  have inD := (hj.member_l I hZF source.source.omega my mn (same hD iD) iC).mp (inner _ hD)
  have inu := (hj.member_l I hZF source.source.omega my mn (same hu iu) iC).mp (inner _ hu)
  have legal := context'.support_reply_l hZF ready.source level hQW₀ bound limit.1 inU inD inu hb hz hσ reply
  have hwW := common.subset_mem_l owner.source.transitive hW hQW₀
    (owner.source.transitive C context.member _ (w.eval ρ).property) reply.1
  exact ⟨β, T', J', G', E', H', d', j, N, R', K₀, L, F, κ', U', D', u', η', C', W,
    next, extension, target, edge, mn, ready, ultra, critical, payload, hL, hτL, bound, heights,
    same hU iU, same hD iD, same hu iu, reply, iη, iC, context', legal, hW, hWC, common, level, hQW₀, hwW, agreement, fixed⟩

end YesMetaZFC.SetTheory.LargeCardinal
