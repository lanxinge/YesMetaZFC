import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyModel
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankLift
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthRank

/-! # 可数闭工作模型的实际 nice 后继

所属模型可以不同于施加源。原内部共同纤维产生良基超幂，最大强度识别
两侧共同秩段。扩展器来自拥有秩段时，先逐项向上读取原公式，再施加同一扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_model_d.apply_l {ω κ K X R K' Y S L F c : M.Domain}
    (h : Ic_model_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y S)
    (closed : Sc_bounded_omega_closed_d ω Y) (op : Sc_power_d Y) (oc : Sc_cover_d Y)
    (bound : Sc_omega_bound_d ω Y L) (sizes : Sc_rank_size_d I Y L) (agree : Ea_agree_d ω κ X Y)
    (hm : Smem_d I c X R) (loc : It_local_d ω Y κ L F)
    (strength : Ex_strength_d hZF ω κ L Y F) (hL : M.IsLimitOrdinal L) :
    ∃ N V d j K₀ W, Smem_d I d N V ∧ It_ultra_d hZF ω κ L F c d j ∧
      Ic_model_d hZF ω L K₀ N V ∧ M.mem W Y ∧ Vr_d Y L W ∧ Er_level_d N L W ∧
      Sc_rank_size_d I N L ∧ Es_strength_d Y L N ∧ ∀ μ, M.mem μ L → Ea_agree_d ω μ Y N := by
  have data := loc
  obtain ⟨_, _, _, _, pre⟩ := data
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hwL := hL.1.transitive κ pre.1.2.2.2.2.1 ω pre.1.2.2.1
  have below := hL.1.transitive ω hwL
  obtain ⟨P, hP, ps⟩ := op K' owner.finite_mem
  obtain ⟨J, O, Z, A, p, T, U, q, b, C, W, system, limit, model, _, _, collapse⟩ :=
    loc.closed_limit_l hZFC h.source owner closed agree hP ps
  obtain ⟨_, c₀, i, N, e, _, d, V, j, mx, hi, constants, ht, wc, bij, hn, he, _, _, _, hj, js, _⟩ := collapse
  obtain ⟨eq, _⟩ := smem_unique_l I hZF.1 mx hm
  subst c₀
  have ultra : It_ultra_d hZF ω κ L F c d j := ⟨X, R, N, V, J, O, Z, A, p, T, U, q, b, C, W, i, e,
    hm, hn, system, limit, model, wc, bij, he, hi, constants, hj, hj.1.1.1.1,
    fun x y => (js x y).trans ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨hi.1.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩
  obtain ⟨K₁, next⟩ := h.ultra_l hZFC owner agree closed op oc bound sizes hL loc strength hm hn ultra
  have reverse : Ea_agree_d ω κ Y X := fun n D B hn hd sub => (agree n D B hn hd sub).symm
  have family := (loc.measures_l hZF owner hP ps).transfer_l reverse
  have coherent := (loc.coherent_l hZF owner).transfer_l hZF reverse
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive
  have seed := (ep_seed_collapse_l hZF h.source ord.1.transitive hL.1.transitive below family coherent
    (loc.atoms_l hZF owner) ((loc.normal_l hZF owner).transfer_l hZF owner h.source agree.subset_l)
    system limit wc (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)).2
  have hLN := ep_support_mem_l hZFC h.source family coherent system limit model ht hn he seed ord.1 hL.1
  obtain ⟨K₀, ready⟩ := next.rebase_l hZF hLN below
    (sc_ordinal_small_l hZF h.source.omega ht hn next.source.theory hLN hL.1)
  have successor : Ep_successor_d hZF ω κ L X R F N V :=
    ⟨J, O, Z, A, p, T, U, q, b, C, W, d, e, system, limit, model, hn, ht, wc, bij, he⟩
  obtain ⟨W₀, hw, rank, level, sizes', exactness, common⟩ := loc.rank_agree_l hZFC h.source owner ready.source
    agree closed.branch_l op oc ready.hierarchy ready.power sizes hL successor strength
  exact ⟨N, V, d, j, K₀, W₀, hn, ultra, ready, hw, rank, level, sizes', exactness, common⟩

/-- 小秩段中的 nice 判断先向上保持；输出的边实际施加到完整工作源。 -/
theorem Ic_model_d.rank_apply_l {ω κ K X R K' Y S δ A L F c : M.Domain}
    (h : Ic_model_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K' Y S)
    (closed : Sc_bounded_omega_closed_d ω Y) (op : Sc_power_d Y) (oc : Sc_cover_d Y)
    (bound : Sc_omega_bound_d ω Y L) (sizes : Sc_rank_size_d I Y L) (agree : Ea_agree_d ω κ X Y) (hm : Smem_d I c X R)
    (hA : M.mem A Y) (rank : Vr_d Y δ A) (hδ : M.IsLimitOrdinal δ)
    (loc : It_local_d ω A κ L F) (strength : Ex_strength_d hZF ω κ L A F)
    (inaccessible : Sc_inaccessible_d ω A L) :
    It_local_d ω Y κ L F ∧ Ex_strength_d hZF ω κ L Y F ∧ Sc_inaccessible_d ω Y L ∧
      ∃ N V d j K₀ W, Smem_d I d N V ∧ It_ultra_d hZF ω κ L F c d j ∧
        Ic_model_d hZF ω L K₀ N V ∧ M.mem W Y ∧ Vr_d Y L W ∧ Er_level_d N L W ∧
        Sc_rank_size_d I N L ∧ Es_strength_d Y L N ∧ ∀ μ, M.mem μ L → Ea_agree_d ω μ Y N := by
  have up := loc.of_rank_l hZF owner hA rank hδ
  have strong := strength.of_rank_l hZF owner.transitive hA rank hδ
  have card := inaccessible.of_rank_l hZF owner.transitive owner.theory.algebra.pair hA rank hδ
  have hL := card.limit_l (ZF.modelsKP hZF) owner.transitive owner.theory.algebra.pair
  exact ⟨up, strong, card, h.apply_l hZFC owner closed op oc bound sizes agree hm up strong hL⟩

end YesMetaZFC.SetTheory.LargeCardinal
