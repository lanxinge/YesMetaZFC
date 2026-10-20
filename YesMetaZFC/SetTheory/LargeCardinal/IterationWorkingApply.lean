import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyApply
import YesMetaZFC.SetTheory.LargeCardinal.IterationNice
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCriticalPoint
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCommonImage
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRankFixed

/-! # 双模型迭代的实际 nice 后继

扩展器在当前所属模型的秩段中构造，施加源可以是树中的另一模型。
有限幂子集一致性给出跨源施加；内部不可达性自动提供正则界和秩枚举。
同一条超幂边保留临界点、可数闭工作模型、共同秩段，并实际加入原 nice 树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_working_rank_apply_l {ω c₀ α ξ T Q G E H k c d X R Y S κ K K' δ A L F : M.Domain}
    (tree : It_pnice_d hZF ω c₀ α T Q G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (owner : Ic_model_d hZF ω κ K X R) (source : Ic_model_d hZF ω κ K' Y S)
    (agree : Ea_agree_d ω κ Y X) (hA : M.mem A X) (rank : Vr_d X δ A) (hδ : M.IsLimitOrdinal δ)
    (loc : It_local_d ω A κ L F) (strength : Ex_strength_d hZF ω κ L A F)
    (inacc : Sc_inaccessible_d ω A L) (above : ∀ i μ, Rd_entry_d i μ H → M.mem μ L) :
    ∃ β U Q' G' E' H' b j p N V K₀ W κ',
      It_pnice_d hZF ω c₀ β U Q' G' E' H' ∧ It_extension_d α ξ k T Q G E β U Q' G' E' ∧
      Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧ It_ultra_d hZF ω κ L F d b j ∧
      It_payload_d p κ L F ∧ Rd_entry_d ξ p E' ∧ Rd_entry_d ξ L H' ∧
      Smem_d I b N V ∧ Ic_model_d hZF ω L K₀ N V ∧ Wd_crit_d I Y j κ κ' ∧ M.MemberSubset L κ' ∧
      M.mem W X ∧ Vr_d X L W ∧ Er_level_d N L W ∧ Sc_rank_size_d I N L ∧ Es_strength_d X L N ∧
      ∀ μ, M.mem μ L → Ea_agree_d ω μ X N := by
  have localFull := loc.of_rank_l hZF owner.source hA rank hδ
  have strongFull := strength.of_rank_l hZF owner.source.transitive hA rank hδ
  have inaccFull := inacc.of_rank_l hZF owner.source.transitive owner.source.theory.algebra.pair hA rank hδ
  have hL := inaccFull.limit_l (ZF.modelsKP hZF) owner.source.transitive owner.source.theory.algebra.pair
  have localCopy := localFull
  obtain ⟨_, _, _, _, pre⟩ := localCopy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hκL : M.mem κ L := pre.1.2.2.2.2.1
  have hωL : M.mem ω L := hL.1.transitive κ hκL ω pre.1.2.2.1
  obtain ⟨regular, sizes⟩ := owner.inaccessible L inaccFull
  obtain ⟨N, V, b, j, K₀, W, target, ultra, ready, hW, common, level, sizes', exactness, agreement⟩ :=
    source.apply_l hZFC owner.source (owner.closed.bounded_l owner.source.transitive) owner.power owner.cover
      (regular ω hωL) sizes agree my localFull strongFull hL
  have hj := ultra.elementary_l hZF my.1 target.1
  obtain ⟨κ', _, hκj⟩ := hj.1.1.2.2 κ source.source.cardinal_mem
  obtain ⟨P, hP, power⟩ := owner.power K owner.source.finite_mem
  have reverse : Ea_agree_d ω κ X Y := fun n D B hn hd sub => (agree n D B hn hd sub).symm
  have family := (localFull.measures_l hZF owner.source.omega (owner.source.read_source_l hZF) owner.source.code owner.source.theory
    (sf_finite_power_l hZF owner.source.omega owner.source.transitive owner.source.code owner.source.theory owner.source.finite hP power)).transfer_l reverse
  have critical := ultra.critical_l hZF source.source family owner.source agree localFull hκL my target hκj
  have bound := ultra.support_l hZF source.source family
    ((localFull.coherent_l hZF (owner.source.read_source_l hZF)).transfer_l hZF reverse) (localFull.atoms_l hZF (owner.source.read_source_l hZF))
    ((localFull.normal_l hZF (owner.source.read_source_l hZF)).transfer_l hZF owner.source source.source agree.subset_l)
    critical.ordinal hL.1 (hL.1.transitive ω hωL) my target hκj
  obtain ⟨K₁, omegaSource⟩ := ready.source.rebase_l hZF ready.source.omega_mem
    (fun _ h => h) (ready.source.cardinal_small.mono_l ready.source.below)
  obtain ⟨β, U, Q', G', E', H', p, next, extension, hb, edge, payload, move, support⟩ :=
    it_pnice_apply_l hZF tree succ hc hd mx my localFull reverse ultra ⟨N, V, K₁, target, omegaSource⟩
      strongFull inaccFull above
  exact ⟨β, U, Q', G', E', H', b, j, p, N, V, K₀, W, κ', next, extension, hb, edge, ultra,
    payload, move, support, target, ready, critical, bound, hW, common, level, sizes', exactness, agreement⟩

/-- 共同极限秩段上的原小超幂像，逐项就是新增完整树边的像。 -/
theorem it_working_image_l {ω c₀ α ξ T Q G E H k c d X R Y S κ K K' δ A L F
    K₁ R₁ a a' B S₁ f ζ V : M.Domain}
    (tree : It_pnice_d hZF ω c₀ α T Q G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (owner : Ic_model_d hZF ω κ K X R) (source : Ic_model_d hZF ω κ K' Y S)
    (hA : M.mem A X) (cut : Vr_d X δ A) (hδ : M.IsLimitOrdinal δ)
    (small : Ep_source_d hZF ω κ K₁ A R₁) (ma : Smem_d I a A R₁) (mb : Smem_d I a' B S₁)
    (smallUltra : It_ultra_d hZF ω κ L F a a' f)
    (loc : It_local_d ω A κ L F) (strength : Ex_strength_d hZF ω κ L A F)
    (inacc : Sc_inaccessible_d ω A L) (hκL : M.mem κ L)
    (hV : M.mem V X) (rank : Vr_d X ζ V)
    (hV' : M.mem V Y) (rank' : Vr_d Y ζ V) (hζ : M.IsLimitOrdinal ζ)
    (hζδ : M.mem ζ δ) (hκV : M.mem κ V) (above : ∀ i μ, Rd_entry_d i μ H → M.mem μ L) :
    ∃ β T' Q' G' E' H' d' j N R' K₀ W κ',
      It_pnice_d hZF ω c₀ β T' Q' G' E' H' ∧ It_extension_d α ξ k T Q G E β T' Q' G' E' ∧
      Rd_entry_d α d' Q' ∧ It_map_d G' k α j ∧ Smem_d I d' N R' ∧ Ic_model_d hZF ω L K₀ N R' ∧
      It_ultra_d hZF ω κ L F d d' j ∧ Wd_crit_d I Y j κ κ' ∧ M.MemberSubset L κ' ∧
      (∃ p, Rd_entry_d ξ p E' ∧ It_payload_d p κ L F) ∧
      (∀ i μ, Rd_entry_d i μ H' → M.mem μ κ' ∨ μ = κ') ∧
      M.mem W X ∧ Vr_d X L W ∧ Er_level_d N L W ∧ (∀ μ, M.mem μ L → Ea_agree_d ω μ X N) ∧
      (∀ x y, M.mem x V → Rd_entry_d x y f → Rd_entry_d x y j) ∧
      ∃ V₀, M.mem V₀ Y ∧ Vr_d Y κ V₀ ∧ M.mem V₀ N ∧ Vr_d N κ V₀ ∧
        ∀ x, M.mem x V₀ → Rd_entry_d x x j := by
  have hζA := cut.ordinal_subset_l hZF owner.source.transitive hA ζ hζδ
  obtain ⟨hVA, cutV⟩ := Vr_d.rank_l hZF owner.source.transitive hA cut hδ hζA hV rank
  have agree : Ea_agree_d ω κ Y X := fun n D B hn hd sub =>
    ((source.source.rank_agree_l hZF hV' rank' hζ hκV n D B hn hd sub).symm).trans
      (owner.source.rank_agree_l hZF hV rank hζ hκV n D B hn hd sub)
  obtain ⟨β, T', Q', G', E', H', d', j, p, N, R', K₀, W, κ', next, extension, target, edge, ultra,
    payload, entry, support, mn, ready, critical, bound, hW, common, level, _, _, agreement⟩ :=
    it_working_rank_apply_l hZFC tree succ hc hd mx my owner source agree hA cut hδ loc strength inacc above
  have powerA := owner.power.rank_l hZF owner.source.transitive hA cut hδ
  obtain ⟨P, hP, subsets⟩ := powerA K₁ small.finite_mem
  have ord := loc.ordinals_l (ZF.modelsKP hZF) small.transitive
  have same := it_ultra_common_l hZF small source.source powerA loc.2.2.1 loc.2.2.2.1
    (loc.measures_l hZF small.omega (small.read_source_l hZF) small.code small.theory
      (sf_finite_power_l hZF small.omega small.transitive small.code small.theory small.finite hP subsets)) ma my mb mn smallUltra ultra hVA cutV hV' rank' hζ hκV
  obtain ⟨V₀, hV₀, r₀⟩ := owner.hierarchy κ owner.source.cardinal_mem ord.1
  obtain ⟨hV₀V, rV⟩ := rank.rank_l hZF owner.source.transitive hV hζ hκV hV₀ r₀
  have hV₀Y := source.source.transitive V hV' V₀ hV₀V
  have rY := rank'.of_rank_l hZF source.source.transitive hV' hV₀V rV
  have hL := inacc.limit_l (ZF.modelsKP hZF) small.transitive small.theory.algebra.pair
  have upper : M.mem L κ' ∨ L = κ' := by
    rcases hL.1.trichotomy hZF.1 critical.ordinal_image (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) L κ') with eq | lt | gt
    · exact Or.inr (hZF.1.eq_of_same_members L κ' eq)
    · exact Or.inl lt
    · exact ((KP.mem_irrefl_d (ZF.modelsKP hZF)) κ' (bound κ' gt)).elim
  have heights i μ (hm : Rd_entry_d i μ H') : M.mem μ κ' ∨ μ = κ' :=
    (next.last_bound_l hZF extension.1 succ support i μ hm).elim
      (fun lt => Or.inl (bound μ lt)) (fun eq => eq.symm ▸ upper)
  obtain ⟨hV₀W, rW⟩ := common.rank_l hZF owner.source.transitive hW hL
    (common.ordinal_subset_l hZF owner.source.transitive hW κ hκL) hV₀ r₀
  have hV₀N := ready.source.transitive W level.member V₀ hV₀W
  have rN := level.hierarchy.of_rank_l hZF ready.source.transitive level.member hV₀W rW
  have fixed := (ultra.elementary_l hZF my.1 mn.1).rank_fixed_l hZF source.source.omega
    source.source.transitive ready.source.transitive my mn critical.image critical.fixed hV₀Y rY hV₀N rN
  exact ⟨β, T', Q', G', E', H', d', j, N, R', K₀, W, κ', next, extension, target, edge, mn, ready,
    ultra, critical, bound, ⟨p, entry, payload⟩, heights, hW, common, level, agreement, same, V₀, hV₀Y, rY, hV₀N, rN, fixed⟩

end YesMetaZFC.SetTheory.LargeCardinal
