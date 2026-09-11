import YesMetaZFC.Model.ZFC.Pure.PureSourcePacketBounds

/-! # 原传输包图的内部正反射

token 的唯一非结构下降由原仿射前提及正尾守卫推出。
隐含中间参数的量词界保留为实际边界证明，不要求它们出现在头表达式中。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceNumerals
open PureSourceTraceComposition PureSourceHornConstruction
open _root_.YesMetaZFC.Automation ObjectHornSemantics ObjectHornRanking
set_option autoImplicit false
set_option maxRecDepth 4096
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem packet_decrease (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    RankedDecrease 𝒩 ObjectPacket.rules ObjectPacketRanking.plan := by
  intro rule hr values hv _ hGuards hPremises premise hp
  simp only [ObjectPacket.rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact False.elim (List.not_mem_nil hp) | skip
  all_goals rcases List.mem_cons.mp hp with rfl | hp
  all_goals first | exact False.elim (List.not_mem_nil hp) | skip
  all_goals try (rcases List.mem_cons.mp hp with rfl | hp)
  all_goals first | exact False.elim (List.not_mem_nil hp) | skip
  all_goals try obtain rfl := List.mem_singleton.mp hp
  all_goals first
    | exact Or.inl (by decide)
    | exact Or.inr ⟨rfl, PureSourceSyntaxRank.below_value h𝒩 values hv (below_sound (by decide +kernel))⟩
    | skip
  apply Or.inr
  refine ⟨rfl, ?_⟩
  change Fin 6 → 𝒩.Carrier .set at values
  change ∀ i : Fin 6, mem 𝒩 (values i) (w 𝒩) at hv
  change mem 𝒩 (values 4) (values 0)
  have hg : Witness (ObjectHorn.step ObjectPacket.rules) (node 𝒩 0 [values 3, values 4, values 0]) := by
    simpa only [ObjectPacket.tokenLarge, ObjectPacket.node, expr_node, List.map_cons, List.map_nil, exprValue] using!
      hPremises _ List.mem_cons_self
  have hPositive : mem 𝒩 (z 𝒩) (values 4) := hGuards _ List.mem_cons_self
  apply (PureSourcePacketBounds.affine_bounds h𝒩 (hv 3) (hv 4) (hv 0) hg).2
  intro he
  exact empty_spec h𝒩 _ (he ▸ hPositive)

theorem packet_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step ObjectPacket.rules) root) : HornProv 𝒩 ObjectPacket.rules root :=
  horn_ranked_positive h𝒩 _ _ ObjectPacketRanking.shapes (packet_decrease h𝒩) hr hg

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
