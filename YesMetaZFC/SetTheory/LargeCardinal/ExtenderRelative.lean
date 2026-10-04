import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSource
import YesMetaZFC.SetTheory.Filter.SourceUltrafilter

/-! # 相对于源模型的有限支撑测度族

只要求测度决定源中的子集，协调律也只作用于这些子集。完整背景测度
给出原有实例；同一有限幂上的子集一致性将整张测度图转用到另一模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

structure Em_source_d (ω κ L X F : M.Domain) : Prop where
  total : ∀ n a, M.mem n ω → Fn0_d n L a → ∃ U, Rd_entry_d a U F
  function : ∀ a U V, Rd_entry_d a U F → Rd_entry_d a V F → U = V
  measure : ∀ a U, Rd_entry_d a U F → ∃ n D, M.mem n ω ∧ Fn0_d n L a ∧
    Ep_space_d κ n D ∧ Sf_ultra_d X D U

def Ec_source_d (I : kpair_convention_l.Interpretation M) (ω κ L X F : M.Domain) : Prop :=
  ∀ m n q a b U V A, M.mem m ω → M.mem n ω → M.mem A X → Es_reindex_d I κ L F m n q a b U V A

/-- 精确的施加条件：所有内部有限 κ 幂上的源子集一致。 -/
def Ea_agree_d (ω κ X Y : M.Domain) : Prop := ∀ n D A, M.mem n ω → Ep_space_d κ n D →
  M.MemberSubset A D → (M.mem A X ↔ M.mem A Y)

theorem Em_source_d.at_l (hE : Extensional M) {ω κ L X F a U n D : M.Domain}
    (h : Em_source_d ω κ L X F) (ha : Rd_entry_d a U F) (hn : Fn0_d n L a)
    (hD : Ep_space_d κ n D) : Sf_ultra_d X D U := by
  obtain ⟨m, E, _, hm, he, hu⟩ := h.measure a U ha
  have en := hm.domain_eq_l hE hn
  subst m
  exact hE.eq_of_same_members E D (fun s => (he s).trans (hD s).symm) ▸ hu

theorem Em_family_d.source_l (hZF : M.Models ZF) {ω κ L F : M.Domain}
    (h : Em_family_d ω κ L F) (X : M.Domain) : Em_source_d ω κ L X F := by
  refine ⟨h.total, h.function, fun a U ha => ?_⟩
  obtain ⟨n, D, hn, hna, hd, hu⟩ := h.measure a U ha
  exact ⟨n, D, hn, hna, hd, hu.source_l hZF X⟩

theorem Es_coherent_d.source_l (I : kpair_convention_l.Interpretation M) {ω κ L F : M.Domain}
    (h : Es_coherent_d I ω κ L F) (X : M.Domain) : Ec_source_d I ω κ L X F :=
  fun m n q a b U V A hm hn _ => h m n q a b U V A hm hn

theorem Em_source_d.transfer_l {ω κ L X Y F : M.Domain} (h : Em_source_d ω κ L X F)
    (agree : Ea_agree_d ω κ X Y) : Em_source_d ω κ L Y F := by
  refine ⟨h.total, h.function, fun a U ha => ?_⟩
  obtain ⟨n, D, hn, hna, hd, hu⟩ := h.measure a U ha
  exact ⟨n, D, hn, hna, hd, hu.transfer_l (fun A hA => agree n D A hn hd hA)⟩

theorem Ec_source_d.transfer_l (hZF : M.Models ZF) {ω κ L X Y F : M.Domain}
    (h : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F) (agree : Ea_agree_d ω κ X Y) :
    Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L Y F := by
  intro m n q a b U V A hm hn hAY hq ha hb haV hbU hA
  obtain ⟨D, hd⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) m κ
  have space : Ep_space_d κ m D := fun s => (hd s).trans
    ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩
  exact h m n q a b U V A hm hn ((agree m D A hm space (fun s hs => (space s).mpr (hA s hs))).mpr hAY)
    hq ha hb haV hbU hA

end YesMetaZFC.SetTheory.LargeCardinal
