import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyAttempt

/-! # 联合尝试沿复制树边严格延伸

先从像中的有限行逐坐标回收到原行，再用实际复制方块把旧行值送到新行。
原树的复合律保证所有前驱行同时延伸；长度的严格增加给出真正的尝试树边。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.attempt_extend_l {ω T Q G E L H Q' G' U k l X A π z Z α Y B σ v V β
    S W o q q' D D' F P P' s t g : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G')
    (tree : It_diagram_d hZF ω ω T Q G) (en : Ja_enum_d I ω ω Q U)
    (left : Ic_at_d H k X A π z Z α) (right : Ic_at_d H l Y B σ v V β)
    (edge : It_map_d G' k l g) (lt : M.mem k l)
    (node : Ja_node_d I ω T Q G U A S o q k P)
    (next : Ja_node_d I ω T Q G U B W o q' l P')
    (values : ∀ i p, Rd_entry_d i p P → ∀ n y, Rd_entry_d n y p ↔ M.mem n k ∧ Ja_value_d G U k π i n y)
    (later : ∀ i p, Rd_entry_d i p P' → ∀ n y, Rd_entry_d n y p ↔ M.mem n l ∧ Ja_value_d G U l σ i n y)
    (pair : KPair_d M s k P) (pair' : KPair_d M t l P') (hs : M.mem s D)
    (dd : Rd_entry_d D D' g) (space : Ja_space_d I ω T Q G U B W o q' D' F) :
    ∃ u, Rd_entry_d s u g ∧ Rd_entry_d t u F := by
  obtain ⟨c, hc, hz, row⟩ := hist.row_l hZF left
  obtain ⟨d, hd, hv, row'⟩ := hist.row_l hZF right
  obtain ⟨Rx, _, Rz, _, _, _, _, mx, _, mz, _, _, source, _, _, _, pi⟩ := row
  obtain ⟨Ry, _, Rv, _, _, _, _, my, _, mv, _, _, target, _, _, _, _⟩ := row'
  have hω := source.source.omega
  have j := hist.diagram.elementary k l g z Z Rz v V Rv edge hz hv mz.1 mv.1
  have hk := j.natural_l hZF hω source.source.transitive target.source.transitive mz mv source.source.omega_mem k node.length
  have hsZ := source.source.transitive D (j.1.1.input_mem_of_pairMember dd) s hs
  have hP := (pair.mem_l M source.source.transitive hsZ).2
  obtain ⟨u, hu, su⟩ := j.1.1.2.2 s hsZ
  obtain ⟨P₁, _, pp⟩ := j.1.1.2.2 P hP
  have pair₁ := (j.kpair_l hZF hω source.source.transitive target.source.transitive mz mv su hk pp).mp pair
  have huD := ((mv.2 u D').mp ((j.relation_l I hZF hω mz.1 mv.1 su dd).mp
    ((mz.2 s D).mpr ⟨hsZ, j.1.1.input_mem_of_pairMember dd, hs⟩))).2.2
  obtain ⟨k₁, P₂, pair₂, shifted⟩ := (space.nodes u).mp huD
  obtain ⟨ek, ep⟩ := kpair_injective_l M pair₂ pair₁
  subst k₁ P₂
  have kl := hist.diagram.map_bound_l hZF edge
  obtain ⟨f, hf⟩ := tree.map_l hZF kl
  have original := tree.elementary k l f c X Rx d Y Ry hf hc hd mx.1 my.1
  have natural := j.natural_l hZF hω source.source.transitive target.source.transitive mz mv source.source.omega_mem
  have extend i p r (hip : Rd_entry_d i p P₁) (hir : Rd_entry_d i r P') : M.MemberSubset p r := by
    have ik := (shifted.domain i).mp ⟨p, hip⟩
    have hi := (tree.order.bound i k ik).1
    obtain ⟨a, C, R, ha, mc⟩ := tree.model_l hZF hi
    obtain ⟨e, he⟩ := (en.domain i).mp hi
    obtain ⟨p₀, hp₀⟩ := (node.domain i).mpr ik
    have fn₀ := (node.rows i p₀ a C R e hp₀ ha mc.1 he).1
    have fn := (shifted.rows i p a C R e hip ha mc.1 he).1
    obtain ⟨p₁, _, p01⟩ := j.1.1.2.2 p₀ (rd_entry_transitive_l source.source.transitive hP hp₀).2
    have entry := (j.entry_l hZF hω source.source.transitive target.source.transitive mz mv (natural i hi) p01 pp).mp hp₀
    have eq := shifted.function.2 i p₁ p entry hip
    subst p₁
    intro a₁ ha₁
    obtain ⟨n, hn, y, _, pairy⟩ := fn.1 a₁ ha₁
    have hny : Rd_entry_d n y p := ⟨a₁, pairy, ha₁⟩
    obtain ⟨x, _, hnx⟩ := fn₀.2.1 n hn
    obtain ⟨y₀, _, xy⟩ := j.1.1.2.2 x (rd_entry_transitive_l source.source.transitive
      (rd_entry_transitive_l source.source.transitive hP hp₀).2 hnx).2
    have hny₀ := (j.entry_l hZF hω source.source.transitive target.source.transitive mz mv
      (natural n (hω.transitive hZF k node.length n hn)) xy p01).mp hnx
    have eq := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 n y₀ y hny₀ hny
    subst y₀
    obtain ⟨_, e₀, f₀, b, w, he₀, hf₀, hnb, hbw, hwx⟩ := (values i p₀ hp₀ n x).mp hnx
    obtain ⟨w', _, hww⟩ := original.1.1.2.2 w (pi.1.1.input_mem_of_pairMember hwx)
    obtain ⟨f₁, hf₁⟩ := tree.map_l hZF (tree.order.trans i k l ik kl)
    have hwy := hist.squares k l X A π z Z α Y B σ v V β f g left right hf edge w x w' y hwx hww xy
    have hnr := (later i r hir n y).mpr ⟨(hω.members_areOrdinals hZF l next.length).transitive k lt n hn,
      e₀, f₁, b, w', he₀, hf₁, hnb, tree.comp i k l f₀ f f₁ hf₀ hf hf₁ b w w' hbw hww, hwy⟩
    obtain ⟨a₂, pair₂, ha₂⟩ := hnr
    exact kpair_unique_l M hZF.1 pair₂ pairy ▸ ha₂
  exact ⟨u, su, (space.edges u t).mpr ⟨huD, (space.nodes t).mpr ⟨l, P', pair', next⟩,
    k, P₁, l, P', pair₁, pair', lt, kl, extend⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
