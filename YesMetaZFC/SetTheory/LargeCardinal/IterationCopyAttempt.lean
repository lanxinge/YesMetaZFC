import YesMetaZFC.SetTheory.LargeCardinal.IterationCopyHistory
import YesMetaZFC.SetTheory.LargeCardinal.IterationCountableFixed
import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptRank

/-! # 复制树结点给出像尝试树中的实际节点

原树编码由公共可数载体固定，目标秩段由复制图的方块确定。末结点嵌入
和根图的像满足同一指定条件；联合尝试绝对性随后把实际有限节点放入像树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_history_d.attempt_l {ω T Q G E L H Q' G' U C ι o X₀ A₀ π₀ z₀ Z₀ α₀
    a₀ S₀ B R i X A π z Z α : M.Domain}
    (hist : Ic_history_d hZF ω T Q G E L ω H T Q' G')
    (tree : It_diagram_d hZF ω ω T Q G) (en : Ja_enum_d I ω ω Q U)
    (start : Ic_at_d H o X₀ A₀ π₀ z₀ Z₀ α₀) (ho : ∀ x, ¬ M.mem x o)
    (first : Smem_d I a₀ A₀ S₀) (space : Ja_space_d I ω T Q G U A₀ S₀ o π₀ B R)
    (hC : M.mem C Z₀) (hι : M.mem ι Z₀) (trans : M.TransitiveSet C) (inj : M.IsSetInjectionFromTo I ι C ω)
    (cover : ∀ i a X R, Rd_entry_d i a Q → KPair_d M a X R → M.MemberSubset X C)
    (hT : M.mem T Z₀) (hQ : M.mem Q Z₀) (hG : M.mem G Z₀) (hU : M.mem U Z₀)
    (hπ : M.mem π₀ Z₀) (hB : M.mem B Z₀) (hR : M.mem R Z₀) (here : Ic_at_d H i X A π z Z α) :
    ∃ g a S q B' R' P s, It_map_d G' o i g ∧ Smem_d I a A S ∧
      Rd_entry_d π₀ q g ∧ Rd_entry_d B B' g ∧ Rd_entry_d R R' g ∧
      Ja_space_d I ω T Q G U A S o q B' R' ∧ KPair_d M s i P ∧ M.mem s B' ∧
      Ja_node_d I ω T Q G U A S o q i P ∧
      ∀ k p, Rd_entry_d k p P → ∀ n y, Rd_entry_d n y p ↔ M.mem n i ∧ Ja_value_d G U i π k n y := by
  obtain ⟨c₀, hc₀, hz₀, row₀⟩ := hist.row_l hZF start
  obtain ⟨c, hc, hz, row⟩ := hist.row_l hZF here
  obtain ⟨V₀, W₀, R₀, b₀, _, _, _, mx₀, _, mz₀, _, _, full₀, hA₀, _, _, old⟩ := row₀
  obtain ⟨V, S, Rz, a, _, _, _, mx, ma, mz, _, _, full, hA, _, _, copied⟩ := row
  have hω := full₀.source.omega
  have hi := (tree.model_domain i).mpr ⟨c, hc⟩
  have hoω := (tree.model_domain o).mpr ⟨c₀, hc₀⟩
  have root := tree.order.root_l hZF ho i hi
  obtain ⟨g, hg⟩ := hist.diagram.map_l hZF root
  have j := hist.diagram.elementary o i g z₀ Z₀ R₀ z Z Rz hg hz₀ hz mz₀.1 mz.1
  obtain ⟨cc, point, tt, qq, gg, uu⟩ := it_countable_fixed_l hZF hω tree en
    full₀.source.transitive full.source.transitive mz₀ mz j full₀.source.theory.algebra
    full₀.source.omega_mem hC hι trans inj cover hT hQ hG hU
  have aa := hist.cuts o i X₀ A₀ π₀ z₀ Z₀ α₀ X A π z Z α g start here hg
  have ss := ep_set_membership_l hZF full₀.source full.source mz₀ mz j first ma aa
  obtain ⟨q, _, pq⟩ := j.1.1.2.2 π₀ hπ
  obtain ⟨B', _, bb⟩ := j.1.1.2.2 B hB
  obtain ⟨R', _, rr⟩ := j.1.1.2.2 R hR
  have ww := j.omega_l I hZF hω full₀.source.transitive full.source.transitive mz₀ mz full₀.source.omega_mem
  have oo := j.natural_l hZF hω full₀.source.transitive full.source.transitive mz₀ mz full₀.source.omega_mem o hoω
  let ρ (A S q B R : M.Domain) : Env M 11 := ⟨Fin.cases ω (Fin.cases T (Fin.cases Q
    (Fin.cases G (Fin.cases U (Fin.cases A (Fin.cases S (Fin.cases o (Fin.cases q (Fin.cases B (fun _ => R)))))))))), fun _ => ω⟩
  have images : ∀ k, Rd_entry_d ((ρ A₀ S₀ π₀ B R).bound k) ((ρ A S q B' R').bound k) g :=
    Fin.cases ww (Fin.cases tt (Fin.cases qq (Fin.cases gg (Fin.cases uu
      (Fin.cases aa (Fin.cases ss (Fin.cases oo (Fin.cases pq (Fin.cases bb (fun _ => rr))))))))))
  have image := space.full_image_l hZF full₀.source full.source mz₀ mz j
    (ρ A₀ S₀ π₀ B R) (ρ A S q B' R') rfl images tree en
  have hx := (mx₀.1.1.mem_l M full₀.source.transitive (rd_entry_transitive_l full₀.source.transitive hQ hc₀).2).1
  have fixed := j.fixed_subset_l hZF hω full₀.source.transitive full.source.transitive mz₀ mz
    cc point hx (cover o c₀ X₀ V₀ hc₀ mx₀.1.1)
  have fn := (j.function_l hZF hω full₀.source.transitive full.source.transitive mz₀ mz fixed aa pq).mp
    (fn0_of_function_l (ZF.modelsKP hZF) old.1.1)
  obtain ⟨f, hf⟩ := tree.map_l hZF root
  have native := tree.elementary o i f c₀ X₀ V₀ c X V hf hc₀ hc mx₀.1 mx.1
  have prescribed x y (hxy : Rd_entry_d x y q) :
      ∃ f v, It_map_d G o i f ∧ Rd_entry_d x v f ∧ Rd_entry_d v y π := by
    have hx₀ := (fn.bound_l hxy).1
    obtain ⟨u, hu, hxu⟩ := old.1.1.2.2 x hx₀
    obtain ⟨v, _, hxv⟩ := native.1.1.2.2 x hx₀
    obtain ⟨w, _, huw⟩ := j.1.1.2.2 u (full₀.source.transitive A₀ hA₀ u hu)
    have hxy' := (j.entry_l hZF hω full₀.source.transitive full.source.transitive mz₀ mz
      (point x (cover o c₀ X₀ V₀ hc₀ mx₀.1.1 x hx₀)) huw pq).mp hxu
    have eq := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 x w y hxy' hxy
    exact ⟨f, v, hf, hxv, eq ▸ hist.squares o i X₀ A₀ π₀ z₀ Z₀ α₀ X A π z Z α f g
      start here hf hg x u v w hxu hxv huw⟩
  obtain ⟨P, node, values⟩ := ja_node_of_l hZF hω tree en hi hc mx.1 ma.1 copied prescribed
  obtain ⟨s, pair⟩ := (I).total i P
  exact ⟨g, a, S, q, B', R', P, s, hg, ma, pq, bb, rr, image, pair,
    (image.nodes s).mpr ⟨i, P, pair, node⟩, node, values⟩

end YesMetaZFC.SetTheory.LargeCardinal
