import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOddLimit

/-! # 指定共尾分支上的实际恢复图

直接把各份奇数存档送入给定极限锥。恒等图只统一原存档的读法，取自实际
传递包络；目标无需返回原模型。良基分支的锥由原坍塌定理构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.branch_limit_l {ω c o C γ Z A D f b d N W P : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (archive : M.IsSetFunction I (U 5))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (branch : It_branch_d ω (U 0) b) (mn : Smem_d I d N W) (nt : M.TransitiveSet N)
    (hwN : M.mem ω N) (cone : It_cone_d hZF ω b (U 1) (U 2) d N W P) :
    ∃ π, (∀ x y, Rd_entry_d x y π → x = y) ∧ Tg_odd_limit_d hZF ω (U 0) (U 2) b (U 5) π N P := by
  have hw := tree.tree.omega
  obtain ⟨r, pack⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) (fun i : Fin 4 => [ω,U 1,U 2,U 5].get i)
  obtain ⟨K, hrK, kt⟩ := ZF.mem_hull_l M hZF I r
  have bound := Rt_tuple_d.members_l pack kt hrK
  obtain ⟨k, R, mk⟩ := smdl_membership_l I hZF ⟨ω, bound 0⟩
  obtain ⟨π, identity, values⟩ := smap_identity_l I hZF (X := K) (c := k) hw
  have models i c (hc : Rd_entry_d i c (U 1)) : ∃ X R, Smem_d I c X R ∧ M.TransitiveSet X := by
    obtain ⟨X, R, _, mx, source⟩ := tree.tree.sources i c hc
    exact ⟨X, R, mx, source.transitive⟩
  have ar := h.archive_l hZF hw columns
  have compatible := it_cone_pull_subset_l hZF hw kt kt nt mk mk mn identity (bound 0) (bound 1)
    ((values _ _).mpr ⟨bound 2, rfl⟩) tree.tree.diagram tree.tree.diagram models cone.toIt_embedding_d
  have growth := compatible.odd_l hZF hw tree.tree.diagram models ar.2.1 ar.2.2
  have nodes : ∀ m i r t₀, M.mem i b → Rd_entry_d m r (U 5) → KPair_d M r i t₀ → ∃ n S s t g,
      M.mem n ω ∧ M.mem S N ∧ M.mem s N ∧ M.mem t N ∧ M.mem g N ∧
      Tg_node_d I n S s t g ∧ Tg_return_node_d ω (U 5) π P m i n S s t g := by
    intro m i r t₀ hi hr pair
    obtain ⟨p, pr, hp⟩ := hr
    obtain ⟨v, l, z, hz, code, hp⟩ := (columns 5 p).mp hp
    obtain ⟨i', Y, R', μ, K', η, C', L, V, q, cell, saved, _⟩ := (h.read_l hZF hz code).1.past.rows m r ⟨p, pr, hp⟩
    have eq : i' = i := (kpair_injective_l M cell.choose_spec.1 pair).1
    subst i'
    have row : Tg_past_at_d (U 5) m i Y R' μ K' η C' L V q :=
      ⟨r, ⟨p, pr, (columns 5 p).mpr ⟨v, l, z, hz, code, hp⟩⟩, cell⟩
    obtain ⟨a, ha, my⟩ := ar.2.1 m i Y R' μ K' η C' L V q row
    have yK := (my.1.1.mem_l M kt (rd_entry_transitive_l kt (bound 1) ha).2).1
    obtain ⟨ρ, cq, _, _, _⟩ := saved.read_l hZF ⟨⟨ω, saved.context.omega⟩⟩
    obtain ⟨hn, member, node⟩ := saved.node_l hZF cq
    let w : Fin 54 → M.Domain := fun a => (ρ.bound a).val
    have fixed a : Rd_entry_d (w a) (w a) π := (values _ _).mpr ⟨kt Y yK (w a) (member a), rfl⟩
    obtain ⟨j, hj⟩ := (cone.domain i).mp hi
    have leg := cone.elementary i j a Y R' hj ha my.1
    obtain ⟨S, hS, iS⟩ := leg.1.1.2.2 (w 19) (member 19)
    obtain ⟨s, hs, is⟩ := leg.1.1.2.2 (w 40) (member 40)
    obtain ⟨t, ht, it⟩ := leg.1.1.2.2 (w 41) (member 41)
    obtain ⟨g, hg, ig⟩ := leg.1.1.2.2 (w 42) (member 42)
    have nat := leg.natural_l hZF hw saved.source.source.transitive nt my mn saved.source.source.omega_mem (w 22) hn
    have image : ∀ a : Fin 5, Rd_entry_d ([w 22,w 19,w 40,w 41,w 42].get a) ([w 22,S,s,t,g].get a) j :=
      Fin.cases nat (Fin.cases iS (Fin.cases is (Fin.cases it (Fin.cases ig (fun a => Fin.elim0 a)))))
    exact ⟨w 22, S, s, t, g, hn, hS, hs, ht, hg,
      (leg.tg_node_l hZF hw saved.source.source.transitive nt my mn image).mp node,
      Y, R', μ, K', η, C', L, V, q, w, row, cq, rfl,
      w 19, w 40, w 41, w 42, j, fixed 19, fixed 40, fixed 41, fixed 42, hj, iS, is, it, ig⟩
  refine ⟨π, fun x y h => ((values x y).mp h).2,
    ⟨nt, hwN, identity.1.2, cone.function, ?_, nodes,
      growth.growth_l hZF hw tree.tree.diagram.order branch archive nodes⟩⟩
  intro i j hij
  obtain ⟨c, hc⟩ := (tree.tree.diagram.model_domain i).mp (branch.subset i ((cone.domain i).mpr ⟨j, hij⟩))
  obtain ⟨X, R, mx, _⟩ := models i c hc
  exact (cone.elementary i j c X R hij hc mx.1).1.1.1

end YesMetaZFC.SetTheory.LargeCardinal
