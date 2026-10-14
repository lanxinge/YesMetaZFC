import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReturnUnion
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReturnTree
import YesMetaZFC.SetTheory.Descriptive.Tree

/-! # 三张并图沿返回因子给出原树中的共尾分支

并图不必是极限模型的元素。对它们的值逐点施加实际返回映射，有限图
的初等像则由自然数固定性识别。三张图合成一个 ω 列，其共尾多个前缀
属于原树；原树的前缀封闭性随后给出每个内部有限前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_cofinal_branch_d (ω X S f : M.Domain) : Prop := Fn0_d ω X f ∧
  ∀ n, M.mem n ω → ∃ m q, M.mem n m ∧ M.mem m ω ∧ M.mem q S ∧ Tg_graph_d I m q ∧ M.MemberSubset q f

theorem Tg_return_sequence_d.original_l {ω H π P N b D J F c X R S S' σ x A : M.Domain} {g : Fin 3 → M.Domain}
    (h : Tg_return_sequence_d hZF ω H π P N b D J F) (xt : M.TransitiveSet X) (mx : Smem_d I c X R)
    (origin : Tg_return_tree_d hZF ω c X N H π P S S' σ x) (input : Fn0_d ω A x)
    (unions : ∀ a, Tg_return_union_d hZF ω N F a (g a)) :
    ∃ Y q t u, Tg_cofinal_branch_d hZF ω Y S q ∧ Tg_graph_d I ω t ∧ Tg_graph_d I ω u ∧ Tg_join_d I ω x t u q := by
  obtain ⟨d, W, mn, map, _, treeImage, trees, plays⟩ := origin
  have nat := map.natural_l hZF h.omega h.transitive xt mn mx h.omega_mem
  have compose a := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) (unions a).1) map.1.1
  obtain ⟨f₀, fn₀, graph₀⟩ := compose 0
  obtain ⟨f₁, fn₁, graph₁⟩ := compose 1
  obtain ⟨f₂, fn₂, graph₂⟩ := compose 2
  let f : Fin 3 → M.Domain := Fin.cases f₀ (Fin.cases f₁ (fun _ => f₂))
  have fn : ∀ a, M.IsSetFunctionFromTo I (f a) ω X := Fin.cases fn₀ (Fin.cases fn₁ (Fin.cases fn₂ (fun a => Fin.elim0 a)))
  have graph : ∀ a i y, Rd_entry_d i y (f a) ↔ M.mem i ω ∧ ∃ x, Rd_entry_d i x (g a) ∧ Rd_entry_d x y σ :=
    Fin.cases graph₀ (Fin.cases graph₁ (Fin.cases graph₂ (fun a => Fin.elim0 a)))
  have front i y (iy : Rd_entry_d i y f₀) : Rd_entry_d i y x := by
    obtain ⟨hi,z,⟨p,pair,hp⟩,zy⟩ := (graph₀ i y).mp iy
    obtain ⟨j,r,v,jr,code,hp⟩ := ((unions 0).2.1 p).mp hp
    obtain ⟨k,m,_,trace,_,_,_⟩ := h.rows j r v jr code
    obtain ⟨s,is,sub⟩ := plays m k (v 0) (v 1) (v 2) (v 3) (v 4) trace
    have entry : Rd_entry_d i y s := (map.entry_l hZF h.omega h.transitive xt mn mx (nat i hi) zy is).mp ⟨p,pair,hp⟩
    exact entry.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  have fnx := fn0_function_l (ZF.modelsKP hZF) input
  have ex : f₀ = x := fn₀.1.1.eq_of_pairMember_iff hZF.1 fnx.1.1 (fun i y => ⟨front i y,fun iy => by
    obtain ⟨z,_,iz⟩ := fn₀.2.2 i (input.bound_l iy).1
    exact fnx.1.2 i z y (front i z iz) iy ▸ iz⟩)
  obtain ⟨V, Y, q, _, _, fq, join⟩ := tg_join_exists_l I hZF fn₀ fn₁ fn₂
  refine ⟨Y,q,f₁,f₂,⟨fn0_of_function_l (ZF.modelsKP hZF) fq,fun n hn => ?_⟩,
    ⟨fn₁.1,fn₁.2.1⟩,⟨fn₂.1,fn₂.2.1⟩,ex ▸ join⟩
  obtain ⟨z, _, ⟨p, pp, hp⟩⟩ := (unions 2).1.2.1 n hn
  obtain ⟨i, r, v, hr, code, hp⟩ := ((unions 2).2.1 p).mp hp
  obtain ⟨k, m, _, trace, hvω, member, node⟩ := h.rows i r v hr code
  have nlen : M.mem n (v 0) := (node.2.2.1.2 n).mpr ⟨z,p,pp,hp⟩
  have treeEq := trees m k (v 0) (v 1) (v 2) (v 3) (v 4) trace
  obtain ⟨s, _, is⟩ := map.1.1.2.2 (v 2) (member 2)
  obtain ⟨t, _, it⟩ := map.1.1.2.2 (v 3) (member 3)
  obtain ⟨u, _, iu⟩ := map.1.1.2.2 (v 4) (member 4)
  let w : Fin 5 → M.Domain := Fin.cases (v 0) (Fin.cases S (Fin.cases s (Fin.cases t (fun _ => u))))
  have images : ∀ a, Rd_entry_d (v a) (w a) σ := Fin.cases (nat _ hvω)
    (Fin.cases (treeEq.symm ▸ treeImage) (Fin.cases is (Fin.cases it (Fin.cases iu (fun a => Fin.elim0 a)))))
  have new := (map.tg_node_l hZF h.omega h.transitive xt mn mx images).mp node
  have sub : ∀ a : Fin 3, M.MemberSubset (w ([2,3,4].get a)) (f a) := by
    intro a
    have coord := images ([2,3,4].get a)
    have cut := (unions a).2.2 i r v hr code
    have oldGraph : Tg_graph_d I (v 0) (v ([2,3,4].get a)) :=
      Fin.cases node.1 (Fin.cases node.2.1 (Fin.cases node.2.2.1 (fun a => Fin.elim0 a))) a
    have newGraph := (map.tg_graph_l hZF h.omega h.transitive xt mn mx (nat _ hvω) coord).mp oldGraph
    intro p hp
    obtain ⟨j, y, pair⟩ := newGraph.1.1 p hp
    have entry : Rd_entry_d j y (w ([2,3,4].get a)) := ⟨p,pair,hp⟩
    have hj := (newGraph.2 j).mpr ⟨y,entry⟩
    have hjω := h.omega.transitive hZF _ hvω j hj
    obtain ⟨x, ix⟩ := (oldGraph.2 j).mp hj
    have xN := (rd_entry_transitive_l h.transitive (member ([2,3,4].get a)) ix).2
    obtain ⟨y', _, iy⟩ := map.1.1.2.2 x xN
    have iy' := (map.entry_l hZF h.omega h.transitive xt mn mx (nat j hjω) iy coord).mp ix
    have eq := newGraph.1.2 j y' y iy' entry
    obtain ⟨p', pair', hp'⟩ := (graph a j y).mpr ⟨hjω, x, ((cut.2 j x).mp ix).2, eq ▸ iy⟩
    exact kpair_unique_l M hZF.1 pair' pair ▸ hp'
  obtain ⟨_, _, _, q', hq', joined⟩ := new
  refine ⟨v 0, q', nlen, hvω, hq', joined.1, ?_⟩
  intro p hp
  obtain ⟨j, x, pair⟩ := joined.1.1.1 p hp
  have hx : Rd_entry_d j x q' := ⟨p,pair,hp⟩
  have hj := (joined.1.2 j).mpr ⟨x,hx⟩
  obtain ⟨a, b, c, z, y, ha, hb, hc, hz, hy, iy⟩ := joined.2 j hj
  have xy := joined.1.1.2 j x y hx iy
  have inc {a b U V : M.Domain} (sub : M.MemberSubset U V) (h : Rd_entry_d a b U) : Rd_entry_d a b V :=
    h.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩
  obtain ⟨a', b', c', z', y', ha', hb', hc', hz', hy', iy'⟩ := join.2 j (h.omega.transitive hZF _ hvω j hj)
  have ea := fn₀.1.2 j a a' (inc (sub 0) ha) ha'
  have eb := fn₁.1.2 j b b' (inc (sub 1) hb) hb'
  have ec := fn₂.1.2 j c c' (inc (sub 2) hc) hc'
  have ez := kpair_unique_l M hZF.1 hz (eb.symm ▸ ec.symm ▸ hz')
  have ey := kpair_unique_l M hZF.1 hy (ea.symm ▸ ez.symm ▸ hy')
  obtain ⟨r', rp, hq⟩ := iy'
  exact kpair_unique_l M hZF.1 rp ((xy.trans ey) ▸ pair) ▸ hq

theorem Tg_cofinal_branch_d.branch_l {ω X S f A F : M.Domain}
    (h : Tg_cofinal_branch_d hZF ω X S f) (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω A F) (tree : Tree_d F S) : Fn0_d ω A f ∧ Branch_d F S f := by
  have fn := fn0_function_l (ZF.modelsKP hZF) h.1
  have inside {n m q} (nm : M.mem n m) (hm : M.mem m ω) (gq : Tg_graph_d I m q) (sub : M.MemberSubset q f)
      {s} (fs : M.IsSetFunctionFromTo I s n A) (sf : M.MemberSubset s f) : M.MemberSubset s q := by
    intro p hp
    obtain ⟨i,x,pair⟩ := fs.1.1 p hp
    have ix : Rd_entry_d i x s := ⟨p,pair,hp⟩
    have hi := (hw.members_areOrdinals hZF m hm).transitive n nm i (fs.input_mem_of_pairMember ix)
    obtain ⟨y, ⟨r, rp, hr⟩⟩ := (gq.2 i).mp hi
    have eq := fn.1.2 i x y ⟨p,pair,sf p hp⟩ ⟨r,rp,sub r hr⟩
    exact kpair_unique_l M hZF.1 rp (eq ▸ pair) ▸ hr
  refine ⟨?_, fun s hs sub => ?_⟩
  · have bound {i x} (hx : Rd_entry_d i x f) : M.mem x A := by
      obtain ⟨m,q,im,_,hq,gq,sub⟩ := h.2 i (h.1.bound_l hx).1
      obtain ⟨y, ⟨p,pp,hp⟩⟩ := (gq.2 i).mp im
      have eq := fn.1.2 i x y hx ⟨p,pp,sub p hp⟩
      obtain ⟨_,_,fq⟩ := (space q).mp (tree.1 q hq)
      exact eq.symm ▸ fq.output_mem_of_pairMember ⟨p,pp,hp⟩
    exact fn0_of_function_l (ZF.modelsKP hZF) ⟨fn.1,fn.2.1,
      fun i hi => (fn.2.2 i hi).elim fun x hx => ⟨x,bound hx.2,hx.2⟩⟩
  · obtain ⟨n,hn,fs⟩ := (space s).mp hs
    obtain ⟨m,q,nm,hm,hq,gq,qf⟩ := h.2 n hn
    exact tree.2 q hq s hs (inside nm hm gq qf fs sub)

end YesMetaZFC.SetTheory.LargeCardinal
