import YesMetaZFC.SetTheory.LargeCardinal.Game.RunMove
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode

/-! # 并历史中每份实数存档仍是同一原对局的前缀

比较某一坐标时，将存档与该坐标所属的轮次放到共同较晚阶段。
事件单值性给出字母相等；旧根图对固定锚点的恒等性给出返回所需的根像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_archive_play_d (ω H G o X Z f : M.Domain) : Prop := ∀ m i Y R μ K η C L V q,
  ∀ v : Fin 54 → M.Domain, Tg_past_at_d H m i Y R μ K η C L V q → Tg_saved_code_d Y R ω V q v →
    M.mem (v 40) X ∧ M.mem (v 40) Z ∧ M.MemberSubset (v 40) f ∧
      ∃ j, It_map_d G o i j ∧ Rd_entry_d (v 40) (v 40) j

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.archive_play_l {ω c o C γ Z A D H X R f : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D H) (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val,by omega⟩ H x)
    (root : Rd_entry_d o c (U 1)) (mx : Smem_d I c X R)
    (played : ∀ k r, Rd_entry_d k r H → ∃ n s, M.SuccessorOf n k ∧ Tg_run_real_d I A n r s ∧ M.IsRestrictionOf I s f n) :
    Tg_archive_play_d ω (U 5) (U 2) o X Z f := by
  have hw := tree.tree.omega
  intro m i Y R' μ K η C' L V q v row code
  obtain ⟨r,⟨p,pair,hp⟩,cell⟩ := row
  obtain ⟨w,k,t,kt,pack,hp⟩ := (columns 5 p).mp hp
  have run := (h.read_l hZF kt pack).1
  have localRow : Tg_past_at_d (w 13) m i Y R' μ K η C' L V q := ⟨r,⟨p,pair,hp⟩,cell⟩
  obtain ⟨v',code',low,_⟩ := run.play m i Y R' μ K η C' L V q localRow
  have ev : v' 40 = v 40 := congrFun (code'.inj_l I hZF.1 code) 42
  obtain ⟨⟨j,leg,_,anchor⟩,_⟩ := run.roots m i Y R' μ K η C' L V q localRow
  have global : It_map_d (U 2) o i j := by
    obtain ⟨a,ap,b,bp,hb⟩ := leg
    exact ⟨a,ap,b,bp,(columns 2 b).mpr ⟨w,k,t,kt,pack,hb⟩⟩
  obtain ⟨d,⟨z,zp,hz⟩,my⟩ := run.links m i Y R' μ K η C' L V q localRow
  have node : Rd_entry_d i d (U 1) := ⟨z,zp,(columns 1 z).mpr ⟨w,k,t,kt,pack,hz⟩⟩
  have source := (run.past.read_l hZF localRow).1.source
  have fixed := (anchor.read_l (ZF.modelsKP hZF) source.transitive my).2.2.2 (v 40) (ev ▸ low)
  have map := tree.tree.diagram.elementary o i j c X R d Y R' global root node mx.1 my.1
  refine ⟨map.1.1.input_mem_of_pairMember fixed,ev ▸ low,?_,j,global,fixed⟩
  obtain ⟨hn,_,node⟩ := (run.past.read_l hZF localRow).2.1.node_l hZF hw my source.transitive code
  intro a ha
  obtain ⟨l,x,px⟩ := node.1.1.1 a ha
  have lx : Rd_entry_d l x (v 40) := ⟨a,px,ha⟩
  have hl := hw.transitive (ZF.modelsKP hZF) _ hn l ((node.1.2 l).mpr ⟨x,lx⟩)
  obtain ⟨b,_,lb⟩ := h.function.2.1 l hl
  obtain ⟨n,nl,w',pack',run',num⟩ := h.rows l b lb
  obtain ⟨z,d,u,zd,cp,keep,keep'⟩ := h.merge_l hZF hw kt lb pack pack'
  have later := (h.read_l hZF zd cp).1
  have row' : Tg_past_at_d (u 13) m i Y R' μ K η C' L V q :=
    ⟨r,⟨p,pair,keep.2.2.1 5 p hp⟩,cell⟩
  obtain ⟨v',cv,_,trace⟩ := later.play m i Y R' μ K η C' L V q row'
  have ev : v' 40 = v 40 := congrFun (cv.inj_l I hZF.1 code) 42
  have trace := ev ▸ trace
  obtain ⟨b',p',pp,hp'⟩ := (run'.past.sequence.2.2 l).mp (num.symm ▸ nl.predecessor_mem)
  have lu : M.mem l (u 37) := (later.past.sequence.2.2 l).mpr ⟨b',p',pp,keep'.2.2.1 5 p' hp'⟩
  obtain ⟨n',s,ns,real,cut⟩ := played z d zd
  obtain ⟨n'',ns',u',cp',_,num'⟩ := h.rows z d zd
  have un : u 37 = n' := (congrFun (rt_tuple_inj_l cp cp') 37).trans (num'.trans (ns'.eq hZF.1 ns))
  obtain ⟨y,_,ly⟩ := (real.function_l I).2.1 l (un ▸ lu)
  have real := real.read_l I cp
  let nc : Nonempty {x // M.mem x (u 5)} := ⟨⟨ω,(later.context.omega_l later.source.source.code)⟩⟩
  obtain ⟨nd,σ,eq,valid⟩ := later.read_l hZF
  let ρ := later.model.slice_env_d I ⟨u 5, later.context.member⟩ nd nc σ
  have valid : Formula.satisfies ρ tg_issued0_m :=
    (later.model.slice_formula_l I ⟨u 5, later.context.member⟩
      (later.source.source.transitive (u 5) later.context.member) nd nc tg_issued0_m σ).mp valid
  have fs := (later.context.read_l hZF later.source.source).1
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have xy := Tg_play_d.entry_eq_l I hZF.1 later.model later.source.source.transitive later.context.member fs.transitive nc J ρ valid
    ((eq 4).symm ▸ (eq 3).symm ▸ (eq 20).symm ▸ trace)
    ((eq 4).symm ▸ (eq 3).symm ▸ (eq 20).symm ▸ real.2) lx ly
  obtain ⟨a',pa,haf⟩ := ((cut.2 l y).mp ly).2
  exact kpair_unique_l M hZF.1 pa (xy ▸ px) ▸ haf

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 极限中的共同树及其实际初等像

图证书同时记录树像和原局前缀。5.15 的实例从壳参数回拉原树，
用根箭头的交换律识别共同树，再由返回因子把它送回原树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_return_tree_d (ω c X N H π P S S' σ f : M.Domain) : Prop :=
  ∃ d W, Smem_d I d N W ∧ Smap_d I ω d c N X σ ∧ M.mem S' N ∧ Rd_entry_d S' S σ ∧
    (∀ m i n T s t g, Tg_return_node_d ω H π P m i n T s t g → T = S') ∧
    ∀ m i n T s t g, Tg_return_node_d ω H π P m i n T s t g → ∃ s₀, Rd_entry_d s s₀ σ ∧ M.MemberSubset s₀ f

theorem Tg_return_model_d.tree_l {ω o c X Z T Q G b H π N P S f : M.Domain}
    (limit : Tg_return_model_d hZF ω o c X T Q G b π N P)
    (hw : M.IsOmega ω) (ho : ∀ x, ¬ M.mem x o) (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G)
    (root : Rd_entry_d o c Q) (memS : M.mem S X) (preimage : ∃ a, Rd_entry_d a S π)
    (names : Tg_root_tree_d ω H G o S) (plays : Tg_archive_play_d ω H G o X Z f) :
    ∃ S' σ, Tg_return_tree_d hZF ω c X N H π P S S' σ f := by
  obtain ⟨B, Rₐ, a, U, Rᵤ, u, Q₀, G₀, c₀, X₀, R₀, π₀, d, W, σ,
    bt, ut, hwB, mb, mu, hj, hQ, hG, mx₀, hcc, hXX, restrict,
    small, mn, cone, hs, ⟨r, hr, factor⟩⟩ := limit
  obtain ⟨S₀, iS⟩ := preimage
  have hS₀ := (hj.member_l I hZF hw mb mu iS hXX).mpr memS
  have nat := hj.natural_l hZF hw bt ut mb mu hwB
  have root₀ := (hj.entry_l hZF hw bt ut mb mu
    (nat o (num_mem_l hZF.1 hw (show Num_d 0 o from ho))) hcc hQ).mpr root
  have leg := cone.elementary o r c₀ X₀ R₀ hr root₀ mx₀.1
  obtain ⟨S', hS', image⟩ := leg.1.1.2.2 S₀ hS₀
  have rootImage := (restrict.2 S₀ S).mpr ⟨hS₀, iS⟩
  obtain ⟨S'', value, iS''⟩ := (factor.2 S₀ S).mp rootImage
  have eq := leg.1.1.1.2 S₀ S'' S' value image
  subst S''
  refine ⟨S', σ, d, W, mn, hs, hS', iS'', ?_, ?_⟩
  · intro m i n T' s t g trace
    obtain ⟨Y, R, μ, K, η, C, L, V, q, v, row, code, _, a', _, _, _, j, ia, _, _, _, hjP, iv, _⟩ := trace
    obtain ⟨f, hf, treeImage⟩ := names m i Y R μ K η C L V q (v 19) (v 22) (v 40) (v 41) (v 42) row ⟨v, code, rfl, rfl, rfl, rfl, rfl⟩
    exact (it_cone_pull_entry_l hZF hw bt ut mb mu hj hwB hG small diagram cone
      hf iS ia treeImage hr hjP image iv).symm
  · intro m i n T' s t g trace
    obtain ⟨Y,R,μ,K,η,C,L,V,q,v,row,code,_,_,a',_,_,j,_,ia,_,_,hjP,_,iv,_⟩ := trace
    obtain ⟨mem,_,sub,f,hf,fixed⟩ := plays m i Y R μ K η C L V q v row code
    have own := (hj.member_l I hZF hw mb mu ia hXX).mpr mem
    obtain ⟨s₀,_,value⟩ := leg.1.1.2.2 a' own
    have eq := it_cone_pull_entry_l hZF hw bt ut mb mu hj hwB hG small diagram cone
      hf ia ia fixed hr hjP value iv
    obtain ⟨z,hz,iz⟩ := (factor.2 a' (v 40)).mp ((restrict.2 a' (v 40)).mpr ⟨own,ia⟩)
    have zs := leg.1.1.1.2 a' z s₀ hz value
    exact ⟨v 40,eq ▸ zs ▸ iz,sub⟩

end YesMetaZFC.SetTheory.LargeCardinal
