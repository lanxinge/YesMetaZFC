import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunMove
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOddRecords

/-! # 并历史中每份实数存档仍是同一原对局的前缀

比较某一坐标时，将存档与该坐标所属的轮次放到共同较晚阶段。
事件单值性给出字母相等；旧根图对固定锚点的恒等性给出返回所需的根像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_archive_play_d (ω H G o X Z f : M.Domain) : Prop := ∀ m i Y R μ K η C L V q,
  ∀ v : Fin 54 → M.Domain, Tg_past_at_d H m i Y R μ K η C L V q → Tg_saved_code_d ω V q v →
    M.mem (v 40) X ∧ M.mem (v 40) Z ∧ M.MemberSubset (v 40) f ∧
      ∃ j, It_map_d G o i j ∧ Rd_entry_d (v 40) (v 40) j

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.archive_play_l {ω c o C γ Z A D H X R f : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D H) (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val,by omega⟩ H x)
    (root : Rd_entry_d o c (U 1)) (mx : Smem_d I c X R)
    (played : ∀ k r, Rd_entry_d k r H → ∃ n s, M.SuccessorOf n k ∧ Tg_run_real_d A n r s ∧ M.IsRestrictionOf I s f n) :
    Tg_archive_play_d ω (U 5) (U 2) o X Z f := by
  have hw := tree.tree.omega
  intro m i Y R' μ K η C' L V q v row code
  obtain ⟨r,⟨p,pair,hp⟩,cell⟩ := row
  obtain ⟨w,k,t,kt,pack,hp⟩ := (columns 5 p).mp hp
  have run := (h.read_l hZF kt pack).1
  have localRow : Tg_past_at_d (w 13) m i Y R' μ K η C' L V q := ⟨r,⟨p,pair,hp⟩,cell⟩
  obtain ⟨v',code',low,_⟩ := run.play m i Y R' μ K η C' L V q localRow
  have ev : v' 40 = v 40 := congrFun (rt_tuple_inj_l code' code) 42
  obtain ⟨⟨j,leg,_,anchor⟩,_⟩ := run.roots m i Y R' μ K η C' L V q localRow
  have fixed := anchor.fixed (v 40) (ev ▸ low)
  have global : It_map_d (U 2) o i j := by
    obtain ⟨a,ap,b,bp,hb⟩ := leg
    exact ⟨a,ap,b,bp,(columns 2 b).mpr ⟨w,k,t,kt,pack,hb⟩⟩
  obtain ⟨d,⟨z,zp,hz⟩,my⟩ := run.links m i Y R' μ K η C' L V q localRow
  have node : Rd_entry_d i d (U 1) := ⟨z,zp,(columns 1 z).mpr ⟨w,k,t,kt,pack,hz⟩⟩
  have map := tree.tree.diagram.elementary o i j c X R d Y R' global root node mx.1 my.1
  refine ⟨map.1.1.input_mem_of_pairMember fixed,ev ▸ low,?_,j,global,fixed⟩
  obtain ⟨hn,_,node⟩ := (run.past.read_l hZF localRow).1.node_l hZF code
  intro a ha
  obtain ⟨l,x,px⟩ := node.1.1.1 a ha
  have lx : Rd_entry_d l x (v 40) := ⟨a,px,ha⟩
  have hl := hw.transitive hZF _ hn l ((node.1.2 l).mpr ⟨x,lx⟩)
  obtain ⟨b,_,lb⟩ := h.function.2.1 l hl
  obtain ⟨n,nl,w',pack',run',num⟩ := h.rows l b lb
  obtain ⟨z,d,u,zd,cp,keep,keep'⟩ := h.merge_l hZF hw kt lb pack pack'
  have later := (h.read_l hZF zd cp).1
  have row' : Tg_past_at_d (u 13) m i Y R' μ K η C' L V q :=
    ⟨r,⟨p,pair,keep.2.2.1 5 p hp⟩,cell⟩
  obtain ⟨v',cv,_,trace⟩ := later.play m i Y R' μ K η C' L V q row'
  have ev : v' 40 = v 40 := congrFun (rt_tuple_inj_l cv code) 42
  have trace := ev ▸ trace
  obtain ⟨b',p',pp,hp'⟩ := (run'.past.sequence.2.2 l).mp (num.symm ▸ nl.predecessor_mem)
  have lu : M.mem l (u 37) := (later.past.sequence.2.2 l).mpr ⟨b',p',pp,keep'.2.2.1 5 p' hp'⟩
  obtain ⟨n',s,ns,real,cut⟩ := played z d zd
  obtain ⟨n'',ns',u',cp',_,num'⟩ := h.rows z d zd
  have un : u 37 = n' := (congrFun (rt_tuple_inj_l cp cp') 37).trans (num'.trans (ns'.eq hZF.1 ns))
  obtain ⟨y,_,ly⟩ := real.function_l.2.1 l (un ▸ lu)
  have real := real.read_l cp
  let nc : Nonempty {x // M.mem x (u 5)} := ⟨⟨ω,later.context.omega⟩⟩
  obtain ⟨ρ,eq,valid⟩ := later.read_l hZF nc
  have fs := (later.context.read_l hZF later.source.source).1
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have xy := Tg_play_d.entry_eq_l hZF fs.transitive nc J ρ valid
    ((eq 4).symm ▸ (eq 3).symm ▸ (eq 20).symm ▸ trace)
    ((eq 4).symm ▸ (eq 3).symm ▸ (eq 20).symm ▸ real.2) lx ly
  obtain ⟨a',pa,haf⟩ := ((cut.2 l y).mp ly).2
  exact kpair_unique_l M hZF.1 pa (xy ▸ px) ▸ haf

end YesMetaZFC.SetTheory.LargeCardinal
