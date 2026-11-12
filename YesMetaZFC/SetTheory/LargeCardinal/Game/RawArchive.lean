import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Game.TraceImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNameSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.RootSquare
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawSavedBase
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope

/-! # 原游戏的十一项档案及选定共同图列

每行只保存原树节点、原模型、回答和原根图。当前列把实际选定的共同图、
该图的端点界和同图事件视图放在一起；推进时直接复合这份见证，
不比较任意两次选择，也不要求原模型嵌入工作秩段。
根切片成员的两条根图经该选定共同图交换；事件视图不带背景 γ 或 Bγ。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_raw_archive_row_d (α : Type u) where
  i : α
  c : α
  X : α
  R : α
  w : α
  η : α
  C : α
  L : α
  U : α
  q : α
  p : α

def Tg_raw_archive_row_d.values_d {α : Type u} (s : Tg_raw_archive_row_d α) : Fin 11 → α :=
  fun i => [s.i,s.c,s.X,s.R,s.w,s.η,s.C,s.L,s.U,s.q,s.p].get i

theorem Tg_raw_archive_row_d.eq_l {a b : Tg_raw_archive_row_d M.Domain} (h : a.values_d = b.values_d) : a = b := by
  cases a; cases b
  congr 1 <;> first
    | exact congrFun h 0 | exact congrFun h 1 | exact congrFun h 2
    | exact congrFun h 3 | exact congrFun h 4 | exact congrFun h 5
    | exact congrFun h 6 | exact congrFun h 7 | exact congrFun h 8
    | exact congrFun h 9 | exact congrFun h 10

/-- 十一项原行实际打包，不加入工作模型或闲置坐标。 -/
theorem Tg_raw_archive_row_d.tuple_l (hKP : M.Models KP) (s : Tg_raw_archive_row_d M.Domain) :
    ∃ r, Rt_tuple_d s.values_d r := rt_tuple_exists_l hKP s.values_d

structure Tg_raw_archive_frame_d (α : Type u) where
  o : α
  n : α
  Q : α
  G : α
  L : α

def Tg_raw_archive_row_d.link_d (f : Tg_raw_archive_frame_d M.Domain) (s : Tg_raw_archive_row_d M.Domain) : Prop :=
  M.mem s.i f.n ∧ Rd_entry_d s.i s.c f.Q ∧ It_map_d f.G f.o s.i s.p ∧ Rd_entry_d s.i s.L f.L

variable (I : kpair_convention_l.Interpretation M)

def Tg_raw_archive_links_d (f : Tg_raw_archive_frame_d M.Domain) (D : M.Domain) : Prop :=
  ∀ m r, ∀ s : Tg_raw_archive_row_d M.Domain, M.PairMember I m r D → Rt_tuple_d s.values_d r → s.link_d f

/-- 保存短图与三个事件坐标使用同一个原共同图；低层根约束不混入事件核心。 -/
def Tg_raw_saved_view_d (X R w U q g N S w' C c e a b z m h : M.Domain) : Prop :=
  ∃ v : Fin 54 → M.Domain, Tg_saved_code_d X R w U q v ∧
    ∃ n t κ u, M.PairMember I m n z ∧ M.PairMember I (v 41) t g ∧
      M.PairMember I (v 15) κ g ∧ M.PairMember I (v 11) u g ∧
      Tg_trace_d I N S w' C c e a n h t κ u ∧
      ∃ s, M.PairMember I (v 40) s g ∧ Tg_play_d I N S C c b h s

def Tg_raw_archive_entry_d (Ω S₀ X₀ R₀ γ₀ D₀ C₀ p N S χ w C c e a b z h m r : M.Domain) : Prop :=
  ∃ s : Tg_raw_archive_row_d M.Domain, Rt_tuple_d s.values_d r ∧
    Smdl_d I s.c s.X s.R ∧ Tg_saved_d I s.w s.X s.R s.η s.C s.L s.U s.q ∧
    (∃ z₀, Rr_layer_d I Ω s.X s.R s.w z₀) ∧
    Tg_saved_name_d I S₀ s.X s.R s.w s.U s.q s.p ∧
    Tg_raw_saved_base_d I X₀ R₀ γ₀ D₀ C₀ s.X s.R s.w s.C s.U s.q s.p ∧
    Tg_raw_cofinal_d I s.w s.X s.R s.L ∧
    ∃ l V Γ g, Ic_common_d I s.X s.R N S s.L l s.U V Γ g ∧
      (Rd_entry_d l χ S ∨ l = χ) ∧ Tg_root_square_d D₀ s.p p g ∧
      Tg_raw_saved_view_d I s.X s.R s.w s.U s.q g N S w C c e a b z m h

def Tg_raw_archive_views_d (Ω S₀ X₀ R₀ γ₀ D₀ C₀ p D N S χ w C c e a b z h : M.Domain) : Prop :=
  ∀ m r, M.PairMember I m r D → Tg_raw_archive_entry_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ p N S χ w C c e a b z h m r

/-- 空原档案是根初态的真实列实例。 -/
theorem Tg_raw_archive_views_d.empty_l {Ω S₀ X₀ R₀ γ₀ D₀ C₀ p D N S χ w C c e a b z h : M.Domain}
    (empty : ∀ x, ¬ M.mem x D) : Tg_raw_archive_views_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ p D N S χ w C c e a b z h := by
  rintro m r ⟨p,_,hp⟩
  exact (empty p hp).elim

theorem Tg_raw_archive_links_d.empty_l {f : Tg_raw_archive_frame_d M.Domain} {D : M.Domain}
    (empty : ∀ x, ¬ M.mem x D) : Tg_raw_archive_links_d I f D := by
  rintro m r s ⟨p,_,hp⟩ _
  exact (empty p hp).elim

/-- 按实际十一项行码读取已选共同图，根方块与事件视图不重新选择。 -/
theorem Tg_raw_archive_entry_d.read_l {Ω S₀ X₀ R₀ γ₀ D₀ C₀ p N S χ w C c e a b z h m r : M.Domain}
    (entry : Tg_raw_archive_entry_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ p N S χ w C c e a b z h m r)
    {row : Tg_raw_archive_row_d M.Domain} (tuple : Rt_tuple_d row.values_d r) :
    Smdl_d I row.c row.X row.R ∧ Tg_saved_d I row.w row.X row.R row.η row.C row.L row.U row.q ∧
    (∃ z₀, Rr_layer_d I Ω row.X row.R row.w z₀) ∧
    Tg_saved_name_d I S₀ row.X row.R row.w row.U row.q row.p ∧
    Tg_raw_saved_base_d I X₀ R₀ γ₀ D₀ C₀ row.X row.R row.w row.C row.U row.q row.p ∧
    Tg_raw_cofinal_d I row.w row.X row.R row.L ∧
    ∃ l V Γ g, Ic_common_d I row.X row.R N S row.L l row.U V Γ g ∧
      (Rd_entry_d l χ S ∨ l = χ) ∧ Tg_root_square_d D₀ row.p p g ∧
      Tg_raw_saved_view_d I row.X row.R row.w row.U row.q g N S w C c e a b z m h := by
  obtain ⟨s,code,rest⟩ := entry
  have eq := Tg_raw_archive_row_d.eq_l (rt_tuple_inj_l code tuple)
  exact eq ▸ rest

/-- 已完成的同图视图随实际档案函数追加，旧条目原样保持。 -/
theorem Tg_raw_archive_views_d.push_l {Ω S₀ X₀ R₀ γ₀ D₀ C₀ p D D' N S χ w C c e a b z h m r : M.Domain}
    (old : Tg_raw_archive_views_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ p D N S χ w C c e a b z h)
    (entry : Tg_raw_archive_entry_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ p N S χ w C c e a b z h m r)
    (entries : ∀ l s, M.PairMember I l s D' ↔ M.PairMember I l s D ∨ l = m ∧ s = r) :
    Tg_raw_archive_views_d I Ω S₀ X₀ R₀ γ₀ D₀ C₀ p D' N S χ w C c e a b z h := by
  intro l s hs
  rcases (entries l s).mp hs with hs | ⟨rfl,rfl⟩
  · exact old l s hs
  · exact entry

theorem Tg_raw_archive_links_d.push_l {f : Tg_raw_archive_frame_d M.Domain} {D D' m r : M.Domain}
    {s : Tg_raw_archive_row_d M.Domain} (old : Tg_raw_archive_links_d I f D)
    (code : Rt_tuple_d s.values_d r) (link : s.link_d f)
    (entries : ∀ l t, M.PairMember I l t D' ↔ M.PairMember I l t D ∨ l = m ∧ t = r) :
    Tg_raw_archive_links_d I f D' := by
  intro l t a ht ca
  rcases (entries l t).mp ht with ht | ⟨rfl,rfl⟩
  · exact old l t a ht ca
  · exact (Tg_raw_archive_row_d.eq_l (rt_tuple_inj_l ca code)).symm ▸ link

/-- 原树框架延伸只需原模型、原根边和支撑列的保持。 -/
theorem Tg_raw_archive_links_d.extend_l {f f' : Tg_raw_archive_frame_d M.Domain} {D : M.Domain}
    (old : Tg_raw_archive_links_d I f D) (grow : M.MemberSubset f.n f'.n)
    (models : ∀ i c, Rd_entry_d i c f.Q → Rd_entry_d i c f'.Q)
    (maps : ∀ i p, M.mem i f.n → It_map_d f.G f.o i p → It_map_d f'.G f'.o i p)
    (levels : ∀ i L, Rd_entry_d i L f.L → Rd_entry_d i L f'.L) : Tg_raw_archive_links_d I f' D := by
  intro m r s hr code
  obtain ⟨hi,node,root,level⟩ := old m r s hr code
  exact ⟨grow s.i hi,models _ _ node,maps _ _ hi root,levels _ _ level⟩

/-- 读取已选同一张图时，只用该图的函数性识别原事件坐标。 -/
theorem Tg_raw_saved_view_d.read_l (hE : Extensional M)
    {X R w U q g N S w' C c e a b z m h n t κ u : M.Domain}
    (view : Tg_raw_saved_view_d I X R w U q g N S w' C c e a b z m h)
    {v : Fin 54 → M.Domain} (code : Tg_saved_code_d X R w U q v)
    (fn : M.IsSetFunction I g) (numbers : M.IsSetFunction I z) (index : M.PairMember I m n z)
    (it : M.PairMember I (v 41) t g) (iκ : M.PairMember I (v 15) κ g) (iu : M.PairMember I (v 11) u g) :
    Tg_trace_d I N S w' C c e a n h t κ u ∧
      ∃ s, M.PairMember I (v 40) s g ∧ Tg_play_d I N S C c b h s := by
  obtain ⟨p,cp,n₀,t₀,κ₀,u₀,index₀,it₀,iκ₀,iu₀,trace,s,is,play⟩ := view
  have eq := cp.inj_l I hE code
  have pt : p 41 = v 41 := congrFun eq 43
  have pκ : p 15 = v 15 := congrFun eq 17
  have pu : p 11 = v 11 := congrFun eq 13
  have ps : p 40 = v 40 := congrFun eq 42
  have et := fn.2 (v 41) t₀ t (pt ▸ it₀) it
  have eκ := fn.2 (v 15) κ₀ κ (pκ ▸ iκ₀) iκ
  have eu := fn.2 (v 11) u₀ u (pu ▸ iu₀) iu
  exact ⟨numbers.2 m n₀ n index₀ index ▸ et ▸ eκ ▸ eu ▸ trace,
    s,ps ▸ is,play⟩

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

/-- 原边搬运事件，复合图读取保存坐标，二者使用同一实际像。 -/
private theorem tg_raw_view_image_l
    {X R w U q g N S wn C c e a b z m h Y T wy C' c' e' a' b' z' h' j g' H : M.Domain}
    (view : Tg_raw_saved_view_d J X R w U q g N S wn C c e a b z m h)
    (move : Tg_trace_image_d J N S wn C c e a b h Y T wy C' c' e' a' b' h' j z z')
    (square : ∀ x y E, Rd_entry_d x y g → (Rd_entry_d x E g' ↔ Rd_entry_d y E j))
    (member : Rd_entry_d H C' T) (keep : ∀ x, M.mem x Y → Rd_entry_d x h' T → Rd_entry_d x H T) :
    Tg_raw_saved_view_d J X R w U q g' Y T wy C' c' e' a' b' z' m H := by
  obtain ⟨v,code,n,t,κ,u,index,it,iκ,iu,trace,s,is,play⟩ := view
  obtain ⟨n',t',κ',u',in',it',iκ',iu',index',carry⟩ := move.1 n t κ u trace
  obtain ⟨s',is',carry_play⟩ := move.2 s play
  exact ⟨v,code,n',t',κ',u',index' m index,(square (v 41) t t' it).mpr it',
    (square (v 15) κ κ' iκ).mpr iκ',(square (v 11) u u' iu).mpr iu',carry H member keep,
    s',(square (v 40) s s' is).mpr is',carry_play H member keep⟩

/-- 一次活动把整份已选档案列推进到新原端点；新界就是本次目标端点。 -/
theorem Tg_raw_archive_views_d.step_l
    {Ω S₀ X₀ R₀ γ₀ Dₛ C₀ p p' D N R P S μ ν U V Γ t c d j χ w C c₀ e₀ a₀ b₀ z h
      w' C' c' e' a' b' z' h' H : M.Domain}
    (old : Tg_raw_archive_views_d J Ω S₀ X₀ R₀ γ₀ Dₛ C₀ p D N R χ w C c₀ e₀ a₀ b₀ z h)
    (step : Ic_common_d J N R P S μ ν U V Γ t)
    (mn : Smdl_d J c N R) (mp : Smdl_d J d P S)
    (hN : (smdl_structure_l J (R := R) mn.2.1).Models KP)
    (ext : Extensional (smdl_structure_l J (R := S) mp.2.1))
    (κ K : (smdl_structure_l J (R := R) mn.2.1).Domain)
    (rank : V_d (kp_pair_l hN) κ K) (below : Rd_entry_d κ.val μ R) (bound : Rd_entry_d χ κ.val R)
    (square : ∀ x : (smdl_structure_l J (R := R) mn.2.1).Domain,
      (smdl_structure_l J (R := R) mn.2.1).mem x K → ∀ E, Rd_entry_d x.val E t ↔ Rd_entry_d x.val E j)
    (root : It_comp_d p j p')
    (move : Tg_trace_image_d J N R w C c₀ e₀ a₀ b₀ h P S w' C' c' e' a' b' h' j z z')
    (member : Rd_entry_d H C' S) (keep : ∀ x, M.mem x P → Rd_entry_d x h' S → Rd_entry_d x H S) :
    Tg_raw_archive_views_d J Ω S₀ X₀ R₀ γ₀ Dₛ C₀ p' D P S ν w' C' c' e' a' b' z' H := by
  intro m r entry
  have stored := old m r entry
  obtain ⟨row,code,_⟩ := stored
  obtain ⟨model,saved,numbers,name,base,cofinal,l,W,Δ,g,common,upper,roots,view⟩ :=
    Tg_raw_archive_entry_d.read_l J (old m r entry) code
  have low : Rd_entry_d l κ.val R := upper.elim
    (fun h => (v_ordinal_l (kp_pair_l hN) rank).transitive
      ⟨χ,(mn.2.2.2 χ κ.val bound).1⟩ bound ⟨l,common.right_rank.1⟩ h)
    (fun eq => eq.symm ▸ bound)
  obtain ⟨l',W',g',next,below',graph⟩ := step.native_archive_step_l hZF mn mp hN ext κ K rank below square
    row.X row.R row.L l row.U W Δ g common low
  exact ⟨row,code,model,saved,numbers,name,base,cofinal,l',W',Δ,g',next,Or.inl below',
    roots.comp_l (common.graph_comp_l hZF next graph) root,
    tg_raw_view_image_l hZF view move graph member keep⟩

/-- 两次原工厂的共同图及同一偶数边，同时推进全部旧档案事件与统一端点界。 -/
theorem Tg_raw_archive_views_d.advance_l
    {Ω S₀ X₀ R₀ γ₀ Dₛ C₀ p p' D N R P S Y T μ ν U V Γ t L l W Z Δ s c d e j k κ χ
      w C c₀ e₀ a₀ b₀ z h w' C' c' e' a' b' z' h' H : M.Domain}
    (old : Tg_raw_archive_views_d J Ω S₀ X₀ R₀ γ₀ Dₛ C₀ p D N R χ w C c₀ e₀ a₀ b₀ z h)
    (first : Ic_common_d J N R P S μ ν U V Γ t) (second : Ic_common_d J P S Y T L l W Z Δ s)
    (mn : Smdl_d J c N R) (mp : Smdl_d J d P S) (my : Smdl_d J e Y T)
    (hN : (smdl_structure_l J (R := R) mn.2.1).Models KP)
    (hP : (smdl_structure_l J (R := S) mp.2.1).Models KP)
    (ext : Extensional (smdl_structure_l J (R := T) my.2.1))
    (κ₀ K : (smdl_structure_l J (R := S) mp.2.1).Domain)
    (rank : V_d (kp_pair_l hP) κ₀ K) (point : Rd_entry_d κ κ₀.val t)
    (below : Rd_entry_d κ μ R) (above : Rd_entry_d κ₀.val L S) (bound : Rd_entry_d χ κ R)
    (inverse : ∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x t)
    (square : ∀ x : (smdl_structure_l J (R := S) mp.2.1).Domain, ∀ y E,
      (smdl_structure_l J (R := S) mp.2.1).mem x K → Rd_entry_d x.val y k →
        (Rd_entry_d x.val E s ↔ Rd_entry_d y E j))
    (root : It_comp_d p j p')
    (move : Tg_trace_image_d J N R w C c₀ e₀ a₀ b₀ h Y T w' C' c' e' a' b' h' j z z')
    (member : Rd_entry_d H C' T) (keep : ∀ x, M.mem x Y → Rd_entry_d x h' T → Rd_entry_d x H T) :
    Tg_raw_archive_views_d J Ω S₀ X₀ R₀ γ₀ Dₛ C₀ p' D Y T l w' C' c' e' a' b' z' H := by
  let N₀ := smdl_structure_l J (R := R) mn.2.1
  have limit : N₀.IsLimitOrdinal ⟨μ,first.left_rank.1⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l J mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨μ,first.left_rank.1⟩)).mp first.limit)
  have ordinal := limit.1.mem (show N₀.mem ⟨κ,(mn.2.2.2 κ μ below).1⟩ ⟨μ,first.left_rank.1⟩ from below)
  intro m r entry
  have stored := old m r entry
  obtain ⟨row,code,_⟩ := stored
  obtain ⟨model,saved,numbers,name,base,cofinal,l₀,B,D₀,g,common,upper,roots,view⟩ :=
    Tg_raw_archive_entry_d.read_l J (old m r entry) code
  have low : Rd_entry_d l₀ κ R := upper.elim
    (fun h => ordinal.transitive ⟨χ,(mn.2.2.2 χ κ bound).1⟩ bound ⟨l₀,common.right_rank.1⟩ h)
    (fun eq => eq.symm ▸ bound)
  obtain ⟨l',B',g',next,below',graph⟩ := first.native_archive_image_l hZF second mn mp my hN hP ext
    κ₀ K rank point below above inverse square row.X row.R row.L l₀ row.U B D₀ g common low
  exact ⟨row,code,model,saved,numbers,name,base,cofinal,l',B',D₀,g',next,Or.inl below',
    roots.comp_l (common.graph_comp_l hZF next graph) root,
    tg_raw_view_image_l hZF view move graph member keep⟩

end YesMetaZFC.SetTheory.LargeCardinal
