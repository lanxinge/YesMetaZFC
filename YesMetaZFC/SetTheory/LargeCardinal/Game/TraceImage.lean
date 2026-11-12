import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedView
import YesMetaZFC.SetTheory.LargeCardinal.Game.Archive
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRoundSyntax

/-! # 原树边上的全部旧事件及后续历史

保存时的轮号、标签、回答域、类型及短前缀保留原值；当前事件使用同一原边的实际像。
各像由原记录的所属判断和原边的全域性构造，并在每个包含搬运历史的目标历史中保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u

def Tg_trace_image_d {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    (X R w C c e a b h Y S w' C' c' e' a' b' h' j z z' : M.Domain) : Prop :=
  (∀ n t κ u, Tg_trace_d I X R w C c e a n h t κ u →
    ∃ n' t' κ' u', M.PairMember I n n' j ∧ M.PairMember I t t' j ∧
      M.PairMember I κ κ' j ∧ M.PairMember I u u' j ∧
      (∀ m, M.PairMember I m n z → M.PairMember I m n' z') ∧
      ∀ H, M.PairMember I H C' S →
        (∀ x, M.mem x Y → M.PairMember I x h' S → M.PairMember I x H S) →
        Tg_trace_d I Y S w' C' c' e' a' n' H t' κ' u') ∧
  ∀ s, Tg_play_d I X R C c b h s →
    ∃ s', M.PairMember I s s' j ∧
      ∀ H, M.PairMember I H C' S →
        (∀ x, M.mem x Y → M.PairMember I x h' S → M.PairMember I x H S) →
        Tg_play_d I Y S C' c' b' H s'

/-- 一份旧档案的新共同图同时解释三个事件坐标与保存短前缀。 -/
def Tg_archive_trace_d {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    (X R B σ w C c e a b h Y S D τ w' C' c' e' a' b' h' j κ z z' : M.Domain) : Prop :=
  ∀ Z T A π L l φ U V Γ g,
    Ic_agree_d I Z T A π X R B σ L l φ U V Γ g → Rd_entry_d l κ R →
    ∃ l' V' g', Ic_agree_d I Z T A π Y S D τ L l' φ U V' Γ g' ∧
      (∀ x y E, Rd_entry_d x y g → (Rd_entry_d x E g' ↔ Rd_entry_d y E j)) ∧
      ∀ w₀ q₀ γ m, Tg_saved_view_d I Z T w₀ U q₀ γ g X R w C c e a b z m h →
        ∀ H, Rd_entry_d H C' S →
          (∀ x, M.mem x Y → Rd_entry_d x h' S → Rd_entry_d x H S) →
          Tg_saved_view_d I Z T w₀ U q₀ γ g' Y S w' C' c' e' a' b' z' m H

variable {M : Structure.{u}}

/-- 原边事件搬运与共同图更新共用实际坐标像；新历史无需重新选择档案视图。 -/
theorem Tg_trace_image_d.archive_l (hKP : M.Models KP)
    {X R B σ w C c e a b h Y S D τ w' C' c' e' a' b' h' j κ z z' : M.Domain}
    (move : Tg_trace_image_d (kp_pair_l hKP) X R w C c e a b h Y S w' C' c' e' a' b' h' j z z')
    (copy : Ic_archive_image_d (kp_pair_l hKP) X R B σ Y S D τ j κ) :
    Tg_archive_trace_d (kp_pair_l hKP) X R B σ w C c e a b h Y S D τ w' C' c' e' a' b' h' j κ z z' := by
  intro Z T A π L l φ U V Γ g old low
  obtain ⟨l',V',g',next,square⟩ := copy Z T A π L l φ U V Γ g old low
  refine ⟨l',V',g',next,square,?_⟩
  intro w₀ q₀ γ m view H hH keepH
  obtain ⟨v,code,lower,n,t,k,u,index₀,it,ik,iu,trace,s,is,play⟩ := view
  obtain ⟨n',t',k',u',in',it',ik',iu',index,keep⟩ := move.1 n t k u trace
  obtain ⟨s',is',keep_play⟩ := move.2 s play
  exact ⟨v,code,lower,n',t',k',u',index m index₀,(square (v 41) t t' it).mpr it',
    (square (v 15) k k' ik).mpr ik',(square (v 11) u u' iu).mpr iu',keep H hH keepH,
    s',(square (v 40) s s' is).mpr is',keep_play H hH keepH⟩

/-- 整列的严格界由实际复制行及统一历史界给出，再逐行调用同一次原边搬运。 -/
theorem Tg_archive_trace_d.columns_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (Ω γ Bγ Cᵣ : M.Domain)
    {d X R B σ w C c e a b h Y S D τ w' C' c' e' a' b' h' j z z' u U β : M.Domain}
    (f : Tg_archive_frame_d M.Domain) (mx : Smdl_d I d X R)
    (hX : (smdl_structure_l I (R := R) mx.2.1).Models KP)
    (row : Ic_at_d f.H f.n X B σ u U β) (node : Rd_entry_d f.n d f.Q)
    (κ : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (move : Tg_archive_trace_d I X R B σ w C c e a b h
      Y S D τ w' C' c' e' a' b' h' j κ.val z z')
    (trans : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet κ) :
    ∀ H χ, Ic_bound_d I f.H f.Q X R σ f.n χ → Rd_entry_d χ κ.val R →
      Tg_archive_links_d I f H →
      Tg_archive_views_d I Ω γ Bγ Cᵣ H X R B σ w C c e a b z h →
      ∀ h₁, Rd_entry_d h₁ C' S →
        (∀ x, M.mem x Y → Rd_entry_d x h' S → Rd_entry_d x h₁ S) →
        Tg_archive_views_d I Ω γ Bγ Cᵣ H Y S D τ w' C' c' e' a' b' z' h₁ := by
  intro H χ bound below links views h₁ member keep m r hr
  let N := smdl_structure_l I (R := R) mx.2.1
  have entry x y : Rd_entry_d x y R ↔ M.PairMember I x y R := by
    let ρ : Env M 3 := ⟨fun i => [x,y,R].get i,fun _ => x⟩
    exact (rd_entry_sat_l hE ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      (Formula.satisfies_orderedPairMem_iff I ρ (.bound 0) (.bound 1) (.bound 2))
  obtain ⟨s,code,model,saved,numbers,roots,l,φ,V,Γ,g,same,view⟩ := views m r hr
  obtain ⟨hi,qi,_,_,z₀,Z₀,α₀,source⟩ := links m r s hr code
  let ln : N.Domain := ⟨l,same.common.right_rank.1⟩
  let vn : N.Domain := ⟨V,same.common.right_rank.2.1⟩
  have rank := (rr_rank_native_l I mx.2.1 hX ln vn).mp same.common.right_rank
  have ord : Rr_truth_d I X R (KP.ord0_m .newest) (fun _ : Fin 1 => l) :=
    (rr_truth_native_l I mx.2.1 (KP.ord0_m .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ln)).mpr ((KP.ord0_sat_l hX _ .newest).mpr (v_ordinal_l (kp_pair_l hX) rank))
  have height : Ic_height_d I f.H f.Q X R σ f.n s.i l :=
    ⟨ord,s.X,s.A,s.π,z₀,Z₀,α₀,B,u,U,β,s.c,d,s.R,s.L,φ,s.U,V,Γ,g,
      source,row,qi,node,model,mx,same⟩
  have low : Rd_entry_d l κ.val R := by
    rcases bound.upper s.i l hi height with lt | eq
    · exact (entry l κ.val).mpr
        (trans ⟨χ,bound.ordinal.1 0⟩ ((entry χ κ.val).mp below) ln ((entry l χ).mp lt))
    · exact eq.symm ▸ below
  obtain ⟨l',V',g',next,_,carry⟩ := move s.X s.R s.A s.π s.L l φ s.U V Γ g same low
  exact ⟨s,code,model,saved,numbers,roots,l',φ,V',Γ,g',next,
    carry s.w s.q γ m view h₁ member keep⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 每个旧事件的四个像自动产生；目标只需 KP，历史包含直接使用其原关系。 -/
theorem Tg_context_d.trace_image_l
    {Ω X R d₀ Y S d j w C w' η' C' c₀ e₀ a₀ b₀ h₀ z z' : M.Domain}
    (context : Tg_context_d I w' Y S η' C') (hΩ : M.IsOmega Ω)
    (mx : Smdl_d I d₀ X R) (my : Smdl_d I d Y S) (map : Smap_d I Ω d₀ d X Y j)
    (hY : (smdl_structure_l I (R := S) my.2.1).Models KP)
    (ext : Rf_ext_d I X R)
    (numbers : Rr_layer_d I Ω X R w z) (numbers' : Rr_layer_d I Ω Y S w' z')
    (nc : Nonempty {x : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem x ⟨C',context.member⟩})
    (c e a b h : (rt_model_l (M := smdl_structure_l I (R := S) my.2.1) ⟨C',context.member⟩ nc).Domain)
    (iw : Rd_entry_d w w' j) (iC : Rd_entry_d C C' j)
    (ic : Rd_entry_d c₀ c.val.val j) (ie : Rd_entry_d e₀ e.val.val j)
    (ia : Rd_entry_d a₀ a.val.val j) (ib : Rd_entry_d b₀ b.val.val j) (ih : Rd_entry_d h₀ h.val.val j) :
    Tg_trace_image_d I X R w C c₀ e₀ a₀ b₀ h₀ Y S w' C' c.val.val e.val.val a.val.val b.val.val h.val.val j z z' := by
  let N := smdl_structure_l I (R := S) my.2.1
  let D : N.Domain := ⟨C',context.member⟩
  let ω : N.Domain := ⟨w',context.omega_mem⟩
  have fs := context.finite_l my.2.1 hY.1
  let J := rt_pair_l fs.transitive nc hY.1 fs.pair
  have ey : Rf_ext_d I Y S := fun x hx y hy same =>
    congrArg Subtype.val (hY.1.eq_of_same_members (⟨x,hx⟩ : N.Domain) ⟨y,hy⟩
      (fun v => same v.val v.property))
  have digits := (numbers.omega_map_l I hZF hΩ mx my map ext ey numbers').2
  refine ⟨?_,?_⟩
  · intro n t κ u trace
    have members := trace.elim fun m _ => m
    obtain ⟨n',hn,in₀⟩ := map.1.1.2.2 n (members 5)
    obtain ⟨t',ht,it⟩ := map.1.1.2.2 t (members 7)
    obtain ⟨κ',hκ,iκ⟩ := map.1.1.2.2 κ (members 8)
    obtain ⟨u',hu,iu⟩ := map.1.1.2.2 u (members 9)
    have moved := trace.map_l I hZF hΩ mx my map iw iC ic ie ia in₀ ih it iκ iu
    have index m (mn : Rd_entry_d m n z) : Rd_entry_d m n' z' := by
      obtain ⟨p,_,mp⟩ := numbers'.injection.1.2.2 m (numbers.injection.1.input_mem_of_pairMember mn)
      exact map.1.1.1.2 n p n' (digits m n p mn mp) in₀ ▸ mp
    refine ⟨n',t',κ',u',in₀,it,iκ,iu,index,fun H hH keep => ?_⟩
    let h' : (rt_model_l D nc).Domain := ⟨⟨H,(my.2.2.2 H C' hH).1⟩,hH⟩
    exact moved.native_mono_l I my.2.1 hY.1 ω D fs.transitive nc J c e a h h'
      ⟨n',hn⟩ ⟨t',ht⟩ ⟨κ',hκ⟩ ⟨u',hu⟩ (fun x hx => keep x.val x.property hx)
  · intro s play
    obtain ⟨s',_,is⟩ := map.1.1.2.2 s (play.elim fun m _ => m 4)
    have moved := play.map_l I hZF hΩ mx my map iC ic ib ih is
    refine ⟨s',is,fun H hH keep => ?_⟩
    let h' : (rt_model_l D nc).Domain := ⟨⟨H,(my.2.2.2 H C' hH).1⟩,hH⟩
    exact moved.native_mono_l I my.2.1 hY.1 D fs.transitive nc J c b h h'
      (fun x hx => keep x.val x.property hx)

end YesMetaZFC.SetTheory.LargeCardinal
