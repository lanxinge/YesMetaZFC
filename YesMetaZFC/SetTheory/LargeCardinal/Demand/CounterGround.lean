import YesMetaZFC.SetTheory.Descriptive.Demand.DemandCounterWeave
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection

/-! # 扩张中同一反策略的有限回复回收

先在扩张内读取真实策略值，再由成员满像和有限列空间回收新两图。
原输入 f 只回收其有限前缀；反策略和反游戏历史仍留在扩张内。
地模型合成图的像与同一次回复的节点图相等，因此原树节点也真实回传。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem td_counter_ground_l
    {ω A U₁ U₂ S k n a b z : M.Domain} {f V F L G T B W O o τ C h : N.Domain}
    (hw : M.IsOmega ω) (hwN : N.IsOmega (e ω))
    (ff : N.IsSetFunctionFromTo J f (e ω) (e A))
    (game : Dg_counter_d hN (e ω) (e U₁) (e U₂) f (e S) V F L G T B W O)
    (control : Cg_control_d J true (e ω) o V F L G T τ C)
    (hk : M.mem k ω) (add : M.IsOrdinalAddition I n k k)
    (fh : Fn0_d (e n) V h) (hh : N.mem h C)
    (fa : Fn0_d k U₁ a) (fb : Fn0_d k U₂ b)
    (weave : Dg_weave_d J (e ω) h (e a) (e b)) (hz : M.mem z U₁) :
    ∃ k' n' s a' b' z', ∃ h₁ h₂ : N.Domain,
      M.SuccessorOf k' k ∧ M.mem k' ω ∧ M.mem n' ω ∧ M.IsOrdinalAddition I n' k' k' ∧
      Fn0_d k' A s ∧ Fn0_d k' U₁ a' ∧ Fn0_d k' U₂ b' ∧ M.mem z' U₂ ∧ Tg_node_d I k' S s a' b' ∧
      (∀ p, M.mem p a' ↔ M.mem p a ∨ KPair_d M p k z) ∧
      (∀ p, M.mem p b' ↔ M.mem p b ∨ KPair_d M p k z') ∧
      Fn0_d (e n') V h₂ ∧ N.mem h₂ C ∧ Fseq_end_d J (e ω) h₁ h (e z) ∧
      Fseq_end_d J (e ω) h₂ h₁ (e z') ∧ Rd_entry_d h₁ (e z') τ ∧
      N.IsRestrictionOf J (e s) f (e k') ∧ Dg_weave_d J (e ω) h₂ (e a') (e b') := by
  have entry i x g := image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i x g
  have imageFn {g X Y : M.Domain} (fg : M.IsSetFunctionFromTo I g X Y) :
      N.IsSetFunctionFromTo J (e g) (e X) (e Y) :=
    image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fg
  -- 有限图由实际有限列空间回收，不把“新图属于地模型”列作前提。
  have finite {j X : M.Domain} {g : N.Domain} (hj : M.mem j ω)
      (fg : N.IsSetFunctionFromTo J g (e j) (e X)) :
      ∃ g₀, Fn0_d j X g₀ ∧ e g₀ = g := by
    obtain ⟨E,space⟩ := ZF.fseq_space_exists_l I hM hw X
    have mem := (image_fseq_l hM hN e hi he hw hwN space g).mpr
      ⟨e j,(image_member_l e hi he).mpr hj,fg⟩
    obtain ⟨g₀,hg₀,eq⟩ := (he E g).mp mem
    obtain ⟨i,_,fi⟩ := (space g₀).mp hg₀
    have fj := imageFn fi
    have ij := hi (fj.2.1.eq hN.1 (eq.symm ▸ fg.2.1))
    subst i
    exact ⟨g₀,fn0_of_function_l (ZF.modelsKP hM) fi,eq⟩
  have hn := ZF.ordinalAddition_mem_omega hM I hw hk hk add
  have faN := fn0_of_function_l (ZF.modelsKP hN) (imageFn (fn0_function_l (ZF.modelsKP hM) fa))
  have fbN := fn0_of_function_l (ZF.modelsKP hN) (imageFn (fn0_function_l (ZF.modelsKP hM) fb))
  obtain ⟨kN,nN,h₁,h₂,zN,sN,aN,bN,succN,hkN,_,addN,f₂,h₂C,end₁,end₂,value,hzN,
    restN,nodeN,faN',fbN',woven,appendA,appendB⟩ := game.reply_extend_l hN hwN control
      ((image_member_l e hi he).mpr hk) ((image_member_l e hi he).mpr hn)
      (image_nat_add_l hM hN e hi he hw hk add) fh hh faN fbN weave ((image_member_l e hi he).mpr hz)
  -- 新长度和新字母均来自同一次回复；后继与加法唯一性识别其原像。
  obtain ⟨k',succ,hk'⟩ := hw.1.2 k hk
  have ek := (image_successor_l (hEN := hN.1) e hi he hM.1 succ).eq hN.1 succN
  subst kN
  obtain ⟨n',add',_⟩ := ZF.ordinalAddition_existsUnique hM I k' (hw.members_areOrdinals (ZF.modelsKP hM) k' hk')
  have hn' := ZF.ordinalAddition_mem_omega hM I hw hk' hk' add'
  obtain ⟨_,_,one⟩ := ZF.ordinalAddition_existsUnique hN J (e k')
    (hwN.members_areOrdinals (ZF.modelsKP hN) (e k') hkN)
  have en := (one (e n') (image_nat_add_l hM hN e hi he hw hk' add')).trans (one nN addN).symm
  subst nN
  obtain ⟨z',hz',ez⟩ := (he U₂ zN).mp hzN
  subst zN
  obtain ⟨s,fs,rest⟩ := ground_prefix_l hM hN e hi he hw hwN ff hk'
  have es := rest.eq hN.1 restN
  subst sN
  obtain ⟨a',fa',ea⟩ := finite hk' (fn0_function_l (ZF.modelsKP hN) faN')
  subst aN
  obtain ⟨b',fb',eb⟩ := finite hk' (fn0_function_l (ZF.modelsKP hN) fbN')
  subst bN
  have pair p i x : KPair_d N (e p) (e i) (e x) ↔ KPair_d M p i x := by
    constructor
    · intro cp
      obtain ⟨r,cr⟩ := (I).total i x
      exact (hi ((J).unique cp (image_kpair_l e he cr))).symm ▸ cr
    · exact image_kpair_l e he
  have first p : M.mem p a' ↔ M.mem p a ∨ KPair_d M p k z :=
    (image_member_l e hi he).symm.trans ((appendA (e p)).trans
      (or_congr (image_member_l e hi he) (pair p k z)))
  have second p : M.mem p b' ↔ M.mem p b ∨ KPair_d M p k z' :=
    (image_member_l e hi he).symm.trans ((appendB (e p)).trans
      (or_congr (image_member_l e hi he) (pair p k z')))
  -- 合成地三图，再以同坐标函数性识别其像就是扩张回复中的节点。
  have fma := fn0_function_l (ZF.modelsKP hM) fa'
  have fmb := fn0_function_l (ZF.modelsKP hM) fb'
  obtain ⟨_,Y,q,_,_,fq,joined⟩ := tg_join_exists_l I hM fs fma fmb
  have fqn := imageFn fq
  have joinedN : Tg_join_d J (e k') (e s) (e a') (e b') (e q) := by
    refine ⟨⟨fqn.1,fqn.2.1⟩,?_⟩
    intro i hik
    obtain ⟨j,hj,rfl⟩ := (he k' i).mp hik
    obtain ⟨x,y,z,v,p,ix,iy,iz,cv,cp,ip⟩ := joined.2 j hj
    exact ⟨e x,e y,e z,e v,e p,(entry j x s).mp ix,(entry j y a').mp iy,
      (entry j z b').mp iz,image_kpair_l e he cv,image_kpair_l e he cp,(entry j p q).mp ip⟩
  obtain ⟨qN,qS,joinN⟩ := nodeN.2.2.2
  have sub₀ := Tg_join_d.subset_l joinedN joinN (imageFn fs).1 (imageFn fma).1 (imageFn fmb).1
    (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h)
  have sub₁ := Tg_join_d.subset_l joinN joinedN (imageFn fs).1 (imageFn fma).1 (imageFn fmb).1
    (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h)
  have eq := hN.1.eq_of_same_members (e q) qN (fun p => ⟨sub₀ p,sub₁ p⟩)
  have node : Tg_node_d I k' S s a' b' :=
    ⟨⟨fs.1,fs.2.1⟩,⟨fma.1,fma.2.1⟩,⟨fmb.1,fmb.2.1⟩,
      q,(image_member_l e hi he).mp (eq.symm ▸ qS),joined⟩
  exact ⟨k',n',s,a',b',z',h₁,h₂,succ,hk',hn',add',fn0_of_function_l (ZF.modelsKP hM) fs,
    fa',fb',hz',node,first,second,f₂,h₂C,end₁,end₂,value,rest,woven⟩

end YesMetaZFC.SetTheory.LargeCardinal
